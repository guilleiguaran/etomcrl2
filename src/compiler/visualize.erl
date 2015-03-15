% Visualisation of the supervision tree
%
% Thomas Arts
% November 2000
% Modified June 2001

-module(visualize).
-export([supervisor/3,
	 callback/1,
         callback/2,
	 script/0]).

-include("../gd/gd.hrl").

-import(lists,[foldr/3, map/2]).


%% FIXME: Taken from etomcrl.erl, we should generalize this code 
%% into some 'utils' like library

script() ->
    {ok,[Args]} = init:get_argument(start),
    case Args of
	[StartTerm] ->
	    {ok,Tokens,_} = erl_scan:string(StartTerm),
	    case Tokens of		
		[{atom,_,Mod},{':',_},{atom,_,Fun},{'(',_}|ArgsPar] ->
		    case parse_exprs(dotlast(ArgsPar)) of
			{ok,AbsTerms} ->
			    Terms =
				map(fun(T) -> erl_parse:normalise(T) end, AbsTerms),
			        supervisor(Mod,Fun,Terms);
			{error,Reason} ->
			    io:format("Error: use \"Mod:Fun(ArgList)\"~n~p ~p~n",
				      [Reason,ArgsPar])
		    end;
		_ ->
		    io:format("Error: use ~p \"Mod:Fun(ArgList)\"~n",[?MODULE])
	    end;
	_ ->
	    io:format("Error: use ~p \"Mod:Fun(ArgList)\"~n",[?MODULE])
    end.

%% Change: erl_parse:parse_expr/1
%
% empty sequence, i.e. [{dot,1}] not parsed to empty list []
%
parse_exprs([{dot,_}]) ->
  {ok,[]};
parse_exprs(Exprs) ->
  erl_parse:parse_exprs(Exprs).


dotlast([_]) ->
  [{dot,1}];
dotlast([_,{dot,_}]) ->
  [{dot,1}];
dotlast([H|T]) ->
  [H|dotlast(T)].


supervisor(Mod,Func,Args) ->
  SupervisorStruct =
    etoe_app:nonapp(Mod,Func,Args),
  gdtop:supertree({?MODULE,callback}, SupervisorStruct).

vertices({supervisor,Name,{error,Reason}},Path) ->
  [{Name,error,Path}];
vertices({supervisor,Name,Children},Path) ->
  {Vertices,_} =
     foldr(fun(Child,{Vs,N}) -> 
              {vertices(Child,Path++[N])++Vs,N+1}
           end,{[],1},Children),
  [{Name,supervisor,Path}|Vertices];
vertices({_,Name,{error,Reason}},Path) ->
  [{Name,error,Path}];
vertices({_,Name,{_,_,Behaviour,_}},Path) ->
  [{Name,Behaviour,Path}].

edges([]) -> 
  [];
edges([{N1,T1,P1}|Vs]) -> 
  [{{N1,T1,P1},{N2,T2,P2}} || {N2,T2,P2}<-Vs, prefix(P1,P2)]++
  edges(Vs).

prefix([],[N]) ->
  true;
prefix([N|Ns],[N|Ms]) ->
  prefix(Ns,Ms);
prefix(_,_) ->
  false.
  
%get_name([],SuperTree) ->
%  atom_to_list(element(2,SuperTree));
%get_name([N|Ns],{supervisor,_,Children}) ->
%  % here the node must be a supervisor node
%  get_name(Ns,lists:nth(N,Children)).

%%-------------------------------------------------------------

callback(graph,SuperTree) ->
    Vertices = (catch vertices(SuperTree,[])),
    {#gd_graph{directed=false,
	       cyclic=false,
	       vertices=Vertices,
	       start_vertices=[hd(Vertices)],
	       edges=edges(Vertices)
              },
     SuperTree};

callback({name_string,{Name,Type,Path}},SuperTree) ->
  {io_lib:format(" ~p ~n~n ~p ",[Name,Type]),SuperTree};

callback({shape,{Name,Type,Path}},SuperTree) -> 
  case Type of
       supervisor ->
         {rectangle,SuperTree};
       _ -> 
         {oval,SuperTree}
  end.

callback({click,node,Node}) ->
  io:format("clicked ~p~n",[Node]);

callback({select_node_attributes,Node}) -> [{fg,red}];
 
callback({old_node_attributes,{_,supervisor,_}}) -> [{fill,lightblue}];
callback({old_node_attributes,{_,error,_}}) -> [{fill,red}];
callback({old_node_attributes,{_,gen_server,_}}) -> [{fill,yellow}];
callback({old_node_attributes,{_,gen_fsm,_}}) -> [{fill,yellow}];
callback({old_node_attributes,{_,gen_event,_}}) -> [{fill,lightyellow}];
callback({old_node_attributes,{_,Worker,_}}) -> [{fill,white}];

callback({new_node_attributes,_}) -> [{fill,white}].



