%% @doc
%%
% Build callgraph for a module
%   (necessary after R8, since exref has been removed)
%
%% <p> Thomas Arts. October 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>
%
% This module depends on noimports.erl, i.e. all function calls from
%      external modules should be replaced by Mod:function call.
%

-module(etoe_callgraph).

-export([forms/1, file/1]).
-export([sideeffect/3]).

-import(lists,[map/2,member/2,foldl/3,foldr/3,foreach/2]).

-include("etomcrl.hrl").

%% @spec sideeffect(absforms(), Sideeffects::[{module(),atom(),int()}], Removes::[{module(),atom(),int()}]) ->
%%                       {[{module(),atom(),int()}],[{module(),atom(),int()}]}
%%
%% @doc
%% May 30, 2001 added support for action: as a side effect
%%
%% Returns a tuple {Dep,InDep} where:
%%
%% - Dep: is the list of all the functions which are called from side
%% effect functions or from the actions directly written in the Erlang
%% source code as -action([...])
%%
%% - InDep: the rest of the functions in the module
%%
%% The functions given in Removes as argument and the ones only called
%% from them are not taken into account

sideeffect(AbsForms,SideEffects,Removes) ->
    Graph = forms(AbsForms), 
    %% Creates the dependency digraph for the functions in the module
    remove(Graph,Removes), % functions in Removes are removed from the graph
    %% Graphs are not functional in Erlang!, Graph value is modified!
    Actions = % Side effects plus the actions written in the source code
	foldl(fun({action,F,A},As) ->
		      %% Supports actions to be written directly in the Erlang code
		      case member({action,F,A},As) of
			  true ->
			      As;
			  false ->
			      [{action,F,A}|As]
		      end;
		 (_,As) ->
		      As
	      end,[],digraph:vertices(Graph)) 
	++ SideEffects,
    ?DEBUG("actions: ~p~n",[Actions]),
    Reachable =
	%% Functions called from the Actions
	digraph_utils:reaching(Actions,Graph),
    Vertices = 
	digraph:vertices(Graph),
    digraph:delete(Graph), % Destroys the graph structure
    {Reachable,Vertices--Reachable}.

%% The Vertices argument is used to remove all functions that are
%% listed in this argument PLUS the functions that can only be reached
%% from functions in these argument (transitively).
%% 
%% The functions that are *only* called from the ones that we want to
%% remove, are also removed.

remove(Graph,Vertices) ->
  Reachable = digraph_utils:reachable(Vertices,Graph), % Functions reachable from the vertices

  Vs = [ V || V<-Reachable,
              (digraph_utils:reaching([V],Graph)--Reachable)==[] ],
  ?DEBUG("removing vertices ~p~n",[Vs]),
  foreach(fun(V) ->
             digraph:del_vertex(Graph,V)
          end,Vs).

%% @spec forms([abs_form()]) -> Digraph

forms(AbsForms) ->
  Module = modulename(AbsForms),
  foldr(fun(AbsForm,Graph) ->
           form(Graph,Module,AbsForm)
        end,digraph:new(),AbsForms).

%%@spec file(filename()) -> Digraph

file(FileName) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms).

%% @spec modulename([absForm()]) -> module()
%% @doc
%% Extracts the module name from the corresponding attribute of the
%% abstract forms list
%% @end

modulename([]) ->
  exit({?MODULE,?LINE,"module name not found"});
modulename([{attribute,_,module,Module}|_]) ->
  Module;
modulename([_|AbsForms]) ->
  modulename(AbsForms).

%% @spec form(digraph(),module(),absForm()) -> digraph()
%%
%% @doc
%% Only for the functions, a new vertex is added to the digraph, and
%% all the subgraph with the internal calls inside that function is
%% created. 
%% In any other case, the Graph is not modified.

form(Graph,Module,{function,Line,Name,Arity,Clauses}) ->
  digraph:add_vertex(Graph,{Module,Name,Arity}),
  addgraph(Graph,Module,{Module,Name,Arity},Clauses);
form(Graph,Module,{attribute,_,import,_}) ->
  Graph;
form(Graph,Module,AbsForm) ->
  Graph.

%%
%% Analyses the clauses of the function to add all the internal
%% function calls to the callgraph
%%
addgraph(Graph,Module,Function,Expr) ->
  case Expr of
       Exprs when list(Exprs) ->
         foldl(fun(E,G) ->
                  addgraph(G,Module,Function,E)
               end,Graph,Exprs);
       {clause,Line,Pats,Guards,E} ->
         G1 = addgraph(Graph,Module,Function,Guards),
         addgraph(G1,Module,Function,E);
       {tuple,Line,Es} ->
         addgraph(Graph,Module,Function,Es);
       {cons,Line,Head,Tail} ->
         G1 = addgraph(Graph,Module,Function,Head),
         addgraph(G1,Module,Function,Tail);
       {match,Line,E1,E2} ->
         addgraph(Graph,Module,Function,E2);
       {'case',Line,E,Clauses} ->
         G1 = addgraph(Graph,Module,Function,E),
         addgraph(G1,Module,Function,Clauses);
       {call,Line,{atom,_,Fun},Args} ->
         % BIFs are not added
         case erl_internal:bif(Fun,length(Args)) of
              true ->
                addgraph(Graph,Module,Function,Args);
              false ->
                Called = {Module,Fun,length(Args)},
                digraph:add_vertex(Graph,Called),
                Result = digraph:add_edge(Graph,Function,Called),
                ?DEBUG("edge added ~p -> ~p (~p)~n",[Function,Called,Result]),
                addgraph(Graph,Module,Function,Args)
         end;
       {call,Line,{remote,_,{atom,_,Mod},{atom,_,Fun}},Args} ->
         Called = {Mod,Fun,length(Args)},
         digraph:add_vertex(Graph,Called),
         Result = digraph:add_edge(Graph,Function,Called),
         ?DEBUG("edge added ~p -> ~p (~p)~n",[Function,Called,Result]),
         addgraph(Graph,Module,Function,Args);
       {call,Line,Fun,Args} ->
         addgraph(Graph,Module,Function,Args);
       {op,Line,Op,E} ->
         addgraph(Graph,Module,Function,E);
       {op,Line,Op,E1,E2} ->
         G1 = addgraph(Graph,Module,Function,E1),
         addgraph(G1,Module,Function,E2);
       {record_index,Line,Name,Field} ->
         addgraph(Graph,Module,Function,Field);
       {record,Line,Name,Inits} ->
         addgraph(Graph,Module,Function,Inits);
       {record,Line,Rec0,Name,Upds0} ->
         G1 = addgraph(Graph,Module,Function,Rec0),
         addgraph(G1,Module,Function,Upds0);
       {record_field,Line,Rec0,Field0} ->
         G1 = addgraph(Graph,Module,Function,Rec0),
         addgraph(G1,Module,Function,Field0);
       {record_field,Line,Rec0,Name,Field0} ->
         G1 = addgraph(Graph,Module,Function,Rec0),
         addgraph(G1,Module,Function,Field0);

% add list comprehensions

       _ ->
         Graph
  end.


