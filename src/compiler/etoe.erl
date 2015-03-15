%% @doc
%% <p>source-to-source translation of Erlang supervision tree
%%   to prepare the code for translation to mCRL</p>
%%
%% <p>Thomas Arts. July 2002</p>
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

%% PRECOND:

%% The Erlang code we want to translate is implemented as a
%% supervision tree. The code is organized as a set of modules where
%% one module (the root of the supervision tree) implements the
%% supervision tree and the other modules implement the children.  
%% The arguments that are passed to this module are the name of the
%% root of the supervision tree, the function that starts the
%% supervision tree and the arguments passed to the supervision tree.
%%
%% INVARIANTS:
%%
%% 
%% 
%% POSTCOND:
%%
%% The supervision module is analyzed. The information about its
%% children is extracted and the initial arguments instantiated for
%% each of the children. If a children is also a supervisor, the
%% information about its children is extracted as well. The
%% information about the children includes: the behaviour of the child
%% (gen_server, gen_fsm, gen_event or worker), the module where it is
%% implemented, the starting function and its arguments and possibly
%% some options ("register" if the process is registered, and
%% "started" to signal that the start function has been already
%% analyzed and is going to be ignored in the rest of the
%% translation).

%% 

%% Pseudocode for this module:
%%
%% supervisor ->
%%           [{Behaviour,{Mod,Fun,Args}, Opts}] = extract_children(etoe_app:nonap()),
%%           combine_mods().
%%
%% combine_mods ->
%%           [writeprog({ok,toppart(TopAbsForms),SefAbsForms,Actions} = split_code ()),
%%            ...,
%%           init_module()]
%%
%% toppart -> changes the handle calls introducing a new variable 'State'
%%

%% writeprog -> Returns {ModuleName, [AbsForm]} and introduces the
%% -copyright with the list of actions
%%

%% split_code ->
%%           AbsForms = readprog() % calls lower, noio, noimports, and
%%           removes -file
%%           {Dep,InDep} = callgraph:sideeffect(behaviour_dep())
%%           NewAbsForms = remove_functions(AbsForms, StartedFunctions)
%%           {ok, TopAbsForms, SefAbsForms, Actions} = 
%%                        split_absforms (Mod, Dep, InDep, NewAbsForms, [],[])
%% @end

-module(etoe).

%% THOMAS: why exporting myerlparse?
-export([supervisor/3,myerlparse/1]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3,reverse/1]).

-record(global,{

%% THOMAS: Only inits and translated are used
                vars = [],
                atoms = [],
                maxcase = 0,
                maxmap = 0,
                scope = [],
                cases = [],
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                inits = [],
                translated = []
               }).

-include("etomcrl.hrl").

%% @spec supervisor(Module::atom(),Func::atom(),Args::[term()]) -> [absForm()]
%% @doc
%% This function takes the name of the modulo where the supervision
%% tree is defined, the function that starts the supervision tree and
%% some arguments.
%% It returns the list of abstract forms for the module where:
%% <dl>
%% <dt>the higher order functions are flattened into first order
%% functions </dt> 
%% <dt>the io:format sentences are removed</dt>
%% <dt> the imported functions are written with the name of the module
%% in front of them, and the "-import" is removed</dt> 
%% </dl>
%% @end

% all processes virtually started in a supervision tree
% by calling Module:Func(Args)
%
supervisor(Module,Func,Args) ->
    put(free,0), % TODO: We think that this is not used here
                 % because free is set to 0 also in nofreevars

    %% For storing the free variables in the process dictionary
    Children = extract_children(etoe_app:nonapp(Module,Func,Args),[]),

    %% app:nonapp returns a tree with the information about all
    %% the processes started by the supervision tree. In this
    %% information, the starting function and its arguments
    %% are included

    %% extract_children flattens the supervision tree and converts it
    %% into a list of process information structures
    
    %% the information about the non worker processes is ignored, the
    %% supervision tree is not used during the compilation to mCRL
    %% anymore

    %% Children has the following structure: 
    %%          [{Behaviour,{Mod,Fun,Args},Opts}]
    %% where Behaviour can be: gen_server, gen_fsm, gen_event or
    %% worker
    %% and Opts can be: [{started,[{Start,length(Args)}]}],
    %% [{registered,Name},{started,[..]}
    %% @end

    ?DEBUG("~p~n",[Children]),
    combine_mods(Module,Children,#global{}).

combine_mods(SuperVisor,[],Global) ->
    Init = {function,0,init,0,[init_to_clause(Global#global.inits)]},
    [writeprog(SuperVisor,[Init],
	       [{attribute,0,module,SuperVisor},
		{attribute,0,export,[{init,0}]}],[])];
combine_mods(SuperVisor,[{Behaviour,{Mod,F,As},Opts}|Rest],Global) ->
    ?DEBUG("Options: ~p~n",[Opts]),
    Self = % Child process' name 
	case lists:keysearch(registered,1,Opts) of
	    {value,{registered,{_,ProcName}}} ->
		ProcName;
	    {value,{registered,ProcName}} ->
		ProcName;
	    false ->
		length(Global#global.inits)
	end,

    %% The children is added to the global init list
    Global1 = construct_init(Self,{Behaviour,{Mod,F,As},Opts},Global),

    %% We check if the module has already been translated, because the
    %% same code is used by other worker already processed. In this
    %% case, we don't need to translate the module code again
    case member(Mod,Global1#global.translated) of
	true ->
	    combine_mods(SuperVisor,Rest,Global1);
	false -> % We need to translate
	    ?DEBUG("analyzing module ~p with behaviour ~p~n",[Mod,Behaviour]),
	    Global2 = 
		Global1#global{translated = [Mod|Global1#global.translated]},
	    %% the module is added to the ones that have been translated
	    case split_code({Behaviour,{Mod,F,As},Opts}) of
		{ok,TopAbsForms,SefAbsForms,Actions} ->
		    %% reverse is used to preserve the layout in the code 
		    NewTopAbsForms = 
			reverse(
			  map(fun(AbsForm) ->
				      %% If the Behaviour is a
				      %% gen_server, the handle
				      %% clauses are changed in order
				      %% to make the transition to
				      %% mCRL easier
				      toppart(Behaviour,Mod,AbsForm)
			      end,TopAbsForms)),
		    NewSefAbsForms = 
			reverse(SefAbsForms),
		    [writeprog(Mod,NewTopAbsForms,NewSefAbsForms,Actions)|
		     combine_mods(SuperVisor,Rest,Global2)];
		{error,ErrorDesc} ->
		    io:format("ERROR: Can't read "++atom_to_list(Mod)++".erl~n"),
		    combine_mods(SuperVisor,Rest,Global2)
	    end
    end.

%% Adds the child to the global init counter

construct_init(Self,{Behaviour,{Mod,F,As},Opts},Global) ->
  Global#global{inits = 
                    [{Behaviour,Self,[Mod,F,As]}|
                     Global#global.inits]}.


init_to_clause(Inits) ->
  {clause,0,[],[],map(fun(E) -> init_to_expr(E) end,Inits)}.

init_to_expr({Behaviour,Self,[M,F,As]}) ->
  Mod = {atom,0,M},
  Fun = {atom,0,F},
  case Behaviour of
       worker ->
         ?DEBUG("abstract: ~p~n",[As]),
         {call,0,{atom,0,spawn},[Mod,Fun,myerlparse(As)]};
       _ ->
         [A] = As,
         Args = myerlparse(A),
         {call,0,{remote,0,{atom,0,Behaviour},{atom,0,start}},
                  if atom(Self) ->
                      [{tuple,0,[{atom,0,local},{atom,0,Self}]},
                       Mod,Args,{nil,0}];
                     true -> 
                      [Mod,Args,{nil,0}]
                  end}
  end.

myerlparse(Expr) ->  % hack because of error in erl_parse
% erl_parse:abstract([storage_group,2]).
%    {cons,0,{atom,0,storage_group},{string,0,[2]}}
% erl_parse:abstract(2).                
%    {integer,0,2}
% erl_parse:abstract({1,2}).
%    {tuple,0,[{integer,0,1},{integer,0,2}]}
%
  ParseExpr = erl_parse:abstract(Expr),
  %?DEBUG("error in erl_parse ~p~n",[ParseExpr]),
  undo_string(ParseExpr).

% change by Juanjo (July 2002): use undo_string instead.
%  case ParseExpr of
%       {cons,0,E1,{string,_,[I]}} when integer(I) ->
%         {cons,0,E1,{cons,0,{integer,0,I},{nil,0}}};
%       Other ->
%         Other
%  end.

undo_string({cons,L,E1,E2}) ->
    {cons,L,undo_string(E1),undo_string(E2)};
undo_string({string,L,String}) ->
    cons_list_from_string(L,String);
undo_string({tuple,L, List}) ->
    {tuple, L, lists:map(fun(TupleElement) ->
                                 undo_string(TupleElement) end,
                         List)
                        };
undo_string(A) -> A.

cons_list_from_string(L,[Char|Chars]) ->
    {cons,L,{integer,L,Char}, cons_list_from_string(L,Chars)};
cons_list_from_string(L,[]) ->
    {nil,L}.



toppart(Behaviour,Mod,AbsForm) ->
  case Behaviour of
       gen_server ->
         change_handles(AbsForm);
       _ ->
         AbsForm
  end.

%% The original expression:
%%  
%% handle_call(Msg, From, {A,B,C}) -> Body
%%
%% is replaced by:
%%
%% handle_call(Msg, From, State) ->
%%        {A,B,C} = State,
%%        Body (with State as free variable)
%%
%% This is done because the handle functions are going to be combined
%% in a unique clause at the mCRL level. This step prepares the code
%% for an easier translation.
%%
%% Note: ERLANG SEMANTICS ARE BROKEN HERE. 
%% 
%% f(1) -> body1
%% f(2) -> body2
%%
%% is not semantically equivalent to:
%%
%% f(X) ->
%%   1 = X,
%%   body1.
%%
%% f(X) ->
%%   2 = X,
%%   body2.

change_handles({function,L,handle_call,3,Clauses}) ->
  %?DEBUG("handle_call ~p~n",[Clauses]),
  {function,L,handle_call,3,
     map(fun({clause,L1,[Msg,From,State],[],Body}) ->
              {clause,L1,[Msg,From,{var,0,'State'}],[],
                 [{match,L1,State,{var,0,'State'}}|freeof('State',Body)]};
	    %% freeof/2 is called to replace any occurence of 'State'
	    %% inside the clause body
            (C) ->
              io:format("error line ~p: wrong handle_call format~n",[L]),
              C
         end,Clauses)};
change_handles({function,L,handle_cast,2,Clauses}) ->
  %?DEBUG("handle_cast ~p~n",[Clauses]),
  {function,L,handle_cast,2,
     map(fun({clause,L1,[Msg,State],[],Body}) ->
              {clause,L1,[Msg,{var,0,'State'}],[],
                 [{match,L1,State,{var,0,'State'}}|freeof('State',Body)]};
            (C) ->
              io:format("error line ~p: wrong handle_cast format~n",[L]),
              C
         end,Clauses)};
change_handles(AbsForm) ->
  AbsForm.

%% TODO 
%% This function substitutes any occurence of Var inside Body by
%% a fresh variable

freeof(Var,Body) ->
  Body.


%%

split_code({Behaviour,{Mod,F,As},Opts}) ->
    FileName = atom_to_list(Mod)++".erl",
    %% readprog already performs some transformations in the abstract forms
    case readprog(FileName) of
	{ok,AbsForms} ->
	    Rem = 
		%% This list of functions are not going to be taken
		%% into account in the translation, neither in the
		%% side effect free, nor in the side effect part of
		%% the program
		case lists:keysearch(started,1,Opts) of
		    {value,{started,Funcs}} ->
			Funcs;
		    false -> 
			[]
		end,
	    MRem = % Modified adding module name
		map(fun({Name,Arity}) -> {Mod,Name,Arity} end,Rem),
	    
	    {Dep,InDep} =
		%% Dep is the list of all the functions which call
		%% either any function contained in the second
		%% argument of sideeffect/3 (that is, the ones
		%% declared in behaviour_dep) or a user defined
		%% actions (written directly in the Erlang source
		%% code). InDep is the rest of functions in the module
		%%
		%% MRem contains a list of functions that are not
		%% taking into account for calculating the return of
		%% sideeffect. The functions called from them, are
		%% also removed.
		etoe_callgraph:sideeffect(AbsForms,
				     [{Mod,F,length(As)}|
                                      behaviour_dep(Mod,Behaviour)],				     
				     MRem),
	    
	    ?DEBUG("Dep: ~p~nInDep: ~p~n",[Dep,InDep]),

	    %% We remove the functions in Rem from the AbsForms
	    NewAbsForms =  
		foldr(fun(AbsForm,Forms) ->
			      remove_functions(AbsForm,Rem)++Forms
		      end,[],AbsForms),

	    %% split_absforms returns {ok,TopAbsForms,SefAbsForms,Actions} 
	    split_absforms(Mod,Dep, InDep,
			   NewAbsForms,[],[]);

	{error,ErrorDesc} ->
	    {error,ErrorDesc} 
    end.

behaviour_dep(Mod, _) ->
  [{gen_server,call,2},{Mod,handle_call,3},
   {gen_server,cast,2},{Mod,handle_cast,2},
   {gen_server,reply,2},{gen_server,replied,3}
  ].

%% If the first argument is an export attribute, removes the list of
%% functions given as second argument from the list of functions that
%% are exported
%%
%% If the first argument is a function, removes the function if it's
%% included in the second argument

remove_functions({attribute,L,export,Exports},Rem) ->
    [{attribute,L,export,Exports -- Rem}];
remove_functions({function,Line,Name,Arity,Clauses},Rem) ->
    case member({Name,Arity},Rem) of
	true -> 
	    [];
	false ->
	    [{function,Line,Name,Arity,Clauses}]
    end;
remove_functions({eof,_},Rem) ->
    [];
remove_functions(AbsForm,Rem) ->
    [AbsForm].

%%  split_absforms(...) -> {ok, TopAbsForms, SefAbsForms, Actions} The
%%  Abstract forms of the functions whose names are in Dep are added
%%  to Top and removed from Dep. Same for InDep, whose functions are
%%  added to Sef.  The values that remain in InDep and Dep are the
%%  actions

split_absforms(Mod,Dep,InDep,[],Top,Sef) ->
  {ok,Top,Sef,Dep++InDep};
split_absforms(Mod,Dep,InDep,[{function,Line,Name,Arity,Body}|AbsForms],Top,Sef) ->
  case member({Mod,Name,Arity},Dep) of
       true ->
         split_absforms(Mod,Dep--[{Mod,Name,Arity}],InDep,AbsForms,
                                [{function,Line,Name,Arity,Body}|Top],Sef);
       false -> 
         split_absforms(Mod,Dep,InDep--[{Mod,Name,Arity}],AbsForms,
                               Top,[{function,Line,Name,Arity,Body}|Sef])
  end;
split_absforms(Mod,Dep,InDep,[AbsForm|AbsForms],Top,Sef) ->
  split_absforms(Mod,Dep,InDep,AbsForms,Top,[AbsForm|Sef]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Reads the filename into an abstract forms list. Then, the higher
%% order functions are flattened into first order functions, the
%% io:format sentences are removed, and the imported functions are
%% written with the name of the module in front of them, removing the
%% import sentence

readprog(FileName) ->
  case epp:parse_file(FileName,["."],[]) of
       {ok,AbsForms} ->
          {ok,etoe_lower:forms(
                etoe_noio:forms(
                  etoe_noimports:forms(etoe_observe_messages:forms(tl(AbsForms)))
           ))};    % remove -file attribute (it was in the head of AbsForms) 
       Other ->
         Other
  end.


%% 

writeprog(Mod,Top,Sef,Acts) ->
  Actions = [ A || A<- Acts, validaction(A) ],
  {Mod,Sef ++ [{attribute,0,copyright,{actions,Actions}}|Top]}.

%% what is a valid action?
%% lists:map() why can be the case that something like this is inside Acts?

validaction({lists,_,_}) -> % lists are implemented directly and
                            % therefore they are no actions
  false;
validaction(_) ->
  true.

%%%%%%%%%%%%%%%%%%%%%%%% helper functions %%%%%%%%%%%%%%%%%%%%


extract_children({supervisor,_,Children},Childs) ->
  foldr(fun(C,Cs) ->
           extract_children(C,Cs)
        end,Childs,Children);
extract_children({Type,Name,{{Mod,Fun,Args},_,Behaviour,Opts}},Childs) ->
  [{Behaviour,{Mod,Fun,Args},Opts}|Childs];
extract_children({Type,Name,{{Mod,Fun,Args},_,Behaviour}},Childs) ->
  [{Behaviour,{Mod,Fun,Args},[]}|Childs].
