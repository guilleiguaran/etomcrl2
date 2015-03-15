%% Erlang -> Erlang translation, addapting as much as possible
%%  to mCRL demanded structure
%%
%% <p>created  Thomas Arts  July 2002</p>
%% <p>modified Thomas Arts  Sep 2003</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% forms([InitAbsForms::absforms() | AbsFormsList:[absforms()]]) ->
%%            children(AbsFormsList, InitAbsForms).
%%
%% children(Sources, InitAbsForms) ->
%%          Obtains 'Children', List with tuples of the form {ProcessType,
%%          ModuleName} of all the modules started by init function,
%%          combine_mods(Sources, Children,
%%                split_code(map(fun(A) -> update_init(A) end, InitAbsForms))).
%%
%% combine_mods(Sources,[{Type,Mod}|Rest],{Proc,SEFs,Acts}) -> 
%%       AbsForms =
%%	  case Type of
%%	    gen_server ->
%%		gs_replace(Mod,bifredefine(find(Mod,Sources)));
%%	    _ ->
%%		bifredefine(find(Mod,Sources))
%%
%%    {TopAbsForms,SefAbsForms,Actions} =
%%	split_code(locals:forms(AbsForms)),
%%    SEF = sef(Mod,SefAbsForms),  % [{atom(),integer()}]
%%    combine_mods(Sources,Rest,
%%		 {procmodify(TopAbsForms,SEF)++Proc, 
%%		  SefAbsForms++SEFs, % Sef part is added without changes
%%		  adduniq(Actions,Acts)}). % New actions are added
%%
%% combine_mods(Sources,[],{Proc,SEFs,Acts}) ->
%%    BIFs = bifs.erl function declaration abstract forms 
%%   [{attribute,1,module,list_to_atom(?PMCRLFile)}|
%%     norecords:forms(sefmodify(0,nofreevar:forms(SEFs++BIFs))) ++
%%     [{attribute,0,copyright,{actions,Acts}}|Proc]];
%%
%% gs_replace(Mod, AbsForms) -> All the functions that have to do with
%% the generic server (init, handle_call, handle_cast) are transformed
%% into ?SERVERLOOP
%%
%% TopAbsForms are modified by procmodify (norecords, conftau,
%% sumvars, callreturn, matches, vararg, nofreevar, gs_addself,
%% addself)
%%
%% SefAbsForms are modified by norecords, sefmodify (), nofreevar 
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-module(etopmcrl).

-export([file/3,forms/1,forms/2]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

forms([InitAbsForms|AbsFormsList]) ->
  children({absforms,AbsFormsList},InitAbsForms).

forms(Dir,InitFile) ->
  ?DEBUG("reading ~p~n",[filename:join(Dir,InitFile)]),
  {ok,AbsForms} = 
    epp:parse_file(filename:join(Dir,InitFile),[Dir],[]),
  children({dir,Dir},AbsForms).

children(Sources,InitAbsForms) ->
    Children = % List with tuples of the form {ProcessType,
               % ModuleName} of all the modules started by the
               % supervisor. This info was obtained in etoe
	uniq(map(fun({call,_,{atom,_,spawn},[Mod,Fun,Args]}) ->
			 {worker,erl_parse:normalise(Mod)}; 
		    %% Obtains the module name from its abstract form
		    ({call,_,{remote,_,{atom,_,gen_server},{atom,_,start}},Args}) ->
			 case Args of
			     [Reg,Mod,As,_] -> % we do not use name of
                                               % registered proc
				 {gen_server,erl_parse:normalise(Mod)};
			     [Mod,As,_] ->
				 {gen_server,erl_parse:normalise(Mod)}
			 end
		 end,		 
		 extract_inits(InitAbsForms))), % Expressions inside
                                                % the init function
    ?DEBUG("Started processes: ~p~n",[Children]),

    combine_mods(Sources,Children,
		 split_code(map(fun(A) -> update_init(A) end, InitAbsForms))).


file(Dir,InitFile,Dest) ->
  AbsForms = forms(Dir,InitFile),
  Mod = list_to_atom(filename:basename(Dest,".erl")),
  file:write_file(Dest,
       map(fun(AbsForm) -> [erl_pp:form(AbsForm),"\n"] end, AbsForms)).

  
extract_inits([AbsForm|AbsForms]) ->
  case AbsForm of
       {function,_,init,0,[{clause,_,_,_,Exprs}]} ->
         Exprs;
       _ ->
         extract_inits(AbsForms)
  end.


update_init(AbsForm) ->
  case AbsForm of
       {function,L1,init,0,[{clause,L2,[],Guards,Exprs}]} ->
         {function,L1,init,0,[{clause,L2,[],Guards,update_init2(Exprs,0)}]};
       _ ->
         AbsForm
  end.

update_init2([],Pid) ->
  [];
update_init2([Expr|Exprs],Pid) ->
  case Expr of
       {call,L1,{atom,L2,spawn},[M,Fun,Args]} ->
	  %% spawn(Mod, Fun, Args) is translated into Mod_Init (pid(Pid),Args)
	  NewF = list_to_atom(
                   atom_to_list(erl_parse:normalise(M))++"_"++
                   atom_to_list(erl_parse:normalise(Fun))),
         [{call,L1,{atom,L2,NewF},
	   [{call,L2,{atom,1,pid},[{integer,1,Pid}]}|abslist_to_list(Args)]}|
          update_init2(Exprs,Pid+1)];
      {call,L1,{remote,L2,{atom,_,gen_server},{atom,_,start}},Args} ->
	  %% gen_server:start([Reg, Mod, Args]) is translated into ?MCRLSERVER:Mod(Reg,Args)
	  case Args of
              [Reg,M,As,_] ->
		  RName = regname(Reg),
		  NewF = erl_parse:normalise(M),
		  %% We don't need to compute Name as intermediate value, it's not used anymore 
		  %% Name = atom_to_list(erl_parse:normalise(M)),
		  %% NewF = list_to_atom(Name),
		  [{call,L1,{remote,L1,{atom,L1,?MCRLSERVER},{atom,L1,NewF}},
		    [RName,As]}|
		   update_init2(Exprs,Pid)];
              [M,As,_] ->
		  Name = atom_to_list(erl_parse:normalise(M)),
                NewF = list_to_atom(Name),
                [{call,L1,{remote,L1,{atom,L1,?MCRLSERVER},{atom,L1,NewF}},
                         [{call,L2,{atom,1,pid},[{integer,1,Pid}]},As]}|
                  update_init2(Exprs,Pid+1)]
         end
  end.

%% 'Sources' is either {dir, Dir} or {absforms, AbsFormsList}

combine_mods(Sources,[],{Proc,SEFs,Acts}) ->
    BifsDir = 
	%% directory inside the etomcrl directory tree where the
	%% etomcrl bifs are stored
	filename:join(filename:dirname(code:which(?MODULE)),"../erlang"),
    {ok,AbsForms} =
	epp:parse_file(filename:join(BifsDir,"bifs.erl"),[BifsDir],[]),
    BIFs = [A || A<-AbsForms, element(1,A)==function], % Only function
                                                       % declarations
    [{attribute,1,module,list_to_atom(?PMCRLFile)}|
     %% Underscores and records are removed from SEFs++BIFs
     norecords:forms(sefmodify(0,nofreevar:forms(SEFs++BIFs))) ++
     [{attribute,0,copyright,{actions,Acts}}|Proc]];
combine_mods(Sources,[{Type,Mod}|Rest],{Proc,SEFs,Acts}) ->
    ?DEBUG("analyzing ~p ~p~n",[Type,Mod]),
    AbsForms =
	case Type of
	    gen_server ->
		gs_replace(Mod,bifredefine(find(Mod,Sources)));
	    _ ->
		bifredefine(find(Mod,Sources))
	end,
    {TopAbsForms,SefAbsForms,Actions} =
	%% locals:forms/1 substitutes all the local function calls
	%% (the functions defined inside the module) by
	%% Module_FunctionName
	split_code(locals:forms(AbsForms)),
    SEF = sef(Mod,SefAbsForms),
    %% SEF = [{atom(),integer()}] where the first element is the
    %% function name and the second one its arity
    combine_mods(Sources,Rest,
		 {procmodify(TopAbsForms,SEF)++Proc, 
		  SefAbsForms++SEFs, % Sef part is added without changes
		  adduniq(Actions,Acts)}). % New actions are added


%% AbsForms are the side effect forms of one module 
%%
%% SEF is a list of [{atom(),integer()}] where the first element is
%% the function name and the second one its arity (SEF is only used by
%% matches:forms/2

procmodify(AbsForms,SEF) ->
   norecords:forms(% maybe can be done in the etoe phase. Doing this
                   % transformation here, records with the same name
                   % in different modules are not supported since it
                   % is done in the code as a whole, without taking
                   % into account the modules.
   conftau:forms(
   sumvars:forms(
     callreturn:forms(
       matches:forms( % maybe can be done in the etoe phase?
         varargs:forms(% maybe can be done in the etoe phase
           nofreevar:forms( % should be called nounderscore, since
                            % that's what it does. We would numerate
                            % the vars as Underscore1, etc. Maybe can
                            % be done in a different place
                            % (etoe). However, not only the
                            % underscores that were originally in the
                            % Erlang code are substituted, also the
                            % ones we have introduced, for instance in
                            % 'gs_addself' we have introduced some for
                            % the Msg returned in a
                            % gen_server_replied. Therefore, THE ORDER
                            % MATTERS here. The way it is done now
                            % 'nofreevar' should be done after
                            % 'gs_addself)
               gs_addself:forms(
                 addself:forms(AbsForms)))),SEF))))).

%% Given a module name (Mod), returns the AbsForms for that module,
%% extracting them either from the file in the given directory, or
%% from the AbsFormsList

find(Mod,{dir,Dir}) ->
  File = atom_to_list(Mod)++".erl",
  {ok,AbsForms} = 
     epp:parse_file(filename:join(Dir,File),[Dir],[]),
  AbsForms;
find(Mod,{absforms,[]}) ->
  exit("Error: cannot find parsed module "++atom_to_list(Mod));
find(Mod,{absforms,[[{attribute,_,module,Mod}|AbsForms]|_]}) ->
  [{attribute,0,module,Mod}|AbsForms];
find(Mod,{absforms,[_|AbsFormsList]}) ->
  find(Mod,{absforms,AbsFormsList}).

%% Deletes the functions in predefined(), they are already in
%% 'bifs.erl' and we want to replace the user implementation with the
%% one we have in etomcrl

bifredefine(AbsForms) ->
  foldr(fun(AbsForm,Forms) ->
           case AbsForm of
                {function,_,Name,Arity,_} ->
                  case member({Name,Arity},predefined()) of
                       true ->
                         Forms;
                       false ->
                         [AbsForm|Forms]
                  end;
                _ ->
                  [AbsForm|Forms]
           end
        end,[],AbsForms).

predefined() -> % Used for accessing the message tags of the gen_server
  [{gen_tag,1},{gen_modtageq,2}].



%% Returns: {AbsForms,Sef,Acts}
%% AbsForms is the list of abstract forms of the code after the
%% copyright attribute (the top, side effect, code)
%% Sef is the list of abstract forms of the code before the copyright
%% attribute (the side effect free code)
%% Acts is the list of actions inside the copyright attribute

split_code(AbsForms) ->
  until_copyright(AbsForms,[]).

until_copyright([{attribute,_,author,_}|AbsForms],Sef) ->
  until_copyright(AbsForms,Sef);
until_copyright([{attribute,_,behaviour,_}|AbsForms],Sef) ->
  until_copyright(AbsForms,Sef);
until_copyright([{attribute,_,module,_}|AbsForms],Sef) ->
  until_copyright(AbsForms,Sef);
until_copyright([{attribute,_,file,_}|AbsForms],Sef) ->
  until_copyright(AbsForms,Sef);
until_copyright([{attribute,_,copyright,{actions,Acts}}|AbsForms],Sef) ->
  {AbsForms,Sef,Acts};
until_copyright([AbsForm|AbsForms],Sef) ->
  until_copyright(AbsForms,[AbsForm|Sef]).


%% All the functions that have to do with the generic server (init,
%% handle_call, handle_cast) are transformed into ?SERVERLOOP,
%% including the {reply,...} and {noreply,...} returned by the
%% callback modules of the generic servers.  
%% They are also deleted from the list of export attribute 
%% +type gs_replace(module(),[absform()]) -> [absform()].

gs_replace(Mod,AbsForms) ->
  {NewAbsForms,LoopClauses} =
    foldr(fun(A,{As,LCs}) ->
             case gs_replace2(Mod,A) of
                  {loopclauses, NLCs} ->
                    {As,NLCs++LCs};
                  NA ->
                    {[NA|As],LCs}
             end
          end,{[],[]},AbsForms),
  NewAbsForms ++ 
    [{function,0,?SERVERLOOP,1,LoopClauses}].

gs_replace2(Mod,{function,Line,init,1,Clauses}) ->
  case Clauses of
       [{clause,_,[Pat],Guards,Exprs}] -> % Only one clause in the init function
         {function,Line,init,1,
                   [{clause,Line,[Pat],Guards,initloop(Exprs)}]};
       _ -> % Why is it an error when we have more than one clause? ==> Assumption
         exit("Error: gen_server "++atom_to_list(Mod)++
              ": more than 1 init clause")
  end;
gs_replace2(Mod,{function,Line,handle_call,3,Clauses}) ->
    {loopclauses,map(fun(C) -> handlecallloop(C) end, Clauses)};
gs_replace2(Mod,{function,Line,handle_cast,2,Clauses}) ->
    {loopclauses,map(fun(C) -> handlecastloop(C) end, Clauses)};
gs_replace2(Mod,{attribute,Line,export,Exports}) ->    
    {attribute,Line,export,Exports--[{handle_call,3},{handle_cast,2},{init,1}]};
gs_replace2(Mod,AbsForm) ->
    AbsForm.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Removes repeated elements from the list L

uniq(L) ->
  adduniq(L,[]).

adduniq([],L) ->
  L;
adduniq([E|Es],L) ->
  case member(E,L) of
       true ->
         adduniq(Es,L);
       false ->
         adduniq(Es,[E|L])
  end.

%% The body of the init function inside the generic server:
%%
%% Expr1,
%% Expr2,
%% {ok,Rest}.
%%
%% is translated into:
%%
%% Expr1,
%% Expr2,
%% ?SERVERLOOP(Rest)

initloop([E]) ->
  case E of
       {tuple,Line,[{atom,_,ok}|Rest]} ->
         [{call,Line,{atom,Line,?SERVERLOOP},Rest}];
       _ ->
         exit("Error: gen_server init not ending with {ok,...}")
  end;
initloop([E|Es]) ->
  [E|initloop(Es)].


%% handle_call(Msg, Client, State) when Guards -> 
%%   Expr1,
%%   Expr2,
%%   ...
%%   ExprN.
%%
%% handle_call(State) -> 
%%      handle_call(?MCRLSelf, Msg, Client)
%%      Expr1,
%%      Expr2,
%%      ...
%%      ExprN-1
%%      handlecall(ExprN).
%%
%% handlecall({noreply,E} -> ?SERVERLOOP(E)
%% handlecall({reply,Msg,E} -> gen_server:reply(Client,Msg), ?SERVERLOOP(E)
%% handlecall(case...) -> handlecall(caseclauses) 
%%    for every clause inside the case, we translate the last expression

handlecallloop({clause,Line,[Msg,Client,State],Guards,Body}) ->
  {clause,Line,[State],Guards,
     [{call,1,{atom,1,handle_call},[{var,0,?MCRLSelf},Msg,Client]}|
      handlecalls(Client,Body)]}.

handlecalls(Client,[Expr]) ->
  handlecall(Client,Expr);
handlecalls(Client,[Expr|Exprs]) ->
  [Expr|handlecalls(Client,Exprs)].


handlecall(Client,Expr) ->
  case Expr of
       {clause,Line,Pats,Guards,Body} -> % Used for the 'case' clauses
         {clause,Line,Pats,Guards,handlecalls(Client,Body)};
       {'case',Line,E,Clauses} ->
         [{'case',Line,E,
                   map(fun(C) -> handlecall(Client,C) end, Clauses)}];
       {tuple,Line,[{atom,_,noreply},E]} ->
         [{call,Line,{atom,1,?SERVERLOOP},[E]}];
       {tuple,Line,[{atom,_,reply},Msg,E]} ->
         [{call,Line,
                {remote,1,{atom,1,gen_server},{atom,1,reply}},[Client,Msg]},
          {call,Line,{atom,1,?SERVERLOOP},[E]}
         ];
       _ ->
         io:format("Warning line "++integer_to_list(element(2,Expr))++
                   ": unchecked end of handle_call~n",[]),
         [Expr]
  end.

%% Same as handlecallloop but for handle_calls (no replay message, and
%% different arguments)

handlecastloop({clause,Line,[Msg,State],Guards,Body}) ->
  {clause,Line,[State],Guards,
     [{call,1,{atom,1,handle_cast},[{var,0,?MCRLSelf},Msg]}| handlecasts(Body)]}.

handlecasts([Expr]) ->
  handlecast(Expr);
handlecasts([Expr|Exprs]) ->
  [Expr|handlecasts(Exprs)].

handlecast(Expr) ->
  case Expr of
       {clause,Line,Pats,Guards,Body} ->
         {clause,Line,Pats,Guards,handlecasts(Body)};
       {'case',Line,E,Clauses} ->
         [{'case',Line,E,
                   map(fun(C) -> handlecast(C) end, Clauses)}];
       {tuple,Line,[{atom,_,noreply},E]} ->
         [{call,Line,{atom,1,?SERVERLOOP},[E]}];
       _ ->
         io:format("Warning line "++integer_to_list(element(2,Expr))++
                   ": unchecked end of handle_cast~n",[]),
         [Expr]
  end.

% different from erl_parse:abstract and erl_parse:normalise, since
% not recursively applied
%
abslist_to_list({nil,_}) ->
  [];
abslist_to_list({cons,_,H,T}) ->
  [H|abslist_to_list(T)].

list_to_abslist([]) ->
  {nil,0};
list_to_abslist([H|T]) ->
  {cons,0,H,list_to_abslist(T)}.

%% Auxiliar function to extract from the abstract form, the name of the registered process

regname({tuple,_,[{atom,_,local},{atom,Line,Name}]}) ->
  {atom,Line,Name};
regname(X) ->
  X.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sefmodify(Max,[]) ->
  [];
sefmodify(Max,[{function,Line,F,A,Clauses}|AbsForms]) ->

  {NewMax,NewClauses,NewAbsForms} =

    foldr(fun({clause,L,Pats,Guards,Exprs},{M,NCs,NAs}) ->
             {NM,NewExpr,ExtraAs} =
                rmstatement(M, % Maximum
			    uniq(pattern:vars(Pats)), 
						% Set of variables in
						% the clause pattern
			    Exprs), % Body of the clause
             {NM,[{clause,L,Pats,Guards,[NewExpr]}|NCs],ExtraAs++NAs}
          end,
	  {Max,[],AbsForms},
	  Clauses),

  [{function,Line,F,A,NewClauses}|sefmodify(NewMax,NewAbsForms)];

sefmodify(Max,[{attribute,L,record,Rec}|AbsForms]) -> % Record attributes are not modified
  [{attribute,L,record,Rec}|sefmodify(Max,AbsForms)];

sefmodify(Max,[_|AbsForms]) -> % Any other form is ignored
  sefmodify(Max,AbsForms).

%% Returns {NM,NewExpr,ExtraAs}
%%

rmstatement(Number,Vars,[Expr]) ->
  case Expr of
       {match,_,P,E} -> % P=E as the last expression of the clause body
         {Number,E,[]}; % P=E is substituted by E
       {'case',Line,E,Clauses} -> % 'case' as the last expression of the clause body
         NewFun = number('case',Number),
         {Number+1, 

	  %%  functionName (Var1,Var2,...,VarN) ->
	  %%           case E of
	  %%              P1 -> Body1;
	  %%              ...
	  %%              PN -> BodyN
	  %%           end.
	  %%
	  %% is translated into: 
	  %%  functionName(Var1,Var2,...,VarN) ->
	  %%           caseNumber(Var1,Var2,...,VarN, E)
	  %%
	  %% caseNumber(Var1, Var2,...,VarN, P1) -> Body1;
	  %% ...
	  %% caseNumber(Var1, Var2,...,VarN, PN) -> BodyN.
	  %%
	  %% This means that a new function is added to the abstract
	  %% forms and that the expression inside the previous
	  %% function (with the case statement) is replaced by a
	  %% function call

          {call,Line,{atom,1,NewFun},Vars++[E]},
          [{function,Line,NewFun,length(Vars)+1,
                     map(fun({clause,L,[P],Guards,Body}) ->
                             {clause,L,Vars++[P],Guards,Body}
                          end,Clauses)}]};
       _ ->
         {Number,Expr,[]}
  end;
rmstatement(Number,Vars,[{match,Line,P,E}|Exprs]) ->
    NewFun = number(match,Number),
    {Number+1,

     %%   functionName(Var1,...VarN) -> 
     %%              P = E,
     %%              Exprs.
     %%
     %% is translated into:
     %%   functionName(Var1,...VarN) -> 
     %%              matchNumber(Var1,...,VarN,E).
     %%
     %%   matchNumber(Var1,...,VarN, P) ->
     %%              Exprs.

   {call,Line,{atom,1,NewFun},Vars++[E]},
   [{function,Line,NewFun,length(Vars)+1,
     [{clause,1,Vars++[P],[],Exprs}]}]};
rmstatement(Number,Vars,[Expr|Exprs]) ->
    io:format("Error: sequence in side-effect free function part~n",[]),
    {Number,[Expr|Exprs],[]}.


%% Concatenates an atom and an integer

number(Atom,Int) ->
  list_to_atom(atom_to_list(Atom)++integer_to_list(Int)).



%% What is sef/2 doing? Why Mod is not used?
%%
%%
%% It is NOT CHECKED whether all remote functions are indeed side-effect
%% free
%%
%% sef(atom(), absforms()) -> [{atom(),integer()}]

sef(Mod,[]) ->
  [];
sef(Mod,[{function,_,Name,Arity,_}|AbsForms]) ->
  [{Name,Arity}|sef(Mod,AbsForms)];
sef(Mod,[_|AbsForms]) ->
  sef(Mod,AbsForms).



