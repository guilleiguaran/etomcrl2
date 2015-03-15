% 
% replace matches on sourcecode level (abstract forms)
%   i.e. X = f(...), g(X), h(X)
%   is replaced by  g(f(...)), h(f(...))
%   but also for a pattern Pat(X,Y) = f(...), g(X), h(Y)
%       we introduce inverses :  g(inv1(f(...))), h(inv2(f(...)))
%
%   this is only safe for side effect free calls, hence
%   a list of side effect free functions should be provided
%   For these functions the matches will be removed
%
%   replace matches for functions with side effect to 
%   action for reading value rcallreturn(Self,Value)
%   (sum is added later).
%
%% <p> created  Nov2001  Thomas Arts</p>
%% <p> modified Sep 2003  Thomas Arts</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(matches).

-export([forms/2,form/2,file/2,file/3]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%+type forms([abs_form()],[funs()]) -> [abs_form()].
%
forms(AbsForms,SEF) ->
  map(fun(AbsForm) -> form(AbsForm,SEF) end,AbsForms).

%+type form(abs_form(),[funs()]) -> abs_form().
%
form({function,Line,Name,Arity,Clauses},SEF) ->
  {NewClauses,_,_} = clauses(Clauses,SEF,[]),
  {function,Line,Name,Arity,NewClauses};
form(AbsForm,SEF) ->
  AbsForm.

%+type file(filename(),[fun()]) -> [abs_form()] 
%
file(FileName,SEF) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms,SEF).

%+type file(filename(),filename(),[fun()]) -> ok.
%
file(Source,Dest,SEF) ->
  AbsForms = tl(file(Source,SEF)),
  ok = 
    file:write_file(Dest, map(fun(A) -> erl_pp:form(A) end, AbsForms)).


%%% modified erl_id_trans

clauses([C0|Cs],SEF,Bindings) ->           % forced local scope
    {C1,Sef1,_} = clause(C0,SEF,Bindings),
    {C1s,Sef2,_} = clauses(Cs,SEF,Bindings),
    {[C1|C1s],Sef1 and Sef2,Bindings};
clauses([],SEF,Bindings) -> 
    {[],true,Bindings}.

clause({clause,Line,P0,G0,B0},SEF,Bindings) ->
    {B1,Sef,Bs1} = exprs(B0,SEF,Bindings),
    {{clause,Line,P0,G0,B1},Sef,Bs1}.

% only one element in pattern list (i.e. from 'case')
% Why is this never used in the compiler code?
%matchclause({clause,Line,[P0],G0,B0},Expr,SEF,Bindings) ->
%    %?DEBUG("match ~p = ~p~n",[P0,Expr]),
%    {P1,Sef1,Bs1} = match1(P0,Expr,[],SEF,Bindings),
%    %?DEBUG("~p bindings added ~p~n",[Sef1,Bs1--Bindings]),
%    {B1,Sef2,Bs2} = exprs(B0,SEF,Bs1),
%    {{clause,Line,[P0],G0,B1},Sef2,Bindings}.   % force local scope 

exprs([{match,Line,P0,E0}|Es],SEF,Bindings) ->
    match(P0,E0,Es,SEF,Bindings);
exprs([E0|Es],SEF,Bindings) ->
    {E1,Sef1,Bs1} = expr(E0,SEF,Bindings),
    {Es1,Sef2,Bs2} = exprs(Es,SEF,Bs1),
    {[E1|Es1],Sef1 and Sef2,Bs2};
exprs([],SEF,Bindings) -> 
    {[],true,Bindings}.

%% We think exprs and expr_list do the same

expr_list([{match,Line,P0,E0}|Es],SEF,Bindings) ->
    {E1,Sef1,Bs1} = match(P0,E0,[],SEF,Bindings),
    {Es1,Sef2,Bs2} = expr_list(Es,SEF,Bs1),
    {[E1|Es1],Sef1 and Sef2,Bs2};
expr_list([E0|Es],SEF,Bindings) ->
    {E1,Sef1,Bs1} = expr(E0,SEF,Bindings),
    {Es1,Sef2,Bs2} = expr_list(Es,SEF,Bs1),
    {[E1|Es1],Sef1 and Sef2,Bs2};
expr_list([],SEF,Bindings) -> 
    {[],true,Bindings}.


%% P0 = E0,
%% Es

match(P0,E0,Es,SEF,Bindings) ->
    {E1,Sef1,Bs1} = expr(E0,SEF,Bindings),
    %?DEBUG("match found ~p (sef ~p)~n",[E1,Sef1]),
    case Sef1 of
	true ->  
	    %% no side effects on match rhs	    
	    match1(P0,E1,Es,SEF,Bs1);
	false -> % side effects on match rhs
	    {Es1,Sef2,Bs2} = exprs(Es,SEF,Bs1),
	    %% E0, recallresult(P0) | Es
	    {[E1,
	      {call,0,{atom,0,rcallresult},[P0]}|
	      Es1],false,Bs2}
    end.

%% Called when E1 has no side effects
%% 
%% Bindings and assertions are added. The right-hand side of the
%% pattern matching replaces the occurrences of the left-hand side,
%% roughly speaking

match1(P0,E1,Es,SEF,Bindings) -> 
  {AddBindings,Assertions} = pattern:patmatch(P0,E1),
  %?DEBUG("bindings: ~p~nassertions ~p~n",[AddBindings,Assertions]),
  NewBindings = Bindings++AddBindings,  %% add unicity check!
  case {Assertions,Es} of
       {[],[]} -> 
         {[E1],true,NewBindings};
       {[],_} ->
         exprs(Es,SEF,NewBindings);
       _ ->
         {AssertBlock,_,_} =
           expr({call,0,{atom,0,assertion},[join(Assertions)]},SEF,NewBindings),
           {Es1,Sef2,Bs2} = exprs(Es,SEF,NewBindings),
           {[AssertBlock|Es1],Sef2,Bs2}
  end.

expr(Expr,SEF,Bindings) ->
  case Expr of
       {var,Line,V} ->
         case lists:keysearch(V,1,Bindings) of
              {value,{_,E1}} ->
                {E1,true,Bindings};
              false ->
                {{var,Line,V},true,Bindings}
         end;
       {cons,Line,H0,T0} ->
         {H1,Sef1,Bs1} = expr(H0,SEF,Bindings),
         {T1,Sef2,Bs2} = expr(T0,SEF,Bs1),
         {{cons,Line,H1,T1},Sef1 and Sef2,Bs2};
       {lc,Line,E0,Qs0} ->
         {Qs1,Sef1,Bs1} = lc_quals(Qs0,SEF,Bindings),
         {E1,Sef2,Bs2} = expr(E0,SEF,Bs1),
         {{lc,Line,E1,Qs1},Sef1 and Sef2,Bs2};
       {tuple,Line,Es0} ->
         {Es1,Sef,Bs1} = expr_list(Es0,SEF,Bindings),
         {{tuple,Line,Es1},Sef,Bs1};
       {record_index,Line,Name,Field0} ->
         {Field1,Sef,Bs1} = expr(Field0,SEF,Bindings),
         {{record_index,Line,Name,Field1},Sef,Bs1};
       {record,Line,Name,Inits0} ->
         {Inits1,Sef,Bs1} = expr_list(Inits0,SEF,Bindings),
         {{record,Line,Name,Inits1},Sef,Bs1};
       {record_field,Line,Rec0,Name,Field0} ->
         {Rec1,Sef1,Bs1} = expr(Rec0,SEF,Bindings),
         {Field1,Sef2,Bs2} = expr(Field0,SEF,Bs1),
         {{record_field,Line,Rec1,Name,Field1},Sef1 and Sef2,Bs2};
       {record,Line,Rec0,Name,Upds0} ->
         {Rec1,Sef1,Bs1} = expr(Rec0,SEF,Bindings),
         {Upds1,Sef2,Bs2} = expr_list(Upds0,SEF,Bindings),
         {{record,Line,Rec1,Name,Upds1},Sef1 and Sef2,Bs2};
       {record_field,Line,Rec0,Field0} ->
         {Rec1,Sef1,Bs1} = expr(Rec0,SEF,Bindings),
         {Field1,Sef2,Bs2} = expr(Field0,SEF,Bs1),
         {{record_field,Line,Rec1,Field1},Sef1 and Sef2,Bs2};
       {block,Line,Es0} ->
         {Es1,Sef,Bs1} = exprs(Es0,SEF,Bindings),
         {{block,Line,Es1},Sef,Bs1};
       {'if',Line,Cs0} ->
         {Cs1,Sef,Bs1} = clauses(Cs0,SEF,Bindings),
         {{'if',Line,Cs1},Sef,Bs1};

      %% case E0 of
      %%    (P1) when G1 -> B1
      %%    ...
      %%    (Pn) when Gn -> Bn
      %%
      %% if E0 is side effect, the clauses are analysed
      %%
      %% if E0 is side effect free, 
      %%    
      %%   a) if the pattern matching between E0 and P1 has no assertions
      %%               block B1 
      %%      is returned (B1 is also analysed before returning)
      %%
      %%   b) if there is only one clause in the case statement
      %%               block assertion(Assertions, B1)       
      %%      is returned (B1 is also analysed before returning)
      %% 
      %%   c) if there are more than one clause
      %%           case Assertions of 
      %%               true -> B1
      %%               false -> result of analysing the rest 
      %%                        of the clauses in the case
      %%      cases are translated to nested if-then-else statements
      %%      using the assertions for simulationg the pattern matching 
      %%
      %% Note: The translation doesn't work when E0 is a function with
      %% side effects (bad programming style)

      {'case',Line,E0,Cs0} ->
         case expr(E0,SEF,Bindings) of
              {E1,false,Bs1} -> % E0 is side effect, we continue the
                                % computation and return false
                {Cs1,Sef2,Bs2} = clauses(Cs0,SEF,Bs1),
                {{'case',Line,E1,Cs1},false,Bs2};

              {E1,true,Bs1} -> % E0 is side effect free
                {clause,L1,[P1],G1,B1} = hd(Cs0),
                {AddBindings,Assertions} = pattern:patmatch(P1,E1),
                {B2,Sef2,Bs2} = 
                   exprs(B1,SEF,Bs1++AddBindings),  %% add unicity check!
                case {tl(Cs0),Assertions} of
		    {_,[]} -> 
			%% There are no assertions. 
                        {{block,Line,B2},Sef2,Bs2};
                     {[],_} ->
			%% There is only one clause in the case
			%% statement (in muCRL it would a if-then-else
			%% with a delta, but we only write it here as
			%% an if-then)
                        {{block,Line,
                          [{call,Line,
                            {atom,Line,assertion},[join(Assertions)]}|B2]},
                         Sef2,Bs2};
                     {Cs1,_} ->
                       {E3,Sef3,Bs3} = expr({'case',Line,E0,Cs1},SEF,Bindings),
		       E4 = 
		         case E3 of % we don't need this block so we
                                    % ignore it (it looks better)
		            {block,_,E3s} ->
			       E3s;
			    _ ->
			       [E3]
			 end,
			%% it would be an if-then-else in muCRL
                       {{'case',Line,join(Assertions), 
                         [{clause,L1,[{atom,L1,true}],G1,B2},
                          {clause,L1,[{atom,L1,false}],G1,E4}]
                        },Sef2 and Sef3,Bs2++(Bs3--Bs2)} %% add unicity check!
                end
         end;

       {'receive',Line,Cs0} ->
         {Cs1,Sef,Bs1} = clauses(Cs0,SEF,Bindings),
         {{'receive',Line,Cs1},Sef,Bs1};
       {'receive',Line,Cs0,To0,ToEs0} ->
         {To1,Sef1,Bs1} = expr(To0,SEF,Bindings),
         {ToEs1,Sef2,Bs2} = exprs(ToEs0,SEF,Bs1),
         {Cs1,Sef3,Bs3} = clauses(Cs0,SEF,Bs2),
         {{'receive',Line,Cs1,To1,ToEs1},Sef1 and Sef2 and Sef3,Bs3};

      %% 
      {'fun',Line,Body} ->
         case Body of
	      {clauses,Cs0} ->
	        {Cs1,Sef,Bs1} = clauses(Cs0,SEF,Bindings),
	        {{'fun',Line,{clauses,Cs1}},Sef,Bs1};	     
	      {function,F,A} ->      %% TODO: might want a lookup in SEF
	        {{'fun',Line,{function,F,A}},false,Bindings};
	      {function,M,F,A} ->	%This is an error in lint!
	        {{'fun',Line,{function,M,F,A},false,Bindings}}
         end;

      %% 
      {call,Line,{atom,L1,F},As0} ->
         {As1,Sef2,Bs2} = exprs(As0,SEF,Bindings),
         {{call,Line,{atom,L1,F},As1},member({F,length(As0)},SEF) and Sef2,Bs2};

      %% 
      {call,Line,{remote,L1,{atom,L2,M},{atom,L3,F}},As0} ->
	  {As1,Sef2,Bs2} = exprs(As0,SEF,Bindings),
	  {{call,Line,{remote,L1,{atom,L2,M},{atom,L3,F}},As1},
           sef({M,F,length(As1)}) and Sef2,Bs2};
      
      {call,Line,F0,As0} ->
         %{F1,Sef1,Bs1} = expr(F0,SEF,Bindings),
         {As1,Sef2,Bs2} = exprs(As0,SEF,Bindings),
         {{call,Line,F0,As1},Sef2,Bs2};
       {'catch',Line,E0} ->
         {E1,Sef,Bs1} = expr(E0,SEF,Bindings),
         {{'catch',Line,E1},Sef,Bs1};
       {'query', Line, E0} ->
         %% lc expression
         {E,Sef,Bs1} = expr(E0,SEF,Bindings),
         {{'query', Line, E},Sef,Bs1};
       {op,Line,Op,A0} ->
         {A1,Sef,Bs1} = expr(A0,SEF,Bindings),
         {{op,Line,Op,A1},Sef,Bs1};
       {op,Line,Op,L0,R0} ->
         {L1,Sef1,Bs1} = expr(L0,SEF,Bindings),
         {R1,Sef2,Bs2} = expr(R0,SEF,Bs1),
         {{op,Line,Op,L1,R1},Sef1 and Sef2,Bs2};
       _ ->
         {Expr,true,Bindings}
  end.

%% -type record_inits([RecordInit]) -> [RecordInit].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.
%
% REPLACED by exprs
%
%record_inits([{record_field,Lf,{atom,La,F},Val0}|Is]) ->
%    Val1 = expr(Val0),
%    [{record_field,Lf,{atom,La,F},Val1}|record_inits(Is)];
%record_inits([]) -> [].
%% -type record_updates([RecordUpd]) -> [RecordUpd].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.
%
%record_updates([{record_field,Lf,{atom,La,F},Val0}|Us]) ->
%    Val1 = expr(Val0),
%    [{record_field,Lf,{atom,La,F},Val0}|record_updates(Us)];
%record_updates([]) -> [].

%% -type lc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_quals([{generate,Line,P0,E0}|Qs],SEF,Bindings) ->
    {E1,Sef1,Bs1} = expr(E0,SEF,Bindings),
    %%%P1 = pattern(P0),
    {Qs1,Sef2,Bs2} = lc_quals(Qs,SEF,Bs1),
    {[{generate,Line,P0,E1}|Qs1],Sef1 and Sef2,Bs2};
lc_quals([E0|Qs],SEF,Bindings) ->
    {E1,Sef1,Bs1} = expr(E0,SEF,Bindings),
    {Qs1,Sef2,Bs2} = lc_quals(Qs,SEF,Bs1),
    {[E1|Qs1],Sef1 and Sef2,Bs2};
lc_quals([],SEF,Bindings) ->
    {[],true,Bindings}.



sef({M,F,A}) ->
  case {M,F,A} of
       {gen_server,_,_} -> false;
       {gen_fsm,_,_} -> false;
       _ -> true
  end.

join([A]) ->
  A;
join([A|As]) ->
  {op,0,'and',A,join(As)}.
