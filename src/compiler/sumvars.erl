%% @doc
%% <p> bind all free variables in a sum construct</p>
%% <p>Thomas Arts. April 2001</p>
%% <p>Revised and commented by Juanjo
%% Sanchez Penas and Clara Benac Earle.  October 2003</p> 

-module(sumvars).

-export([forms/1,form/1,file/1,file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
  map(fun(AbsForm) -> form(AbsForm) end,AbsForms).

%+type form(abs_form()) -> abs_form().
%
form({function,Line,Name,Arity,Clauses}) ->
  ?DEBUG("~p function ~p/~p~n~p~n",[?MODULE,Name,Arity,Clauses]),
  NewClauses = clauses(Clauses),
  {function,Line,Name,Arity,NewClauses};
form(AbsForm) ->
  AbsForm.

%+type file(filename()) -> [abs_form()] 
%
file(FileName) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms).

%+type file(filename(),filename()) -> ok.
%
file(Source,Dest) ->
  AbsForms = tl(file(Source)),
  ok = 
    file:write_file(Dest, map(fun(A) -> erl_pp:form(A) end, AbsForms)).


%% Given a list of n Variables constructs:
%%  
%% mcrlsum(Vn, block 
%%                mcrlsum(Vn-1, block
%%                     ... 
%%                     mcrlsum(V1)))

sum([],Exprs) ->
  Exprs;
sum([V|Vs],Exprs) ->
  sum(Vs,[{call,0,{atom,0,mcrlsum},[V,{block,0,Exprs}]}]).


%%% modified erl_id_trans

clauses([C0|Cs]) ->
    C1 = clause(C0,[]),
    [C1|clauses(Cs)];
clauses([]) -> [].

%% The variables in the second argument are those that are known (thus
%% covered by an earlier sum) the one returned are the new once only!!

clause({clause,Line,H0,G0,B0},Vs) ->
    Vars = pattern:vars(H0)--Vs, 
    ?DEBUG("patvars: ~p~n",[Vars]),
    G1 = guard(G0), % guards are not modified
    {B1,_} = exprs(B0,Vs++Vars),
    {clause,Line,H0,G1,B1}.         % local scope, Vars not returned

%%  These patterns are processed "sequentially" for purposes of variable
%%  definition etc.

string_to_conses([], Line, Tail) ->
    Tail;
string_to_conses([E|Rest], Line, Tail) ->
    {cons, Line, {integer, Line, E}, string_to_conses(Rest, Line, Tail)}.


bit_types([]) ->
    [];
bit_types([Atom | Rest]) when atom(Atom) ->
    [Atom | bit_types(Rest)];
bit_types([{Atom, Integer} | Rest]) when atom(Atom), integer(Integer) ->
    [{Atom, Integer} | bit_types(Rest)].



guard([G0|Gs]) when list(G0) ->
    [guard0(G0) | guard(Gs)];
guard(L) ->
    guard0(L).

guard0([G0|Gs]) ->
    G1 = guard_test(G0),
    [G1|guard0(Gs)];
guard0([]) -> [].

%%  All function calls here must be type tests and only comparison
%%  operators are allowed here! Note record/2 tests are special and
%%  will be expanded later.

guard_test({atom,Line,true}) -> {atom,Line,true};
guard_test({call,Line,{atom,La,F},As0}) ->
    case erl_internal:type_test(F, length(As0)) of
	true -> As1 = gexpr_list(As0),
		{call,Line,{atom,La,F},As1}
    end;
guard_test({op,Line,Op,L0,R0}) ->
    case erl_internal:comp_op(Op, 2) of
	true ->
	    L1 = gexpr(L0),
	    R1 = gexpr(R0),			%They see the same variables
	    {op,Line,Op,L1,R1}
    end.

%% -type gexpr(GuardExpr) -> GuardExpr.

gexpr({var,Line,V}) -> {var,Line,V};
gexpr({integer,Line,I}) -> {integer,Line,I};
gexpr({float,Line,F}) -> {float,Line,F};
gexpr({atom,Line,A}) -> {atom,Line,A};
gexpr({string,Line,S}) -> {string,Line,S};
gexpr({nil,Line}) -> {nil,Line};
gexpr({cons,Line,H0,T0}) ->
    H1 = gexpr(H0),
    T1 = gexpr(T0),				%They see the same variables
    {cons,Line,H1,T1};
gexpr({tuple,Line,Es0}) ->
    Es1 = gexpr_list(Es0),
    {tuple,Line,Es1};
gexpr({record_index,Line,Name,Field0}) ->
    Field1 = gexpr(Field0),
    {record_index,Line,Name,Field1};
gexpr({record_field,Line,Rec0,Name,Field0}) ->
    Rec1 = gexpr(Rec0),
    Field1 = gexpr(Field0),
    {record_field,Line,Rec1,Name,Field1};
gexpr({call,Line,{atom,La,F},As0}) ->
    case erl_internal:guard_bif(F, length(As0)) of
	true -> As1 = gexpr_list(As0),
		{call,Line,{atom,La,F},As1}
    end;
gexpr({op,Line,Op,A0}) ->
    case erl_internal:arith_op(Op, 1) of
	true -> A1 = gexpr(A0),
		{op,Line,Op,A1}
    end;
gexpr({op,Line,Op,L0,R0}) ->
    case erl_internal:arith_op(Op, 2) of
	true ->
	    L1 = gexpr(L0),
	    R1 = gexpr(R0),			%They see the same variables
	    {op,Line,Op,L1,R1}
    end.

%% -type gexpr_list([GuardExpr]) -> [GuardExpr].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

gexpr_list([E0|Es]) ->
    E1 = gexpr(E0),
    [E1|gexpr_list(Es)];
gexpr_list([]) -> [].

%% -type exprs([Expression],BoundVars) -> [Expression].
%%  These expressions are processed "sequentially" for purposes of variable
%%  definition etc.

exprs([E0|Es],Vars) ->
    {E1,Vs} = expr(E0,Vars), % Vs contains the free variables in E0
    case Vs of
         [] -> % No need for a mcrlsum
           {E1s,NVs} = exprs(Es,Vars),
           {[E1|E1s],NVs};
         _ ->
           ?DEBUG("new found: ~p~n",[Vs]),
           {E1s,NVs} = exprs(Es,Vs++Vars), % Vs are now bounded
                                           % variables, because the
                                           % mcrlsum has already been
                                           % created for them in this
                                           % level of the analysis
           {sum(Vs,[E1|E1s]),NVs}
    end;
exprs([],Vars) -> {[],[]}.

%% -type expr(Expression,BoundVars) -> {Expression,FreeVars}.

expr({var,Line,V},Vars) -> 
  {{var,Line,V},
   case member({var,1,V},Vars) of
        true ->
          [];
        false ->  % unbound variable found
          ?DEBUG("unbound var: ~p~n",[V]),
          [{var,1,V}]
   end
  };
expr({integer,Line,I},Vars) -> {{integer,Line,I},[]};
expr({float,Line,F},Vars) -> {{float,Line,F},[]};
expr({atom,Line,A},Vars) -> {{atom,Line,A},[]};
expr({string,Line,S},Vars) -> {{string,Line,S},[]};
expr({nil,Line},Vars) -> {{nil,Line},[]};
expr({cons,Line,H0,T0},Vars) ->
    {H1,V1s} = expr(H0,Vars),
    {T1,V2s} = expr(T0,Vars++V1s),
    {{cons,Line,H1,T1},union(V1s,V2s)};
expr({lc,Line,E0,Qs0},Vars) ->
    {Qs1,V1s} = lc_quals(Qs0,Vars),
    {E1,V2s} = expr(E0,Vars++V1s),
    {{lc,Line,E1,Qs1},union(V1s,V2s)};
expr({tuple,Line,Es0},Vars) ->
    {Es1,V1s} = expr_list(Es0,Vars),
    {{tuple,Line,Es1},V1s};
expr({record_index,Line,Name,Field0},Vars) ->
    {Field1,V1s} = expr(Field0,Vars),
    {{record_index,Line,Name,Field1},V1s};
expr({record,Line,Name,Inits0},Vars) ->
    {Inits1,V1s} = record_inits(Inits0,Vars),
    {{record,Line,Name,Inits1},V1s};
expr({record_field,Line,Rec0,Name,Field0},Vars) ->
    {Rec1,V1s} = expr(Rec0,Vars),
    {Field1,V2s} = expr(Field0,Vars++V1s),
    {{record_field,Line,Rec1,Name,Field1},union(V1s,V2s)};
expr({record,Line,Rec0,Name,Upds0},Vars) ->
    {Rec1,V1s} = expr(Rec0,Vars),
    {Upds1,V2s} = record_updates(Upds0,Vars++V1s),
    {{record,Line,Rec1,Name,Upds1},union(V1s,V2s)};
expr({record_field,Line,Rec0,Field0},Vars) ->
    {Rec1,V1s} = expr(Rec0,Vars),
    {Field1,V2s} = expr(Field0,Vars++V1s),
    {{record_field,Line,Rec1,Field1},V2s};
expr({block,Line,Es0},Vars) ->
    %% Unfold block into a sequence.
    {Es1,V1s} = exprs(Es0,Vars),
    {{block,Line,Es1},V1s};
expr({'if',Line,Cs0},Vars) ->
    Cs1 = icr_clauses(Cs0,Vars),
    {{'if',Line,Cs1},[]};         % local scope
expr({'case',Line,E0,Cs0},Vars) ->
    {E1,V1s} = expr(E0,Vars),
    Cs1 = icr_clauses(Cs0,V1s++Vars),
    {{'case',Line,E1,Cs1},V1s};
expr({'receive',Line,Cs0},Vars) ->
    Cs1 = icr_clauses(Cs0,Vars),
    {{'receive',Line,Cs1},[]};
expr({'receive',Line,Cs0,To0,ToEs0},Vars) ->
    {To1,V1s} = expr(To0,Vars),
    {ToEs1,V2s} = exprs(ToEs0,Vars++V1s),
    Cs1 = icr_clauses(Cs0,V2s++V1s++Vars),
    {{'receive',Line,Cs1,To1,ToEs1},union(V1s,V2s)};
expr({'fun',Line,Body},Vars) ->
    case Body of
	{clauses,Cs0} ->
	    Cs1 = fun_clauses(Cs0,Vars),
	    {{'fun',Line,{clauses,Cs1}},[]};
	{function,F,A} ->
	    {{'fun',Line,{function,F,A}},[]};
	{function,M,F,A} ->			%This is an error in lint!
	    {{'fun',Line,{function,M,F,A}},[]}
    end;
expr({call,Line,F0,As0},Vars) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    {F1,V1s} = expr(F0,Vars),
    {As1,V2s} = expr_list(As0,Vars++V1s),
    {{call,Line,F1,As1},union(V1s,V2s)};
expr({'catch',Line,E0},Vars) ->
    %% No new variables added.
    {E1,V1s} = expr(E0,Vars),
    {{'catch',Line,E1},V1s};
expr({'query', Line, E0},Vars) ->
    %% lc expression
    {E,V1s} = expr(E0,Vars),
    {{'query', Line, E},V1s};
expr({match,Line,P0,E0},Vars) ->
    PVars = pattern:vars(P0),
    {E1,V1s} = expr(E0,Vars++PVars),
    {{match,Line,P0,E1},V1s}; %% We add PVars to the bounded variables
                              %% to avoid them to show up free later
                              %% in sequence!
expr({op,Line,Op,A0},Vars) ->
    {A1,V1s} = expr(A0,Vars),
    {{op,Line,Op,A1},V1s};
expr({op,Line,Op,L0,R0},Vars) ->
    {L1,V1s} = expr(L0,Vars),
    {R1,V2s} = expr(R0,Vars++V1s), 
    %% V1s is added to the bounded variables when computing R0, to avoid
    %% computing the same free variables twice
    {{op,Line,Op,L1,R1},union(V1s,V2s)};
%% The following are not allowed to occur anywhere!
expr({remote,Line,M0,F0},Vars) ->
    {M1,V1s} = expr(M0,Vars),
    {F1,V2s} = expr(F0,Vars++V1s),
    {{remote,Line,M1,F1},union(V1s,V2s)}.

%% -type expr_list([Expression],Vars) -> [Expression].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

expr_list([E0|Es],Vars) ->
    {E1,V1s} = expr(E0,Vars),
    {E1s,V2s} = expr_list(Es,Vars++V1s),
    {[E1|E1s],union(V1s,V2s)};
expr_list([],Vars) -> {[],[]}.

%% -type record_inits([RecordInit]) -> [RecordInit].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is],Vars) ->
    {Val1,V1s} = expr(Val0,Vars),
    {Is1,V2s} = record_inits(Is,Vars++V1s),
    {[{record_field,Lf,{atom,La,F},Val1}|Is1],union(V1s,V2s)};
record_inits([],Vars) -> {[],[]}.

%% -type record_updates([RecordUpd]) -> [RecordUpd].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us],Vars) ->
    {Val1,V1s} = expr(Val0,Vars),
    {Us1,V2s} = record_updates(Us,Vars++V1s),
    {[{record_field,Lf,{atom,La,F},Val0}|Us1],union(V1s,V2s)};
record_updates([],Vars) -> {[],[]}.

%% -type icr_clauses([Clause]) -> [Clause].

icr_clauses([C0|Cs],Vars) ->
    C1 = clause(C0,Vars),
    [C1|icr_clauses(Cs,Vars)];
icr_clauses([],Vars) -> [].

%% -type lc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_quals([{generate,Line,P0,E0}|Qs],Vars) ->
    V0s = pattern:vars(P0),
    {E1,V1s} = expr(E0,Vars++V0s),
    {Qs1,V2s} = lc_quals(Qs,Vars++V0s++V1s),
    {[{generate,Line,P0,E1}|Qs1],union(V1s,V2s)};
lc_quals([E0|Qs],Vars) ->
    {E1,V1s} = expr(E0,Vars),
    {Es,V2s} = lc_quals(Qs,Vars++V1s),
    {[E1|Es],union(V1s,V2s)};
lc_quals([],Vars) -> {[],[]}.

%% -type fun_clauses([Clause]) -> [Clause].

fun_clauses([C0|Cs],Vars) ->
    C1 = clause(C0,Vars),
    [C1|fun_clauses(Cs,Vars)];
fun_clauses([],Vars) -> [].

union([],S) ->
  S;
union([H|T],S) ->
  case member(H,S) of
       true ->
         union(T,S);
       false ->
         union(T,[H|S])
  end.
