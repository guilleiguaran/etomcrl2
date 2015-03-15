%
% collect variables and atoms from AbsForms 
%
% Thomas Arts
% March 2001

-module(collect).

-export([vars/1,atoms/1]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

atoms(AbsForms) ->
  uniq(forms(AbsForms,atom)).

vars(AbsForms) ->
  uniq(forms(AbsForms,var)).

uniq(X) ->
  ordsets:to_list(ordsets:from_list(X)).

%+type forms([abs_form()]) -> [absvar() | absatom()].
%
forms(AbsForms,Collect) ->
  foldl(fun(AbsForm,Rs) ->
               Rs++form(AbsForm,Collect)
        end,[],AbsForms).

%+type form(abs_form()) -> [absvar() | absatom()].
%
form({function,Line,Name,Arity,Clauses},Collect) ->
  foldl(fun(Clause,Rs) ->
           Rs++clause(Clause,Collect)
        end,[],Clauses);
form(AbsForm,Collect) ->
  [].


clause({clause,Line,P0,G0,B0},Collect) ->
    P1 = patterns(P0,Collect),
    G1 = guard(G0,Collect),
    B1 = exprs(B0,Collect),
    P1++G1++B1.

%%  These patterns are processed "sequentially" for purposes of variable
%%  definition etc.

patterns(Ps,Collect) ->
  foldl(fun(P,Rs) ->
           Rs++pattern(P,Collect)
        end,[],Ps).

pattern({var,Line,V},var) -> [{var,Line,V}];
pattern({var,Line,V},_) -> [];
pattern({match,Line,L0,R0},Collect) ->
    L1 = pattern(L0,Collect),
    R1 = pattern(R0,Collect),
    L1++R1;
pattern({integer,Line,I},integer) -> [{integer,0,I}];
pattern({integer,Line,I},_) -> [];
pattern({float,Line,F},float) -> [{float,0,F}];
pattern({float,Line,F},_) -> [];
pattern({atom,Line,A},atom) -> [{atom,0,A}];
pattern({atom,Line,A},_) -> [];
pattern({string,Line,S},Collect) -> [];
pattern({nil,Line},Collect) -> [];
pattern({cons,Line,H0,T0},Collect) ->
    H1 = pattern(H0,Collect),
    T1 = pattern(T0,Collect),
    H1++T1;
pattern({tuple,Line,Ps0},Collect) ->
    patterns(Ps0,Collect);
pattern({record,Line,Name,Pfs0},Collect) ->
    pattern_fields(Pfs0,Collect);
pattern({record_field,Line,Rec0,Field0},Collect) ->
    Rec1 = expr(Rec0,Collect),
    Field1 = expr(Field0,Collect),
    Rec1++Field1;
pattern({bin,Line,Fs},Collect) -> [];
pattern({op,Line,'++',{nil,_},R},Collect) ->
    pattern(R,Collect);
pattern({op,Line,'++',{cons,Li,{integer,L2,I},T},R},Collect) ->
    pattern({cons,Li,{integer,L2,I},{op,Li,'++',T,R}},Collect);
pattern({op,Line,'++',{string,Li,L},R},Collect) ->
    [];
pattern({op,Line,Op,A},Collect) ->
    [];
pattern({op,Line,Op,L,R},Collect) ->
    [].


%% -type pattern_fields([Field]) -> [Field].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

pattern_fields([{record_field,Lf,{atom,La,F},P0}|Pfs],Collect) ->
    case Collect of
         atom ->
           [{atom,0,F}];
         _ ->
           []
    end ++
    pattern(P0,Collect) ++ pattern_fields(Pfs,Collect);
pattern_fields([],_) -> [].

guard([G0|Gs],Collect) when list(G0) ->
    guard(Gs,Collect);
guard(L,Collect) ->
    [].

exprs(Es,Collect) ->
  foldl(fun(E,Rs) ->
           Rs++expr(E,Collect)
        end,[],Es).

%% -type expr(Expression) -> Expression.

expr({var,Line,V},var) -> [{var,0,V}];
expr({var,Line,V},_) -> [];
expr({integer,Line,I},integer) -> [{integer,0,I}];
expr({integer,Line,I},_) -> [];
expr({float,Line,F},float) -> [{float,0,F}];
expr({float,Line,F},_) -> [];
expr({atom,Line,A},atom) -> [{atom,0,A}];
expr({atom,Line,A},_) -> [];
expr({string,Line,S},Collect) -> [];
expr({nil,Line},Collect) -> [];
expr({cons,Line,H0,T0},Collect) ->
    H1 = expr(H0,Collect),
    T1 = expr(T0,Collect),
    H1++T1;
expr({lc,Line,E0,Qs0},Collect) ->
    Qs1 = lc_quals(Qs0,Collect),
    E1 = expr(E0,Collect),
    E1++Qs1;
expr({tuple,Line,Es0},Collect) ->
    exprs(Es0,Collect);
expr({record_index,Line,Name,Field0},Collect) ->
    case Collect of
         atom ->
           [{atom,0,Name}|expr(Field0,Collect)];
         _ ->
           expr(Field0,Collect)
    end;
expr({record,Line,Name,Inits0},Collect) ->
    case Collect of
         atom ->
           [{atom,0,Name}|record_inits(Inits0,Collect)];
         _ ->
           record_inits(Inits0,Collect)
    end;
expr({record_field,Line,Rec0,Name,Field0},Collect) ->
    expr(Rec0,Collect) ++ expr(Field0,Collect);
expr({record,Line,Rec0,Name,Upds0},Collect) ->
    Rec1 = expr(Rec0,Collect),
    Upds1 = record_updates(Upds0,Collect),
    Rec1++Upds1;
expr({record_field,Line,Rec0,Field0},Collect) ->
    Rec1 = expr(Rec0,Collect),
    Field1 = expr(Field0,Collect),
    Rec1++Field1;
expr({block,Line,Es0},Collect) ->
    %% Unfold block into a sequence.
    exprs(Es0,Collect);
expr({'if',Line,Cs0},Collect) ->
    icr_clauses(Cs0,Collect);
expr({'case',Line,E0,Cs0},Collect) ->
    E1 = expr(E0,Collect),
    Cs1 = icr_clauses(Cs0,Collect),
    E1++Cs1;
expr({'receive',Line,Cs0},Collect) ->
    icr_clauses(Cs0,Collect);
expr({'receive',Line,Cs0,To0,ToEs0},Collect) ->
    To1 = expr(To0,Collect),
    ToEs1 = exprs(ToEs0,Collect),
    Cs1 = icr_clauses(Cs0,Collect),
    Cs1++To1++ToEs1;
expr({'fun',Line,Body},Collect) ->
    case Body of
	{clauses,Cs0} ->
	    icr_clauses(Cs0,Collect);
	{function,F,A} ->
	    [];
	{function,M,F,A} ->			%This is an error in lint!
	    []
    end;
expr({call,Line,F0,As0},Collect) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    %F1 = expr(F0,Collect),
    exprs(As0,Collect);
expr({'catch',Line,E0},Collect) ->
    %% No new variables added.
    expr(E0,Collect);
expr({'query', Line, E0},Collect) ->
    %% lc expression
    expr(E0,Collect);
expr({match,Line,P0,E0},Collect) ->
    E1 = expr(E0,Collect),
    P1 = pattern(P0,Collect),
    P1++E1;
expr({bin,Line,Fs},Collect) ->
    [];
expr({op,Line,Op,A0},Collect) ->
    expr(A0,Collect);
expr({op,Line,Op,L0,R0},Collect) ->
    expr(L0,Collect) ++ expr(R0,Collect).

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is],Collect) ->
    expr(Val0,Collect)++record_inits(Is,Collect);
record_inits([],_) -> [].

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us],Collect) ->
    expr(Val0,Collect)++record_inits(Us,Collect);
record_updates([],_) -> [].

%% -type icr_clauses([Clause]) -> [Clause].

icr_clauses([C0|Cs],Collect) ->
    C1 = clause(C0,Collect),
    C1++icr_clauses(Cs,Collect);
icr_clauses([],_) -> [].

%% -type lc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_quals([{generate,Line,P0,E0}|Qs],Collect) ->
    E1 = expr(E0,Collect),
    P1 = pattern(P0,Collect),
    P1++E1++lc_quals(Qs,Collect);
lc_quals([E0|Qs],Collect) ->
    E1 = expr(E0,Collect),
    E1++lc_quals(Qs,Collect);
lc_quals([],Collect) -> [].

%% -type fun_clauses([Clause]) -> [Clause].

