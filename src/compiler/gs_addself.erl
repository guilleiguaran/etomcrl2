%
% changes gen_server:call 
%   (not longer handle_call, since taken care of in etopmcrl.erl)
%   by adding a Self variable
%   and putting all gen_server:call inside a match (will be a Sum later)
%
% added later: replace the call self() to Self variable 
%
%% <p>Thomas Arts. April 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(gs_addself).

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
  {function,Line,Name,Arity,clauses(Clauses)};
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
    file:write_file(Dest, 
                    map(fun(A) -> erl_pp:form(A) end, AbsForms)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% modified erl_id_trans

clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|clauses(Cs)];
clauses([]) -> [].

clause({clause,Line,H0,G0,B0}) ->
    H1 = head(H0),
    G1 = guard(G0),
    B1 = exprs(B0),
    {clause,Line,H1,G1,B1}.

head(Ps) -> patterns(Ps).

%%  These patterns are processed "sequentially" for purposes of variable
%%  definition etc.

patterns([P0|Ps]) ->
    P1 = pattern(P0),
    [P1|patterns(Ps)];
patterns([]) -> [].

string_to_conses([], Line, Tail) ->
    Tail;
string_to_conses([E|Rest], Line, Tail) ->
    {cons, Line, {integer, Line, E}, string_to_conses(Rest, Line, Tail)}.

pattern({var,Line,V}) -> {var,Line,V};
pattern({match,Line,L0,R0}) ->
    L1 = pattern(L0),
    R1 = pattern(R0),
    {match,Line,L1,R1};
pattern({integer,Line,I}) -> {integer,Line,I};
pattern({float,Line,F}) -> {float,Line,F};
pattern({atom,Line,A}) -> {atom,Line,A};
pattern({string,Line,S}) -> {string,Line,S};
pattern({nil,Line}) -> {nil,Line};
pattern({cons,Line,H0,T0}) ->
    H1 = pattern(H0),
    T1 = pattern(T0),
    {cons,Line,H1,T1};
pattern({tuple,Line,Ps0}) ->
    Ps1 = pattern_list(Ps0),
    {tuple,Line,Ps1};
%%pattern({struct,Line,Tag,Ps0}) ->
%%    Ps1 = pattern_list(Ps0),
%%    {struct,Line,Tag,Ps1};
pattern({record,Line,Name,Pfs0}) ->
    Pfs1 = pattern_fields(Pfs0),
    {record,Line,Name,Pfs1};
%% record_field occurs in query expressions
pattern({record_field,Line,Rec0,Field0}) ->
    Rec1 = expr(Rec0),
    Field1 = expr(Field0),
    {record_field,Line,Rec1,Field1};
pattern({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
pattern({op,Line,'++',{nil,_},R}) ->
    pattern(R);
pattern({op,Line,'++',{cons,Li,{integer,L2,I},T},R}) ->
    pattern({cons,Li,{integer,L2,I},{op,Li,'++',T,R}});
pattern({op,Line,'++',{string,Li,L},R}) ->
    pattern(string_to_conses(L, Li, R));
pattern({op,Line,Op,A}) ->
    {op,Line,Op,A};
pattern({op,Line,Op,L,R}) ->
    {op,Line,Op,L,R}.

pattern_grp([{bin_element,L1,E1,S1,T1} | Fs]) ->
    S2 = case S1 of
	     default ->
		 default;
	     _ ->
		 expr(S1)
	 end,
    T2 = case T1 of
	     default ->
		 default;
	     _ ->
		 bit_types(T1)
	 end,
    [{bin_element,L1,expr(E1),S2,T2} | pattern_grp(Fs)];
pattern_grp([]) ->
    [].

bit_types([]) ->
    [];
bit_types([Atom | Rest]) when atom(Atom) ->
    [Atom | bit_types(Rest)];
bit_types([{Atom, Integer} | Rest]) when atom(Atom), integer(Integer) ->
    [{Atom, Integer} | bit_types(Rest)].



%% -type pattern_list([Pattern]) -> [Pattern].
%%  These patterns are processed "in parallel" for purposes of variable
%%  definition etc.

pattern_list([P0|Ps]) ->
    P1 = pattern(P0),
    [P1|pattern_list(Ps)];
pattern_list([]) -> [].

%% -type pattern_fields([Field]) -> [Field].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

pattern_fields([{record_field,Lf,{atom,La,F},P0}|Pfs]) ->
    P1 = pattern(P0),
    [{record_field,Lf,{atom,La,F},P1}|pattern_fields(Pfs)];
pattern_fields([]) -> [].

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
gexpr({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
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

%% -type exprs([Expression]) -> [Expression].
%%  These expressions are processed "sequentially" for purposes of variable
%%  definition etc.

% ADDITION to erl_id_trans

%% gen_server:call(To,Msg) is replaced by:
%%
%% gen_server_call(To, Msg, MCRLSelf), 
%% gen_server_replied(MCRLSelf, _ ,To) 
%%
%% note that the underscore will become a MCRLFreeN (N being an
%% integer) when the module 'nofreevar'is called. So there is a
%% dependency between these two modules.

exprs([{call,L1,{remote,L2,{atom,_,gen_server},{atom,_,call}},[To,Msg]}|Es]) ->
    [{call,L1,{atom,1,gen_server_call},exprs([To,Msg,{var,1,?MCRLSelf}])},
     {call,0,{atom,0,gen_server_replied},
                                 exprs([{var,1,?MCRLSelf},{var,0,'_'},To])}|
     exprs(Es)];

%% Pattern = gen_server:call(To,Msg) is replaced by:
%%
%% gen_server_call(To, Msg, MCRLSelf),
%% gen_server_replied(MCRLSelf, Pattern, To)

exprs([{match,L0,P1,
        {call,L1,{remote,L2,{atom,_,gen_server},{atom,_,call}},[To,Msg]}}|
       Es]) ->
    [{call,L1,{atom,1,gen_server_call},exprs([To,Msg,{var,1,?MCRLSelf}])},
     {call,0,{atom,0,gen_server_replied},exprs([{var,1,?MCRLSelf},P1,To])}|
     exprs(Es)];

exprs([E0|Es]) -> % if the first expresion is not a call to the generic
                  % server nor a match involving the generic server,
                  % then 'expr' is called
    E1 = expr(E0),
    [E1|exprs(Es)];
exprs([]) -> [].

%% -type expr(Expression) -> Expression.

expr({var,Line,V}) -> {var,Line,V};
expr({integer,Line,I}) -> {integer,Line,I};
expr({float,Line,F}) -> {float,Line,F};
expr({atom,Line,A}) -> {atom,Line,A};
expr({string,Line,S}) -> {string,Line,S};
expr({nil,Line}) -> {nil,Line};
expr({cons,Line,H0,T0}) ->
    H1 = expr(H0),
    T1 = expr(T0),				%They see the same variables
    {cons,Line,H1,T1};
expr({lc,Line,E0,Qs0}) ->
    Qs1 = lc_quals(Qs0),
    E1 = expr(E0),
    {lc,Line,E1,Qs1};
expr({tuple,Line,Es0}) ->
    Es1 = expr_list(Es0),
    {tuple,Line,Es1};
%%expr({struct,Line,Tag,Es0}) ->
%%    Es1 = pattern_list(Es0),
%%    {struct,Line,Tag,Es1};
expr({record_index,Line,Name,Field0}) ->
    Field1 = expr(Field0),
    {record_index,Line,Name,Field1};
expr({record,Line,Name,Inits0}) ->
    Inits1 = record_inits(Inits0),
    {record,Line,Name,Inits1};
expr({record_field,Line,Rec0,Name,Field0}) ->
    Rec1 = expr(Rec0),
    Field1 = expr(Field0),
    {record_field,Line,Rec1,Name,Field1};
expr({record,Line,Rec0,Name,Upds0}) ->
    Rec1 = expr(Rec0),
    Upds1 = record_updates(Upds0),
    {record,Line,Rec1,Name,Upds1};
expr({record_field,Line,Rec0,Field0}) ->
    Rec1 = expr(Rec0),
    Field1 = expr(Field0),
    {record_field,Line,Rec1,Field1};
expr({block,Line,Es0}) ->
    %% Unfold block into a sequence.
    Es1 = exprs(Es0),
    {block,Line,Es1};
expr({'if',Line,Cs0}) ->
    Cs1 = icr_clauses(Cs0),
    {'if',Line,Cs1};
expr({'case',Line,E0,Cs0}) ->
    E1 = expr(E0),
    Cs1 = icr_clauses(Cs0),
    {'case',Line,E1,Cs1};
expr({'receive',Line,Cs0}) ->
    Cs1 = icr_clauses(Cs0),
    {'receive',Line,Cs1};
expr({'receive',Line,Cs0,To0,ToEs0}) ->
    To1 = expr(To0),
    ToEs1 = exprs(ToEs0),
    Cs1 = icr_clauses(Cs0),
    {'receive',Line,Cs1,To1,ToEs1};
expr({'fun',Line,Body}) ->
    case Body of
	{clauses,Cs0} ->
	    Cs1 = fun_clauses(Cs0),
	    {'fun',Line,{clauses,Cs1}};
	{function,F,A} ->
	    {'fun',Line,{function,F,A}};
	{function,M,F,A} ->			%This is an error in lint!
	    {'fun',Line,{function,M,F,A}}
    end;
expr({call,Line,F0,As0}) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    F1 = expr(F0),
    As1 = expr_list(As0),

%% gen_server:call(Args)
%% is translated into:
%% '_' = gen_server_call(Args,MCRLSelf)
%%
%% gen_server:reply(Args)
%% is translated into:
%% gen_server_reply(Args,MCRLSelf)
%%
%% self()
%% is translated into
%% MCRLSelf variable
%%


    case F1 of
         {remote,L2,{atom,_,gen_server},{atom,_,call}} ->
           {match,Line,{var,Line,'_'},
            {call,Line,{atom,L2,gen_server_call},As1++[{var,0,?MCRLSelf}]}};
	%% TODO: When is the case that we don't create the
	%% gen_server_replied?  Should be added. Even then it would
	%% not work for all the cases. Needs a careful analysis and
	%% re-implement.

         {remote,L2,{atom,_,gen_server},{atom,_,reply}} ->
           {call,Line,{atom,L2,gen_server_reply},As1++[{var,0,?MCRLSelf}]};
%        {atom,L2,handle_call} ->
%          {call,Line,{atom,L2,handle_call},[{var,0,?MCRLSelf}|As1]};
         {atom,L2,self} ->
           {var,L2,?MCRLSelf};
         _ -> 
           {call,Line,F1,As1}
    end;
expr({'catch',Line,E0}) ->
    %% No new variables added.
    E1 = expr(E0),
    {'catch',Line,E1};
expr({'query', Line, E0}) ->
    %% lc expression
    E = expr(E0),
    {'query', Line, E};
expr({match,Line,P0,E0}) ->
    P1 = pattern(P0),
    E1 = expr(E0),
    case E1 of
         {match,_,{var,_,'_'},E2} ->   % gen_server placed in this match (hack)
           {match,Line,P1,E2}; 
	%% Used in the cases where after %% analysing the E0, an
	%% expression of %%%% the type '_'=gen_server_call %%was %%
	%% created. In this case, we %%can remove %% the '_' and
	%% directly %%assing the %% gen_server_call to %%the pattern
	%% P0
	%%
	%% X = case Y of
	%%  true -> 
	%%        gen_server:call(Z)
	%%  false ->
	%% end.
	%%
	%% We don't want to get this expression:
	%%    X = '_' = gen_server_call(Z)
	%%    <|...|>
	%% Therefore, the '_' is removed

         _ ->
           {match,Line,P1,E1}
    end;
expr({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
expr({op,Line,Op,A0}) ->
    A1 = expr(A0),
    {op,Line,Op,A1};
expr({op,Line,Op,L0,R0}) ->
    L1 = expr(L0),
    R1 = expr(R0),				%They see the same variables
    {op,Line,Op,L1,R1};
%% The following are not allowed to occur anywhere!
expr({remote,Line,M0,F0}) ->
    M1 = expr(M0),
    F1 = expr(F0),
    {remote,Line,M1,F1}.

%% -type expr_list([Expression]) -> [Expression].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

expr_list([E0|Es]) ->
    E1 = expr(E0),
    [E1|expr_list(Es)];
expr_list([]) -> [].

%% -type record_inits([RecordInit]) -> [RecordInit].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is]) ->
    Val1 = expr(Val0),
    [{record_field,Lf,{atom,La,F},Val1}|record_inits(Is)];
record_inits([]) -> [].

%% -type record_updates([RecordUpd]) -> [RecordUpd].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us]) ->
    Val1 = expr(Val0),
    [{record_field,Lf,{atom,La,F},Val0}|record_updates(Us)];
record_updates([]) -> [].

%% -type icr_clauses([Clause]) -> [Clause].

icr_clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|icr_clauses(Cs)];
icr_clauses([]) -> [].

%% -type lc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_quals([{generate,Line,P0,E0}|Qs]) ->
    E1 = expr(E0),
    P1 = pattern(P0),
    [{generate,Line,P1,E1}|lc_quals(Qs)];
lc_quals([E0|Qs]) ->
    E1 = expr(E0),
    [E1|lc_quals(Qs)];
lc_quals([]) -> [].

%% -type fun_clauses([Clause]) -> [Clause].

fun_clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|fun_clauses(Cs)];
fun_clauses([]) -> [].
