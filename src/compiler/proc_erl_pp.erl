-module(proc_erl_pp).

%%  for proc part
%% pretty printing for proc part.

%% <p>Thomas Arts</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

%% Hide confluent tau action


-export([form/1,form/2,
	 attribute/1,attribute/2,function/1,function/2,%rule/1,rule/2,
	 guard/1,guard/2,exprs/1,exprs/2,exprs/3,expr/1,expr/2,expr/3,expr/4]).

-import(lists, [foldl/3,flatten/1,member/2]).
-import(io_lib, [write/1,format/2,write_char/1,write_string/1,indentation/2]).
-import(erl_parse, [inop_prec/1,preop_prec/1,func_prec/0]).

-include("etomcrl.hrl").

%% After each "thing" has been printed the cursor is left in place. It is
%% up to what comes after, or the caller to decide how to terminate the
%% previous "thing".

form(Thing) ->
     form(Thing, none).

form({attribute,Line,Name,Arg}, Hook) ->
    attribute({attribute,Line,Name,Arg}, Hook);

form({function,Line,Name,Arity,Clauses}, Hook) ->
    function({function,Line,Name,Arity,Clauses}, Hook);

%% Not used
%% form({rule,Line,Name,Arity,Clauses}, Hook) ->
%%    rule({rule,Line,Name,Arity,Clauses}, Hook);

%% These are specials to make it easier for the compiler.
form({error,E}, Hook) ->
    format("~p~n", [{error,E}]);
form({warning,W}, Hook) ->
    format("~p~n", [{warning,W}]);
form({eof,Line}, Hook) -> "\n".

attribute(Thing) ->
    attribute(Thing, none).

attribute({attribute,Line,Name,Arg}, Hook) ->
    attribute(Name, Arg, Hook).

attribute(Name, Arg, Hook) ->
    format("\n", []).


%% It seems that it is never used in the compiler
falist([]) -> "[]";
falist(Fas) -> falist(Fas, $[).
falist([{Name,Arity}|Falist], P) ->
    [P,write(Name),$/,write(Arity)|falist(Falist, $,)];
falist([], _) -> [$]].

function(F) -> function(F, none).

function({function,Line,init,0,[{clause,_,[],_,Body}]}, Hook) ->
  ["\n\n",
    "init\n     hide({"++atom_to_list(?conftau)++
    ",buffercall,buffercast,bufferinfo},\n",
    "     encap({handle_call,gen_server_call,handle_cast,gen_server_cast,\n",
    "                  gscall,gshcall,gscast,gshcast,send,gsinfo,\n",
    "                  gen_server_reply,gen_server_replied},\n",
    "\n           ",
    separated_list(fun expr/3, " ||\n           " , 10, Hook, Body),
    "\n          ))"];
function({function,Line,Name,Arity,[{clause,_,Head,Guard,Body}|Cs]}, Hook) ->
    Bodies = [Body| % Bodies for all the clauses in this function
	      [B||{clause,_,_,_,B}<-Cs]],
    [atom_to_list(Name),arg_list(Head,5,Hook)," =\n     ",
     %% In the side effect part, the different clauses of a function
     %% are going to be separated by +
     separated_list(fun exprs/3,"+\n     ", 5, Hook,Bodies),"\n\n"].

%% Not used

%% rule(R) -> rule(R, none).

%% rule({rule,Line,Name,Arity,Cs}, Hook) ->
%%    [clauses(fun (C, I, H) -> rule_clause(Name, C, H) end, 0, Hook, Cs),".\n"].

%% rule_clause(Name, {clause,Line,Head,Guard,Body}, Hook) ->
%%    [expr({call,Line,{atom,Line,Name},Head}, 0, Hook),
%%     guard(Guard, 0, Hook),
%%     rule_body(Body, 4, Hook)].

%% rule_body(Es, I, Hook) ->
%%     [" :-",nl_indent(I)|lc_quals(Es, I, Hook)].

%% guard(GuardExpressions)
%% guard(GuardExpressions, Hook)
%% guard(GuardExpressions, Indentation, Hook)

guard(Gs) -> guard(Gs, none).

guard(Gs, Hook) -> guard(Gs, 0, Hook).

guard_no_when([E|Es], I, Hook) when list(E) ->
    separated_list(fun guard0/3, "; ", I, Hook, [E|Es]);
guard_no_when([E|Es], I, Hook) ->
    guard_no_when([[E|Es]], I, Hook);
guard_no_when([], _, _) -> [].

guard([E|Es], I, Hook) when list(E) ->
    " when " ++ separated_list(fun guard0/3, "; ", I, Hook, [E|Es]);
guard([E|Es], I, Hook) ->
    guard([[E|Es]], I, Hook);
guard([], _, _) -> [].

guard0([], _, _) -> 
  [];
guard0([E], I, Hook) ->
  expr(E,I,Hook);
guard0([E|Es], I, Hook) ->
  ["and(",expr(E,I,Hook),",",guard0(Es,I,Hook),")"].

%% body(Es, Indentation, Hook) -> [Char].

body(Es, I, Hook) ->
    [" =",nl_indent(I)|exprs(Es, I, Hook)].

%% exprs(Expressions)
%% exprs(Expressions, Hook)
%% exprs(Expressions, Indentation, Punctuation, Hook)
%%  Prettyprint expressions.

exprs(Es) ->
    exprs(Es, none).

exprs(Es, Hook) ->
    exprs(Es, -10000, Hook).			%A hack to prohibit line breaks

exprs([{call,_,{atom,_,assertion},[Arg]}|Es], I, Hook) ->
    ["(",
     separated_list(fun expr/3, "." ++ nl_indent(I), I, Hook, Es),
     nl_indent(I), "<| eq(",expr(Arg,I,Hook),",true) |>", nl_indent(I),
     "delta)"];
exprs(Es, I, Hook) ->
    separated_list(fun expr/3, "." ++ nl_indent(I), I, Hook, Es).

%% expr(Expression)
%% expr(Expression, Hook)
%% expr(Expression, Indentation, Hook)
%% expr(Expression, Indentation, Precedence, Hook)
%%  Prettyprint one expr. Seeing everything is a "expr" we have to handle
%%  operator precedences for arithmetic expressions as well.
%%  N.B. We use a simple length/1 call to calculate indent

expr(E) -> expr(E, -10000, 0, none).

expr(E, Hook) -> expr(E, -10000, 0, Hook).

expr(E, I, Hook) -> expr(E, I, 0, Hook).

expr({var,_,V}, _, _, _) when integer(V) ->	%Special hack for Robert
    format("_~w", [V]);
expr({var,Line,'_'}, _, _, _) -> 
   exit("Free variable in pmcrl file! line "++integer_to_list(Line));
expr({var,_,V}, _, _, _) -> format("~s", [V]);
expr({char,_,C}, _, _, _) -> write_char(C);	%When this comes
expr({integer,_,N}, _, _, _) -> "int("++to_integer(N)++")";
expr({float,_,F}, _, _, _) -> write(F);
expr({atom,_,A}, _, _, _) -> write(A);
expr({string,_,S}, _, _, _) -> write_string(S);
expr({nil,_}, _, _, _) -> "nil";
expr({cons,_,H,T}, I, _, Hook) ->
    I1 = I + 1,
    ["cons(",expr(H, I1, 0, Hook),tail(T, I1, Hook),")"];
expr({lc,_,E,Qs}, I, Prec, Hook) ->
    ["[ ",
     expr(E, I+2, 0, Hook),
     " ||", nl_indent(I+4),
     lc_quals(Qs, I+4, Hook),
     nl_indent(I),"]"];
expr({tuple,_,Elts}, I, _, Hook) ->
    tuple_list(Elts, "tuple(", "tuplenil(", I, Hook);
%%expr({struct,_,Tag,Elts}, I, _, Hook) ->
%%    Tl = flatten(write(Tag)),
%%    [Tl|expr_list(Elts, "{", "}", I+length(Tl), Hook)];
expr({record_index, _, Name, F}, I, Prec, Hook) ->
    {P,R} = preop_prec('#'),
    Nl = flatten(write(Name)),
    El = ["#",Nl,".",expr(F, I+length(Nl)+2, R, Hook)],
    maybe_paren(P, Prec, El);
expr({record, _, Name, Fs}, I, Prec, Hook) ->
    {P,R} = preop_prec('#'),
    Nl = flatten(write(Name)),
    El = ["#",Nl,record_fields(Fs, I+length(Nl)+1, Hook)],
    maybe_paren(P, Prec, El);
expr({record_field, _, Rec, Name, F}, I, Prec, Hook) ->
    {L,P,R} = inop_prec('#'),
    Rl = expr(Rec, I, L, Hook),
    Nl = flatten(write(Name)),
    El = [Rl,"#",Nl,".",expr(F, indentation(Rl, I)+length(Nl)+2, R, Hook)],
    maybe_paren(P, Prec, El);
expr({record, _, Rec, Name, Fs}, I, Prec, Hook) ->
    {L,P,R} = inop_prec('#'),
    Rl = expr(Rec, I, L, Hook),
    Nl = flatten(write(Name)),
    El = [Rl,"#",Nl,record_fields(Fs, indentation(Rl, I)+length(Nl)+1, Hook)],
    maybe_paren(P, Prec, El);
expr({record_field, _, Rec, F}, I, Prec, Hook) ->
    {L,P,R} = inop_prec('#'),
    Rl = expr(Rec, I, L, Hook),
    El = [Rl,".",expr(F, indentation(Rl, I)+1, R, Hook)],
    maybe_paren(P, Prec, El);
expr({block,_,Es}, I, _, Hook) ->
    ["(",nl_indent(I+4),
     exprs(Es, I+4, Hook),
     nl_indent(I), ")"];
expr({'if',_,[{clause,_,[],Guards,Body}]}, I, J, Hook) ->
    case Guards of
         [] ->
           exprs(Body,I,Hook);
         [[{atom,_,true}]] ->
           exprs(Body,I,Hook);
         Guards ->
           ["(",exprs(Body, I, Hook), nl_indent(I),
            " <| eq(",guard_no_when(Guards,I,Hook),",true) |> delta)"]
    end;
%
% condition [] means non-deterministic choice
expr({'if',L,[{clause,_,[],Guards,Body}|Cs]}, I, J, Hook) ->
  case Guards of
       [[{atom,_,true}]] ->
         [exprs(Body,I,Hook)," +",nl_indent(I),expr({'if',0,Cs},I,J,Hook)];
       [] -> 
         [exprs(Body,I,Hook)," +",nl_indent(I),expr({'if',0,Cs},I,J,Hook)];
       Guards ->
         ["(",exprs(Body, I, Hook), nl_indent(I),
          " <| eq(",guard_no_when(Guards,I,Hook),",true) |>",
          expr({'if',L,Cs}, I, J, Hook),")"]
  end;
expr({'if',_,Cs}, I, _, Hook) ->
    I1 = I + 4,
    ["IF",nl_indent(I1),
     if_clauses(Cs, I1, Hook),
     nl_indent(I),"end"];
expr({'case',_,Expr,[C1]}, I, _, Hook) ->  % as two, but with delta
    I1 = I + 4,
    {clause,_,[T1],G1,B1} = C1,
    ["(",
     exprs(B1, I, Hook), nl_indent(I1),
     " <| eq(",expr(Expr,I,Hook),",",expr(T1,I,Hook),") |> ", nl_indent(I),
     "delta)"];
expr({'case',_,Expr,[C1,C2]}, I, _, Hook) ->  % only works for case out of 2
    I1 = I + 4,
    {clause,_,[T1],G1,B1} = C1,
    %{clause,_,[{var,_,_}],G2,B2} = C2,
    {clause,_,[_],G2,B2} = C2,
    ["(",
     exprs(B1, I, Hook), nl_indent(I1),
     " <| eq(",expr(Expr,I,Hook),",",expr(T1,I,Hook),") |> ", nl_indent(I),
     exprs(B2, I, Hook),
     ")"];
%expr({'case',_,Expr,Cs}, I, _, Hook) ->
%    I1 = I + 4,
%    ["case ",
%     expr(Expr, I+5, 0, Hook),
%     " of",nl_indent(I1),
%     cr_clauses(Cs, I1, Hook),
%     nl_indent(I),"end"];
expr({'receive',_,Cs}, I, _, Hook) ->
    I1 = I + 4,
    ["receive",nl_indent(I1),
     cr_clauses(Cs, I1, Hook),
     nl_indent(I),"end"];
expr({'receive',_,Cs,To,ToOpt}, I, _, Hook) ->
    I1 = I + 4,
    ["receive",nl_indent(I1),
     if						%Must special case no clauses
	 Cs /= [] -> cr_clauses(Cs, I1, Hook);
	 true -> ""
     end,
     %% Now for the timeout bit.
     nl_indent(I), "after",
     nl_indent(I1),
     expr(To, I1, 0, Hook),
     body(ToOpt, I1+4, Hook),
     nl_indent(I), "end"];
expr({'fun',_,{function,F,A}}, I, Prec, Hook) ->
    ["fun ",write(F),$/,write(A)];
expr({'fun',_,{clauses,Cs}}, I, Prec, Hook) ->
    ["fun ",
     fun_clauses(Cs, I+4, Hook),
     " end"];
expr({'fun',_,{clauses,Cs},Extra}, I, Prec, Hook) ->
    [io_lib:format("% fun-info: ~p~n", [Extra]),
     string:chars($\s, I),
     "fun ",
     fun_clauses(Cs, I+4, Hook),
     " end"];
expr({'query',_,Lc}, I, Prec, Hook) ->
    ["query ",
     expr(Lc, I+6, 0, Hook),
     " end"];
expr({call,_,{atom,_,pid},[{integer,_,Nat}]}, I, Prec, Hook) ->
    ["pid(",write(Nat),")"];
expr({call,_,{atom,_,mcrlsum},[V,{block,_,Exprs}]}, I, Prec, Hook) ->
    ["sum(",expr(V,I,Prec,Hook),": "++?Term++",",nl_indent(I+5),
     exprs(Exprs,I+5,Hook),")"];
expr({call,_,{atom,_,?conftau},[]}, I, Prec, Hook) ->
    [atom_to_list(?conftau)];
expr({call,_,{remote,_,{atom,_,?MCRLSERVER},{atom,_,Name}},Args},I,Prec,Hook) ->
    {F,P} = func_prec(),
    Nl = expr(append(Name,"_init"), I, F, Hook),
    ["hide({push_callstack,pop_callstack},\n",
          "     encap({rcallvalue,wcallvalue,rcallresult,wcallresult},\n"
          "          CallStack(empty) || ",Nl,expr_list(Args, "(", ")", indentation(Nl, I), Hook),
          ")) ||\n        Server_Buffer"|expr_list([hd(Args),{atom,0,?emptybuffer}],"(", ")",I, Hook)];
expr({call,Line,{remote,_,{atom,_,Mod},{atom,_,Fun}},Args}, I, Prec, Hook) ->
    {F,P} = func_prec(),
    Nl =
    case member({Mod,Fun,length(Args)},?See_as_Bifs) of
         true ->
           atom_to_list(Fun);
         false ->
           ?WARNING(Line,"imported function ~p~n",[{Mod,Fun,length(Args)}]),
           [expr({atom,0,Mod}, I, F, Hook),"_",expr({atom,0,Fun},0,F,Hook)]
    end,
    El = [Nl|expr_list(Args, "(", ")", indentation(Nl, I), Hook)],
    maybe_paren(P, Prec, El);
expr({call,_,Name,Args}, I, Prec, Hook) ->
    {F,P} = func_prec(),
    Nl = expr(Name, I, F, Hook),
    El = [Nl|expr_list(Args, "(", ")", indentation(Nl, I), Hook)],
    maybe_paren(P, Prec, El);
expr({'catch',_,Expr}, I, Prec, Hook) ->
    {P,R} = preop_prec('catch'),
    El = ["catch ",expr(Expr, I+6, R, Hook)],
    maybe_paren(P, Prec, El);
expr({match,_,Lhs,Rhs}, I, Prec, Hook) ->
    {L,P,R} = inop_prec('='),
    Pl = expr(Lhs, I, L, Hook),
    El = [Pl," = ",expr(Rhs, indentation(Pl, I)+3, R, Hook)],
    maybe_paren(P, Prec, El);
expr({op,_,Op,Arg}, I, Prec, Hook) ->
    {P,R} = preop_prec(Op),
    Ol = flatten(format("~s ", [Op])),
    El = [Ol,expr(Arg, I+length(Ol), R, Hook)],
    maybe_paren(P, Prec, El);
expr({op,Line,Op,Larg,Rarg}, I, Prec, Hook) ->
    {L,P,R} = inop_prec(Op),
    Ll = expr(Larg, I, L, Hook),
    case lists:keysearch(Op,1,?BIN_OPERATORS) of
         {value,{_,Operator}} ->
           [Operator,"(",Ll,",",expr(Rarg,I,Prec,Hook),")"];
         false ->
           ?WARNING(Line,"unknown operator ~p~n",[Op]),
           [atom_to_list(Op),"(",Ll,",",expr(Rarg,I,Prec,Hook),")"]
    end;
%% Special expressions which are not really legal everywhere.
expr({remote,_,M,F}, I, Prec, Hook) ->
    {L,P,R} = inop_prec(':'),
    Ml = expr(M, I, L, Hook),
    El = [Ml,"_",expr(F, indentation(Ml, I)+1, R, Hook)],
    maybe_paren(P, Prec, El);
%% BIT SYNTAX:
expr({bin,_,Fs}, I, Prec, Hook) ->
    bit_grp(Fs,I,Prec,Hook);
%% Special case for straight values.
expr({value,_,Val}, _, _,_) ->
    write(Val);
%% Now do the hook.
expr(Other, Indentation, Precedence, none) ->
    format("INVALID-FORM:~w:",[Other]);
expr(Expr, Indentation, Precedence, {Mod,Func,Eas}) when Mod /= 'fun' ->
    apply(Mod, Func, [Expr,Indentation,Precedence,{Mod,Func,Eas}|Eas]);
expr(Expr, Indentation, Precedence, Func) ->
    Func(Expr, Indentation, Precedence, Func).

%% BITS:
bit_grp(Fs,I,Prec,Hook) ->
    ["<<", bit_elems(Fs,I,Prec,Hook),">>"].

bit_elems([E], I, Prec, Hook) ->
    [ bit_elem(E, I, Prec, Hook) ];
bit_elems([E1,E2],I,Prec,Hook) ->
    [ bit_elem(E1,I,Prec,Hook), separator(E2), bit_elem(E2,I,Prec,Hook) ];
bit_elems([E|Es],I,Prec,Hook) ->
    [ bit_elem(E,I,Prec,Hook), ",", bit_elems(Es,I,Prec,Hook) ];
bit_elems([],I,Prec,Hook) ->
    [].

bit_elem({bin_tail,_,Var}, I, Prec, Hook) ->
    expr(Var,I,Prec,Hook);
bit_elem({bin,_,Fs}, I, Prec, Hook) ->
    bit_grp(Fs,I,Prec,Hook);
bit_elem({bin_element,_,Expr,Sz,Types}, I, Prec, Hook) ->
    Expr1 = 
	if Sz =/= default ->
		{remote, 0, Expr, Sz};
	   true ->
		Expr
	end,
    Expr2 =
	if Types =/= default ->
		{op, 0, '/', Expr1, bit_elem_types(lists:reverse(Types))};
	   true ->
		Expr1
	end,
    expr(Expr2,I,Prec,Hook).

bit_elem_types([T]) ->
    case T of
	{A, B} ->
	    {remote, 0,
	     erl_parse:abstract(A),
	     erl_parse:abstract(B)};
	_ ->
	    erl_parse:abstract(T)
    end;    
bit_elem_types([T | Rest]) ->
    {op, 0, '-', bit_elem_types(Rest), bit_elem_types([T])}.

separator(Elem) ->
    case element(1,Elem) of
        bin_tail -> "|";
        bin  -> ",";
        bin_element -> ","
    end.

%%% end of BITS

record_fields(Fs, I, Hook) ->
    I1 = I + 1,
    ["{",
     separated_list(fun record_field/3, "," ++ nl_indent(I1), I1, Hook, Fs),
     "}"].

record_field({record_field,_,F,Val}, I, Hook) ->
    {L,P,R} = inop_prec('='),
    Fl = expr(F, I, L, Hook),
    [Fl," = ",expr(Val, indentation(Fl, I)+3, R, Hook)];
record_field({record_field,_,F}, I, Hook) ->
    expr(F, I, Hook).

tail({cons,_,H,T}, I, Hook) ->
    [",cons(", expr(H, I, 0, Hook),tail(T, I, Hook),")"];
tail({nil,_}, _, _) -> ",nil";
%tail(Other, I, Hook) ->
%    io:format("ERROR in ~p~n",[?MODULE]),
%    [",cons(", expr(Other, I, 0, Hook),",nil)"].
tail(Other, I, Hook) ->
    %io:format("ERROR in ~p (line ~p) ~p~n",[?MODULE,element(2,Other),Other]),
    [",",expr(Other, I, 0, Hook)]. 

expr_list(Es, First, Last, I, Hook) ->
    [First,
     separated_list(fun expr/3, ",", I+length(First), Hook, Es),
     Last].

arg_list(Es, I, Hook) ->
    ["(",
     separated_list(fun(E,I1,H) -> [expr(E,I1,H),":Term"] end, ",", I, Hook, Es),
     ")"].

tuple_list([], First, Last, I, Hook) ->
    ["{}"];
tuple_list([E], First, Last, I, Hook) ->
    [Last,expr(E,I+2,Hook),")"];
tuple_list([E|Es], First, Last, I, Hook) ->
    [First, expr(E,I+2,Hook), ", ",tuple_list(Es,First,Last,I+2,Hook),")"].


%% if_clauses(Clauses, Indentation, Hook) -> [Char].
%%  Print 'if' clauses.

if_clauses(Cs, I, Hook) -> clauses(fun if_clause/3, I, Hook, Cs).

if_clause({clause,_,[],G,B}, I, Hook) ->
    [if
	 G /= [] -> guard_no_when(G, I+2, Hook);
	 true -> write(true)
     end,
     body(B, I+4, Hook)].

%% cr_clauses(Clauses, Indentation, Hook) -> [Char].
%%  Print 'case'/'receive' clauses.

cr_clauses(Cs, I, Hook) -> clauses(fun cr_clause/3, I, Hook, Cs).

cr_clause({clause,_,[T],G,B}, I, Hook) ->
    [expr(T, I, 0, Hook),
     guard(G, I, Hook),
     body(B, I+4, Hook)].

%% fun_clauses(Clauses, Indentation, Hook) -> [Char].
%%  Print 'fun' clauses.

fun_clauses(Cs, I, Hook) -> clauses(fun fun_clause/3, I, Hook, Cs).

fun_clause({clause,_,A,G,B}, I, Hook) ->
    [expr_list(A, "(", ")", I, Hook),
     guard(G, I, Hook),
     body(B, I+4, Hook)].

%% clauses(Type, Identation, Hook) -> [Char].
%%  Generic clause printing function.

clauses(Type, I, Hook, Cs) ->
    separated_list(Type,  nl_indent(I), I, Hook, Cs).

%% separated_list(Fun, Sep, Indentation, Hook, Es) -> [Char].
%%  Generic function for printing a list of things with separators
%%  between them. We can handle the empty case.

separated_list(Fun, S, I, Hook, [E1|Es]) ->
    [Fun(E1, I, Hook)|lists:map( fun (E) -> [S,Fun(E, I, Hook)] end, Es)];
separated_list(Fun, S, I, Hook, []) -> "".

%% lc_quals(Qualifiers, Indentation, Hook)
%% List comprehension qualifiers

lc_quals(Qs, I, Hook) ->
    separated_list(fun lc_qual/3, "," ++ nl_indent(I), I, Hook, Qs).

lc_qual({generate,_,Pat,E}, I, Hook) ->
    Pl = expr(Pat, I, 0, Hook),
    [Pl," <- ",expr(E, indentation(Pl, I)+4, 0, Hook)];
lc_qual(Q, I, Hook) ->
    expr(Q, I, 0, Hook).

%%
%% Utilities
%%

maybe_paren(P, Prec, Expr) when P < Prec -> [$(,Expr,$)];
maybe_paren(P, Prec, Expr) -> Expr.

nl_indent(I) when I >= 0 -> [$\n|string:chars($\s, I)];
nl_indent(I) -> " ".

to_integer(0) ->
  "0";
to_integer(N) when N>0 ->
  "s("++to_integer(N-1)++")".

append(Atom,String) ->
  {atom,0,list_to_atom(atom_to_list(Atom)++String)}.
