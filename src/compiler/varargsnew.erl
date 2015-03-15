%%
% replace all patterns in f(P1,...,PN) -> ...
%  by variable arguments and matching, i.e.
%     f(A1,...,An) ->
%       P1 = A1, ..., PN = An,...
%
% added later
%
% replace multiple clauses by one nested 'if' statement
%
% Thomas Arts
% May 2001

-module(varargs).

-export([forms/1,form/1,file/1,file/2]).

-include("etomcrl.hrl").

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
  map(fun(AbsForm) -> form(AbsForm) end,AbsForms).

%+type form(abs_form()) -> abs_form().
%
form({function,Line,handle_call,3,Clauses}) ->
  {function,Line,handle_call,3,Clauses};
form({function,Line,handle_cast,2,Clauses}) ->
  {function,Line,handle_cast,2,Clauses};
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

%%% modified erl_id_trans

% Modification to original: clause gets vars instead of patterns
%
clauses([]) -> 
  [];
clauses([C0|Cs]) ->
  Head = varargclause(C0),
  [{clause,0,Head,[],
    foldr(fun(C,Clause) ->
             {Line,Expr,Body} = newclause(C,Head),
             case {Expr,Clause} of
                  {{atom,_,true},_} ->
                    Body++Clause;
                  {_,[]} ->
                    [{'case',Line,Expr,
                     [{clause,Line,[{atom,Line,true}],[],Body}]}];
                  _ ->
                    [{'case',Line,Expr,
                     [{clause,Line,[{atom,Line,true}],[],Body},
                      {clause,Line,[{atom,Line,false}],[],Clause}]}]
             end
          end,[],[C0|Cs])}].

gtoexpr([]) ->
  {atom,0,true};
gtoexpr([Guard|Guards]) ->
  foldl(fun(G,Expr) ->
           {op,0,'and',Expr,G}
        end,Guard,Guards).

varargclause({clause,Line,H0,[],B0}) ->
  {H1,N} =
    foldr(fun(P,{Ps,Free}) ->
           case P of
                {var,_,X} when X =/= '_'->
                  {[P|Ps],Free};
                _ ->
                  {[{var,Line,list_to_atom("MCRLArg"++
                             integer_to_list(Free))}|Ps],Free+1}
           end
        end,{[],1},H0),
  H1.
 
newclause({clause,Line,H0,[],B0},Head) ->
  {Bindings,Assertions} = pattern:patmatch(H0,Head),
  ?DEBUG("bindings: ~p~nassertions ~p~n",[Bindings,Assertions]),
  {Line,gtoexpr(Assertions),exprs(B0,Bindings)};
newclause({clause,Line,H0,_,B0},Head) ->
  exit("Guards not allowed (line "++integer_to_list(Line)++")").

%newclause({clause,Line,H0,[],B0},Head) ->
%  {Bindings,Assertions} = pattern:patmatch(H0,Head),
%  ?DEBUG("bindings: ~p~nassertions ~p~n",[Bindings,Assertions]),
%  {clause,Line,[],
%     Assertions,exprs(B0,Bindings)};
%newclause({clause,Line,H0,_,B0},Head) ->
%  exit("Guards not allowed (line "++integer_to_list(Line)++")").

%zip([],[]) ->
%  [];
%zip([X|Xs],[Y|Ys]) ->
%  [{X,Y}|zip(Xs,Ys)].

clause({clause,Line,P0,G0,B0},Bindings) ->
    B1 = exprs(B0,Bindings),
    {clause,Line,P0,G0,B1}.

exprs(Es,Bindings) ->
    map(fun(E) -> expr(E,Bindings) end,Es).

expr(Expr,Bindings) ->
  case Expr of
       {var,Line,V} ->
         case lists:keysearch(V,1,Bindings) of
              {value,{_,E1}} ->
                E1;
              false ->
                {var,Line,V}
         end;
       {cons,Line,H0,T0} ->
         H1 = expr(H0,Bindings),
         T1 = expr(T0,Bindings),
         {cons,Line,H1,T1};
       {lc,Line,E0,Qs0} ->
         Qs1 = lc_quals(Qs0,Bindings),
         E1 = expr(E0,Bindings),
         {lc,Line,E1,Qs1};
       {tuple,Line,Es0} ->
         Es1 = exprs(Es0,Bindings),
         {tuple,Line,Es1};
       {record_index,Line,Name,Field0} ->
         Field1 = expr(Field0,Bindings),
         {record_index,Line,Name,Field1};
       {record,Line,Name,Inits0} ->
         Inits1 = exprs(Inits0,Bindings),
         {record,Line,Name,Inits1};
       {record_field,Line,Rec0,Name,Field0} ->
         Rec1 = expr(Rec0,Bindings),
         Field1 = expr(Field0,Bindings),
         {record_field,Line,Rec1,Name,Field1};
       {record,Line,Rec0,Name,Upds0} ->
         Rec1 = expr(Rec0,Bindings),
         Upds1 = exprs(Upds0,Bindings),
         {record,Line,Rec1,Name,Upds1};
       {record_field,Line,Rec0,Field0} ->
         Rec1 = expr(Rec0,Bindings),
         Field1 = expr(Field0,Bindings),
         {record_field,Line,Rec1,Field1};
       {block,Line,Es0} ->
         Es1 = exprs(Es0,Bindings),
         {block,Line,Es1};
       {'if',Line,Cs0} ->
         Cs1 = map(fun(C) -> clause(C,Bindings) end, Cs0),
         {'if',Line,Cs1};
       {'case',Line,E0,Cs0} ->
         E1 = expr(E0,Bindings),
         Cs1 = map(fun(C) -> clause(C,Bindings) end, Cs0),
         {'case',Line,E1,Cs1};
       {'receive',Line,Cs0} ->
         Cs1 = map(fun(C) -> clause(C,Bindings) end, Cs0),
         {'receive',Line,Cs1};
       {'receive',Line,Cs0,To0,ToEs0} ->
         To1 = expr(To0,Bindings),
         ToEs1 = exprs(ToEs0,Bindings),
         Cs1 = map(fun(C) -> clause(C,Bindings) end, Cs0),
         {'receive',Line,Cs1,To1,ToEs1};
       {'fun',Line,Body} ->
         case Body of
	      {clauses,Cs0} ->
                Cs1 = map(fun(C) -> clause(C,Bindings) end, Cs0),
	        {'fun',Line,{clauses,Cs1}};
	      {function,F,A} -> 
	        {'fun',Line,{function,F,A}};
	      {function,M,F,A} ->	%This is an error in lint!
	        {'fun',Line,{function,M,F,A}}
         end;


       {call,Line,{atom,L1,F},As0} ->
         As1 = exprs(As0,Bindings),
         {call,Line,{atom,L1,F},As1};
       {call,Line,{remote,L1,{atom,L2,M},{atom,L3,F}},As0} ->
         As1 = exprs(As0,Bindings),
         {call,Line,{remote,L1,{atom,L2,M},{atom,L3,F}},As1};
       {call,Line,F0,As0} ->
         %F1 = expr(F0,Bindings),
         As1 = exprs(As0,Bindings),
         {call,Line,F0,As1};
       {'catch',Line,E0} ->
         E1 = expr(E0,Bindings),
         {'catch',Line,E1};
       {'query', Line, E0} ->
         %% lc expression
         E1 = expr(E0,Bindings),
         {'query', Line, E1};
       {op,Line,Op,A0} ->
         A1 = expr(A0,Bindings),
         {op,Line,Op,A1};
       {op,Line,Op,L0,R0} ->
         L1 = expr(L0,Bindings),
         R1 = expr(R0,Bindings),
         {op,Line,Op,L1,R1};
       _ ->
         Expr
  end.


lc_quals([{generate,Line,P0,E0}|Qs],Bindings) ->
    E1 = expr(E0,Bindings),
    P1 = expr(P0,Bindings),
    Qs1 = lc_quals(Qs,Bindings),
    [{generate,Line,P1,E1}|Qs1];
lc_quals([E0|Qs],Bindings) ->
    E1 = expr(E0,Bindings),
    Qs1 = lc_quals(Qs,Bindings),
    [E1|Qs1];
lc_quals([],Bindings) ->
    [].

