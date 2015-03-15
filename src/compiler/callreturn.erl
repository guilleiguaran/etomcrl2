%
% add wcallresult to end of recursion 
%
%% <p> Thomas Arts. May 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(callreturn).

-export([forms/1, file/1,file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

-define(RETURN(Value),{call,0,{atom,0,wcallresult},[Value]}).

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
  Procs =
    [{F,A} || {function,_,F,A,_}<-AbsForms ],
  map(fun(AbsForm) ->
             replace(Procs,AbsForm)
      end,AbsForms).

%+type file(filename()) -> [abs_form()].
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

% function should recursively call one of the funs in Locals
%
replace(Locals,{function,Line,Name,Arity,Clauses}) ->
  ?DEBUG("~p function ~p/~p~n~p~n",[?MODULE,Name,Arity,Clauses]),
  {function,Line,Name,Arity,
   map(fun({clause,L,Pats,Guards,Body}) ->
            {clause,L,Pats,Guards,exprs(Locals,true,Body)}
       end, Clauses)};
replace(Locals,AbsForm) ->
  AbsForm.


%   recursive calls to fun in Locals remain
%   replacing other call f(...) by wcallresult(?MCRLSelf,f(...))
exprs(Locals,Last,{block,Line,Es}) ->
  [{block,Line,exprs(Locals,Last,Es)}];
exprs(Locals,Last,[E]) ->
  case recursion(Locals,Last,E) of
       Exprs when list(Exprs) ->
         Exprs;
       Expr ->
         [Expr] % hack 
  end;
exprs(Locals,Last,[E|Es]) ->
  [recursion(Locals,false,E)|exprs(Locals,Last,Es)].

recursion(Locals,Last,Expr) ->
  case Expr of
       Exprs when list(Exprs) ->
         map(fun(E) -> recursion(Locals,Last,E) end, Exprs);
       {clause,Line,Pats,Guards,E} ->
         {clause,Line,Pats,Guards,exprs(Locals,Last,E)};
       {tuple,Line,Es} ->
         NExpr = {tuple,Line,exprs(Locals,false,Es)},
         case Last of
              true -> 
                ?RETURN(NExpr);
              false ->
                NExpr
         end;
       {cons,Line,Head,Tail} ->
         NExpr = 
          {cons,Line,recursion(Locals,false,Head),recursion(Locals,false,Tail)},
         case Last of
              true -> 
                ?RETURN(NExpr);
              false ->
                NExpr
         end;
       {match,Line,E1,E2} ->
         {match,Line,E1,recursion(Locals,false,E2)};
       {'case',Line,E,Clauses} ->
         {'case',Line,E,recursion(Locals,Last,Clauses)};
       {'if',Line,Clauses} ->
         {'if',Line,recursion(Locals,Last,Clauses)};
       {call,Line,{atom,_,Fun},Args} ->
         case member({Fun,length(Args)},Locals) of
              true -> % local side effect function
                {call,Line,{atom,Line,Fun},Args};
              false -> % not in the side effect locals 
                case Last of
                     true ->
                       case {Fun,Args} of
			   %% we could have gen_server_reply but then
			   %% it only returns ok 
                            {gen_server_replied,[Self,Value,From]} -> 
                              [Expr,?RETURN(Value)];
			   %% This is an action, and we cannot have actions as arguments
                            _ ->
                              ?RETURN(Expr)
                       end;
                     false ->
                       Expr
                end
         end;
       {op,Line,Op,E} ->
         {op,Line,Op,recursion(Locals,false,E)};
       {op,Line,Op,E1,E2} ->
         {op,Line,Op,recursion(Locals,false,E1),recursion(Locals,false,E2)};

% list comprehensions should also be considered, like records
       {block,Line,Exprs} ->
         {block,Line,map(fun(E) -> recursion(Locals,Last,E) end, Exprs)};

       _ ->
         case Last of
              true -> 
                ?RETURN(Expr);
              false ->
                Expr
         end
  end.

