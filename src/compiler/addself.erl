%
% add extra argument "Self" to functions and calls to these functions
%
%% <p>Thomas Arts. March 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(addself).

-export([forms/1, file/1,file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
    Procs =  % A tuple {Function,Arity} for all the functions in AbsForms
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

replace(Locals,{function,Line,Name,Arity,Clauses}) ->
    {function,Line,Name,Arity+1,
     map(fun({clause,L,Pats,Guards,Body}) ->
		 {clause,L,[{var,L,?MCRLSelf}|Pats],Guards,addarg(Locals,Body)}
	 end, Clauses)};
replace(Locals,AbsForm) ->
    AbsForm.

% addarg/2: parsing an expression, 
%   replacing a call f(...) by  f(Self,...)
addarg(Locals,Expr) ->
  case Expr of
       Exprs when list(Exprs) ->
         map(fun(E) -> addarg(Locals,E) end,Exprs);
       {clause,Line,Pats,Guards,E} ->
         {clause,Line,Pats,addarg(Locals,Guards),addarg(Locals,E)};
       {tuple,Line,Es} ->
         {tuple,Line,addarg(Locals,Es)};
       {cons,Line,Head,Tail} ->
         {cons,Line,addarg(Locals,Head),addarg(Locals,Tail)};
       {match,Line,E1,E2} ->
         {match,Line,E1,addarg(Locals,E2)};
       {'case',Line,E,Clauses} ->
         {'case',Line,addarg(Locals,E),addarg(Locals,Clauses)};
       {'if',Line,Clauses} ->
         {'if',Line,addarg(Locals,Clauses)};
       {call,Line,{atom,_,Fun},Args} -> % Call to Fun(Args)
         case member({Fun,length(Args)},Locals) of 
	     %% If the function is in Locals, it is a function with
	     %% side effects
              true ->
		 {call,Line,{atom,Line,Fun},
		  addarg(Locals,[{var,Line,?MCRLSelf}|Args])};
              false ->
                {call,Line,{atom,Line,Fun},addarg(Locals,Args)}
         end;
       {call,Line,Fun,Args} ->
         {call,Line,Fun,addarg(Locals,Args)};
       {op,Line,Op,E} ->
         {op,Line,Op,addarg(Locals,E)};
       {op,Line,Op,E1,E2} ->
         {op,Line,Op,addarg(Locals,E1),addarg(Locals,E2)};

% list comprehensions should also be considered, like records

       _ ->
         Expr
  end.

