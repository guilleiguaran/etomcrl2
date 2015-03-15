%
% add extra tau step to recursive calls of function without progress
%
% should only be called on "proc" function calls
%
%% <p> Thomas Arts. June 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(conftau).

-export([forms/1, file/1,file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
  map(fun(AbsForm) ->
             replace(AbsForm)
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

replace({function,Line,Name,Arity,Clauses}) ->
  {function,Line,Name,Arity,
   map(fun({clause,L,Pats,Guards,Body}) ->
          {clause,L,Pats,Guards,addtau({Name,Arity},Body)}
       end, Clauses)};
replace(AbsForm) ->
  AbsForm.

% addtau/2: parsing an expression, 
%   replacing a recursive call f(...) by  tau.f(...) if not preceeded by action
%%
%% Recursion: {Name, Arity} for the analysed function
%% Expr: Body of the clause

addtau(Recursion,Expr) ->
  case Expr of
       [] -> 
         [];
       [E|Es] ->
         [addtau(Recursion,E)|Es];  % if first one no recursion, then action
       {clause,Line,Pats,Guards,E} ->
         {clause,Line,Pats,Guards,addtau(Recursion,E)};
       {match,Line,E1,E2} ->
         {match,Line,E1,addtau(Recursion,E2)};
       {'case',Line,E,Clauses} ->
         {'case',Line,E,map(fun(C) -> addtau(Recursion,C) end,Clauses)};
       {'if',Line,Clauses} ->
         {'if',Line,map(fun(C) -> addtau(Recursion,C) end,Clauses)};
       {call,Line,{atom,_,Fun},Args} ->
	  case {Fun,length(Args)}==Recursion of % If it's a recursive call
              true ->
		  %% Introduces conftau() call in a block. A block
		  %% makes one expression (statement) from several
		  %% expressions. In this case it is just for the
		  %% function call and the conftau
		  {block,Line,[{call,Line,{atom,0,?conftau},[]},Expr]}; 
	      false ->
		  {call,Line,{atom,Line,Fun},
		   map(fun(A) -> addtau(Recursion,A) end,Args)}
	  end;
       {call,Line,Fun,Args} ->
         {call,Line,Fun,map(fun(A) -> addtau(Recursion,A) end,Args)};
       {op,Line,Op,E} ->
         {op,Line,Op,addtau(Recursion,E)};
       {op,Line,Op,E1,E2} ->
         {op,Line,Op,addtau(Recursion,E1),addtau(Recursion,E2)};
       {block,Line,Es} ->
         {block,Line,addtau(Recursion,Es)};
       _ ->
         Expr
  end.

