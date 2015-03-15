%% @doc
%% <p>replace function names f by MODULE:f on sourcecode level (abstract forms)</p>
%% <p>Thomas Arts. March 2001</p>
%% <p>Revised and commented by Juanjo
%% Sanchez Penas and Clara Benac Earle.  October 2003</p> 


%% PRECOND:
%% 
%% A list of Erlang abstract forms.
%% TODO: list comprehensions, records and funs. 
%%
%% INVARIANTS:
%% 
%% Erlang semantics are preserved.
%%
%% POSTCOND:
%%
%% All function names f are replaced by MODULE:f on sourcecode level
%% (abstract forms).  
%% The import attribute, -import(...), is removed from the abstract
%% forms.

%% @end
 
-module(etoe_noimports).

-export([forms/1, forms/2, file/1,file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%+type forms([abs_form()]) -> [abs_form()].
%

%% When the module is called with the forms/1 we are not giving any
%% exception so, for instance, the function member is translated as
%% lists:member as well. Only when changing the syntax to mCRL we will
%% add the BIFs and operations over lists from the module where they
%% are defined as mCRL operations.

forms(AbsForms) ->
  forms(AbsForms,[]).

% exceptions occur as BIFs in code, e.g. lists:member -> member
%
forms(AbsForms,Exceptions) ->
  Imports =
    module(AbsForms,dict:new()),
  foldr(fun(AbsForm,NewAbsForms) ->
             replace(Imports,AbsForm,Exceptions)++NewAbsForms
        end,[],AbsForms).

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

%+type module([abs_form()]) -> {module :: atom(),dictionary(fun(),fun())]}.
%

%% module puts all the functions in the import attribute in the
%% dictionary.
module([],Dict) ->
  Dict;
module([{attribute,_,import,{Mod,Funs}}|AbsForms],Dict) ->
  module(AbsForms,
         foldl(fun({F,A},D) ->
                  dict:store({F,A},{Mod,F,A},D)
               end,Dict,Funs));
module([_|AbsForms],Dict) ->
  module(AbsForms,Dict).

replace(Imports,{function,Line,Name,Arity,Clauses},Exceptions) ->
  [{function,Line,Name,Arity,newname(Imports,Clauses,Exceptions)}];
replace(Imports,{attribute,_,import,_},Exceptions) ->
  [];
replace(Imports,AbsForm,Exceptions) ->
  [AbsForm].

% newname/3: parsing an expression, 
%   replacing a call f(...) that is imported by  MODULE:f(...)
newname(Imps,Expr,Exc) ->
  case Expr of
       Exprs when list(Exprs) ->
         map(fun(E) -> newname(Imps,E,Exc) end,Exprs);
       {clause,Line,Pats,Guards,E} ->
         {clause,Line,Pats,newname(Imps,Guards,Exc),newname(Imps,E,Exc)};
       {tuple,Line,Es} ->
         {tuple,Line,newname(Imps,Es,Exc)};
       {cons,Line,Head,Tail} ->
         {cons,Line,newname(Imps,Head,Exc),newname(Imps,Tail,Exc)};
       {match,Line,E1,E2} ->

         {match,Line,E1,newname(Imps,E2,Exc)};
       {'case',Line,E,Clauses} ->
         {'case',Line,newname(Imps,E,Exc),newname(Imps,Clauses,Exc)};
       {call,Line,{atom,_,Fun},Args} ->
         case dict:find({Fun,length(Args)},Imps) of
              {ok,{M,F,A}} -> % the fucntion was in -import
                case member({M,F,A},Exc) of
                     true ->
                       {call,Line,{atom,Line,Fun},newname(Imps,Args,Exc)};
                     false ->
                       {call,Line,{remote,Line,{atom,Line,M},{atom,Line,F}},
                               newname(Imps,Args,Exc)} 
		       %% remote: call to a function which is declared
		       %% in another module, e.g., lists:member. The
		       %% ":" is substituted for "remote" in the
		       %% abstract form.
                end;
              error ->
                {call,Line,{atom,Line,Fun},newname(Imps,Args,Exc)}
         end;
       {call,Line,{remote,_,{atom,_,Mod},{atom,_,Fun}},Args} ->
         case member({Mod,Fun,length(Args)},Exc) of
              true ->
                {call,Line,{atom,Line,Fun},newname(Imps,Args,Exc)};
              false ->
                {call,Line,{remote,Line,{atom,Line,Mod},{atom,Line,Fun}},
                                                newname(Imps,Args,Exc)}
         end;
       {call,Line,Fun,Args} ->
         {call,Line,Fun,newname(Imps,Args,Exc)};
       {op,Line,Op,E} ->
         {op,Line,Op,newname(Imps,E,Exc)};
       {op,Line,Op,E1,E2} ->
         {op,Line,Op,newname(Imps,E1,Exc),newname(Imps,E2,Exc)};
       {record,Line,Rec,Name,Fields} ->
         {record,Line,newname(Imps,Rec,Exc),Name,newname(Imps,Fields,Exc)};
       {record_field,Line,Field,E} ->
         {record_field,Line,newname(Imps,Field,Exc),newname(Imps,E,Exc)};

% list comprehensions should also be considered, like records and funs

       _ ->
         Expr
  end.


