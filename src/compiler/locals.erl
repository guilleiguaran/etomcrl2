%% Could we move this to etoe? No, because it causes problem with the remote functions

%% Example:

%% -module M0
%% f(..) ->
%%   M1:g(...)
%%   ...
%%   f(..)

%% would be translated to :
%% M0_f(..) ->
%%   M1_g(...)
%%   ...
%%   M0_f(..) 

%% but this would not compile. We could fix it using an extra import
%% (-import(M1,[M1_g,...]), but we would still problems with lists,
%% for instance. What we would like is the module system implemented
%% in the mucRL toolset. For now we would like this transformation as
%% late as possible, so that we can skip it when there is a module
%% system implemented in the mucRL toolset.
%%
%% replace function names f by MODULE_f on sourcecode level (abstract forms)
%%
%% <p>Thomas Arts. March 2001</p>
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>


-module(locals).

-export([forms/1, file/1, file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
    ModName = atom_to_list(get_module_name(AbsForms))++"_",
    %% Locals is the list of functions defined in the module with the
    %% new name as third element of the tuple. Names of the functions
    %% that are not locally defined are not going to be changed
    Locals =
	[{F,A,name(ModName,F)} || {function,_,F,A,_}<-AbsForms ],
    map(fun(AbsForm) ->
		replace(Locals,AbsForm)
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

get_module_name([]) ->
  exit("missing -module attribute");
get_module_name([{attribute,_,module,Mod}|_]) ->
  Mod;
get_module_name([_|AbsForms]) ->
  get_module_name(AbsForms).

replace(Locals,{function,Line,Name,Arity,Clauses}) ->
    %% newfun changes the name of the function in the function
    %% definition and in the export attribute
    %%
    %% newname changes the name of all the local functions in the clauses
    {function,Line,newfun(Locals,Name,Arity),Arity,newname(Locals,Clauses)};
replace(Locals,{attribute,Line,export,Exports}) ->
    {attribute,Line,export,
     map(fun({F,A}) ->
		 {newfun(Locals,F,A),A}
	 end,Exports)};
replace(Locals,AbsForm) ->
    AbsForm.

% newname/3: parsing an expression, 
%   replacing a local call f(...) by  MODULE_f(...)
newname(Locals,Expr) ->
  case Expr of
       Exprs when list(Exprs) ->
         map(fun(E) -> newname(Locals,E) end,Exprs);
       {clause,Line,Pats,Guards,E} ->
         {clause,Line,Pats,newname(Locals,Guards),newname(Locals,E)};
       {tuple,Line,Es} ->
         {tuple,Line,newname(Locals,Es)};
       {cons,Line,Head,Tail} ->
         {cons,Line,newname(Locals,Head),newname(Locals,Tail)};
       {match,Line,E1,E2} ->
         {match,Line,E1,newname(Locals,E2)};
       {'case',Line,E,Clauses} ->
         {'case',Line,newname(Locals,E),newname(Locals,Clauses)};
       {call,Line,{atom,_,Fun},Args} ->
         case find(Locals,Fun,length(Args)) of 
              {ok,NewF} -> % NewF is the new name for the function,
                           % with the module name included
                {call,Line,{atom,Line,NewF},newname(Locals,Args)};
              error ->
                {call,Line,{atom,Line,Fun},newname(Locals,Args)}
         end;
       {call,Line,Fun,Args} ->
         {call,Line,Fun,newname(Locals,Args)};
       {op,Line,Op,E} ->
         {op,Line,Op,newname(Locals,E)};
       {op,Line,Op,E1,E2} ->
         {op,Line,Op,newname(Locals,E1),newname(Locals,E2)};
       {record,Line,E,Name,Fields} ->
         {record,Line,newname(Locals,E),Name,newname(Locals,Fields)};
       {record_field,Line,Name,E} ->
         {record_field,Line,Name,newname(Locals,E)};

% list comprehensions should also be considered, like records

       _ ->
         Expr
  end.

newfun(Locals,F,A) ->
  case find(Locals,F,A) of
       error ->
         exit({F,A,"function not defined"});
       {ok,NewF} ->
         NewF
  end.

%% Searches for F,A in the {F,A,FunctionName} list, and returns {ok,
%% FunctionName} or error if it is not found

find([],F,A) ->
  error;
find([{F,A,NewF}|_],F,A) ->
  {ok,NewF};
find([_|Locals],F,A) ->
  find(Locals,F,A).


%% name (string() , atom()) -> atom()
name(ModName,F) ->
  list_to_atom(ModName++atom_to_list(F)).

