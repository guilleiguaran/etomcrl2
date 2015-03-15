%% @doc
%% <p>Thomas Arts. May 2001</p> 
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac
%% Earle.  October 2003</p> TODO: Should be completed with forms, file
%% and ...  
%% This modules looks like an auxiliar module which is only 
%% used by other modules, therefore forms, etc
%% This module is only used now for the sef part

%% @end


-module(pattern).

-export([patmatch/2,match/2,vars/1]).

-import(lists,[map/2,foldl/3]).

-define(tuplelength(E),{call,0,{atom,0,size},[E]}).

% Function used only for testing
match(Pattern,Expr) ->
  {ok,Tokens,_} =
    erl_scan:string(Pattern++","++Expr++"."),
  {ok,[AbsPat,AbsExpr]} =
    erl_parse:parse_exprs(Tokens),
  {Bindings,Assertions} = 
    pattern(AbsPat,fun(E) -> E end,{[],[]}),
  map(fun(F) -> 
         io:format("~s~n",[erl_pp:expr(F(AbsExpr))])
      end, Assertions),
  map(fun({V,F}) -> 
         io:format("~p = ~s~n",[V,erl_pp:expr(F(AbsExpr))])
      end, Bindings),
  patmatch(AbsPat,AbsExpr).


% Main function called from the other modules

patmatch([],[]) ->
  {[],[]};
patmatch([AbsPat|AbsPats],[AbsExpr|AbsExprs]) ->
  {Bindings1,Assertions1} =
    patmatch(AbsPat,AbsExpr),
  {Bindings2,Assertions2} =
    patmatch(AbsPats,AbsExprs),
  {Bindings1++Bindings2,Assertions1++Assertions2};

patmatch(AbsPat,AbsExpr) ->
    {Bindings,Assertions} = % {{var(),fun()},fun()}

%% Bindings is a tuple where the first argument is a variable and the
%% second is a function that does the pattern matching for the
%% variable. For instance, if the variable is a list it would return
%% the calls to the function hd() and tl()

%% Assertions is a list of functions of the shape: 
%% fun (E) -> EFun1(EFun2(...EfunN((E)))) == Expr 
%% where EFun() is either the identity, hd(list), tl(lidt),
%% size(tuple) or element(N,tuple). Records are not implemented.

%% Note: when AbsPat is either a variable or a list of variables or a
%% tree of variables, then no Assertions are created (in the current
%% implementation).

	pattern(AbsPat,fun(E) -> E end,{[],[]}), 
    {map(fun({V,F}) -> {V,F(AbsExpr)} end,Bindings), 
     map(fun(F) -> F(AbsExpr) end,Assertions)}.

%% @spec pattern( absform(), fun(), {[{var(),fun()}],[fun()]}) -> 
%%                                          {[{var(),fun()}],[fun()]}
%%
%% @doc
%%
%%  Receives an expression and a function that modifies the expression
%%  on the right-hand side of the match, and a tuple with as first
%%  element the list of bindings as the second the list of assertions.
%%
%% Returns the new bindings and assertions. 
%%
%% This is used because in mCRL we don't have pattern matching

pattern(Expr,EFun,{Bindings,Assert}) -> % First time this is called
                                        % with the identity function
  case Expr of
       {var,Line,'_'} ->
         {Bindings,Assert};
       {var,Line,V} ->
         add(V,EFun,Bindings,Assert); % Adds {V, EFun} to Bindings

       {cons,Line,H0,T0} ->
	  pattern(T0,  
		  %% In the case of a List, we need to compute first
		  %% the pattern for the head, passing hd() as the
		  %% function that is going to modify the rigth-hand
		  %% side of the pattern matching. This means that we
		  %% want to calculate the bindings and assertions for
		  %% the pattern matching between H0 and the head of
		  %% the rigth-hand side

		  %% The same idea holds for the pattern matching of
		  %% T0 with the tl() of the rigth-hand side
		  fun(E) -> {call,0,{atom,0,tl},[EFun(E)]} end,
		  pattern(H0,
			  fun(E) -> {call,0,{atom,0,hd},[EFun(E)]} end,
			  {Bindings,Assert})
		 );

      {tuple,Line,Ps0} ->
	  {NB,NA} = 
	      %% If the left-hand side of the pattern matching is a
	      %% tuple, we need to add the following assertion:
	      %% length(Ps0) == size of the rigth-hand side. size()
	      %% -introduced by ?tuplelength- is a function
	      %% implemented in mCRL and included directly from the
	      %% bifs file in the mCRL directory
	      add(assertion,
		  fun(E) ->
			  {op,0,'==',?tuplelength(E),{integer,0,length(Ps0)}} 
			  %% Adds fun (E) -> size(E) == length(Ps0) to
			  %% assertions
		  end,
		  Bindings,Assert),	 
 
	  foldl(fun({N,P},NBA) ->
			%% We also need to compute all the assertions
			%% and bindings for the pattern matching
			%% between each of the elements of the tuple
			%% and each of the elements of the rigth-hand
			%% side. For that, we introduce the mmCRL
			%% function 'element', also implemented in the
			%% mCRL bifs
			pattern(P,
				fun(E)-> 
					{call,0,{atom,0,element},[{integer,0,N},EFun(E)]} 
					
				end,
				NBA)
                end,
		{NB,NA},
		%% Pattern is called with a bunch of new
		%% functions. Later on this functions (fun(E) ->
		%% element(integer, EFun(E))) will be added to the
		%% Assertions.
		zip(lists:seq(1,length(Ps0)),Ps0));
      
       {record,Line,Name,Pfs0} -> 
	  %% TODO: Records are not implemented (they don't appear
	  %% defined in the mcrl file where the bifs are defined)
	  {NB,NA} = 
	      add(assertion,
		  fun(E) -> 
			  {call,0,{atom,0,record},[?tuplelength(E),{atom,0,Name}]}
			  %% Modified 16/10/2003
			  %% '?tuplelength(E),{atom,0,Name}'
			  %% should be a % list.
		  end,
		  Bindings,Assert),
	  foldl(fun({record_field,_,Field,P},NBA) ->
			pattern(P,fun(E)->
					  {call,0,{atom,0,element},
					   [{record_index,0,Name,Field},EFun(E)]}
				  end,NBA)
                end,{NB,NA},Pfs0);
						
      {op,Line,'++',{nil,_},R} ->
	  pattern(R,EFun,{Bindings,Assert});
      {op,Line,'++',{cons,L1,{integer,L2,I},T},R} ->
	  pattern({cons,L1,{integer,L2,I},{op,L1,'++',T,R}},EFun,
		  {Bindings,Assert});
      _ ->
       add(assertion,fun(E) -> {op,0,'==',EFun(E),Expr} end,Bindings,Assert) 
       % Adds fun (E) -> EFun(E) == Expr to assertions
  end.

%% Dict represents the bindings
add(assertion,Fun,Dict,Assert) ->
  {Dict,[Fun|Assert]};

add(Var,Fun,[],Assert) -> % There are no bindings
  {[{Var,Fun}],Assert};

add(Var,Fun,[{Var,F}|Dict],Assert) ->
  {[{Var,F}|Dict],[fun(E)->{op,0,'==',Fun(E),F(E)} end|Assert]};
add(Var,Fun,[{V,F}|Dict],Assert) when V<Var ->
  {NewDict,NewAssert} =
     add(Var,Fun,Dict,Assert),
  {[{V,F}|NewDict],NewAssert};
add(Var,Fun,[{V,F}|Dict],Assert) ->
  {[{Var,Fun},{V,F}|Dict],Assert}.

%% Pair of lists to list of pairs

zip([],[]) ->
  [];
zip([A|As],[B|Bs]) ->
  [{A,B}|zip(As,Bs)].

%% TODO: substitute by collect:vars. Is it really equal?

vars(Expr) ->
  case Expr of
       [] ->
         [];
       [E|Es] ->
         vars(E) ++ vars(Es);
       {var,Line,'_'} ->
         [];
       {var,Line,V} ->
         [{var,1,V}];
       {cons,Line,H0,T0} ->
         vars(H0)++vars(T0);
       {tuple,Line,Ps0} ->
         vars(Ps0);
       {record,Line,Name,Pfs0} ->
         vars(Name)++vars(Pfs0);
%    {record_field,Line,Rec0,Field0} ->
       {op,Line,'++',{nil,_},R} ->
         vars(R);
       {op,Line,'++',{cons,L1,{integer,L2,I},T},R} ->
         vars(T)++vars(R);
       _ ->
         []
  end.
