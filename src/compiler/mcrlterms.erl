%% Generate mCRL terms 
%%
%% Generates the mcrl terms corresponding to the sef abstract forms
%%
%% <p>Thomas Arts. July 2002</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(mcrlterms).

-export([forms/2]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%% start from the side-effect free part of the code, 
%%  with all atoms of the whole code

forms(AbsForms,AllAtoms) ->
    CodeDir = filename:dirname(code:which(?MODULE)),
    Atoms =  
	%% Legal atoms
	sets:to_list(
	  %% true, false and all the other atoms used in the source
	  %% code that are not in the following list: pid, int, nil,
	  %% cons, tuplenil, tuple, true and false
	  legal_atoms(AllAtoms,
		      sets:from_list([true,false]), 
		      foldl(fun({A,_},As) ->
				    sets:add_element(A,As)
			    end,
			    sets:new(),
			    ?MCRL_TERM_CONSTRUCTORS))),

    Vars = 
	sort(sets:to_list(
	       legal_vars(collect:vars(AbsForms),
			  foldl(fun({_,VTs},Vs) ->
					%% Vars inside
					%% ?MCRL_TERM_CONSTRUCTORS
					%% with a ?Term in the rhs are
					%% included
					foldl(fun({V,T},NVs) ->
						      case T==?Term of
							  true ->  sets:add_element(V,NVs);
							  false -> NVs
						      end
					      end,
					      Vs,
					      VTs)
				end,
				sets:new(),
				?MCRL_TERM_CONSTRUCTORS),
			  sets:from_list(?MCRL_RESERVED_VARS)))), %% Excluded from the legal vars
    
    [basicterms(map(fun({Cons,Args}) ->
			    {Cons,number(Args,1)} % §argument number is
                                                  % placed at the
                                                  % beginning of the
                                                  % tuple
		    end,?MCRL_TERM_CONSTRUCTORS)++
		map(fun(Atom) -> 
			    {Atom,[]} % empty list means that atoms
                                      % are constructors of the sort
                                      % term with arity 0
		    end,Atoms)),

     include(filename:join(CodeDir,"../mCRL"),"bifs.mcrl"),
     "map   % ERLANG side-effect free functions\n",
     map(fun({function,Line,Name,Arity,_}) ->
		 "     "++atom_to_list(Name)++":"++  
		     withsep(fun(_)-> ?Term end," # ",seq(1,Arity))++" -> "++?Term++"\n";
	    (_) ->
		 ""
	 end,
	 lists:keysort(3,AbsForms)), % Orders the abstract forms by name
     "\nvar\n     ",
     withsep(fun(V) -> V end,",",Vars)++": Term\n",
     "rew\n"
    ]++map(fun(AF) -> pp(AF) end, AbsForms).

include(Dir,FileName) ->
    ?DEBUG("reading ~p~n",[filename:join(Dir,FileName)]),
    case file:read_file(filename:join(Dir,FileName)) of
	{ok,Data} ->
	    binary_to_list(Data);
	{error,Reason} ->
	    io:format("Error (~p): cannot open ~p (~p)~n",
		      [?MODULE,FileName,Reason]),
	    []
    end.

withsep(F,Sep,[]) ->
  [];
withsep(F,Sep,[X]) ->
  F(X);
withsep(F,Sep,[X|Xs]) ->
  F(X) ++ Sep ++ withsep(F,Sep,Xs).

%+type legal_vars([absform()],set(string()),set(atom())) -> set(string()).
%
legal_vars(AbsVars,Included,Excluded) ->
  foldl(fun({var,Line,V},Vs) ->
           case sets:is_element(V,Excluded) of
                true ->
                  io:format("Error in line ~p: variable ~p should not be used~n",
                            [Line,V]),
                  Vs;
                false ->
                  sets:add_element(atom_to_list(V),Vs)
           end
        end,
	Included,
	AbsVars).

%%+type legal_atoms([absform()],set(atom()),set(atom())) -> set(atom()).
%%
%% Adds to Included all the atoms in AbsAtoms that are not in Excluded

legal_atoms(AbsAtoms,Included,Excluded) ->
  foldl(fun({atom,Line,A},As) ->
           case sets:is_element(A,Excluded) of
                true ->
                  io:format("Error in line ~p: atom ~p should not be used~n",
                            [Line,A]),
                  As;
                false ->
                  sets:add_element(A,As)
           end
        end, 
	Included, 
	AbsAtoms).

number([],N) ->
  [];
number([{V,T}|Rest],N) ->
  [{N,V,T}|number(Rest,N+1)].
  
  

basicterms(Constructors) ->
  ["sort\n     "++?Term++"\nfunc\n",
   map(fun({Name,Args}) -> 
          "     "++atom_to_list(Name)++": " ++
          withsep(fun({_,_,Type}) -> Type end, " # ",Args)++" -> "++?Term++"\n"
       end,Constructors),
   recognizers(Constructors),
   destructors(Constructors),
   equalityrules(Constructors)].

recognizers(Constructors) ->
  ["\n% RECOGNIZERS\n\n",
   "map\n     ",
   withsep(fun({Name,_}) -> "is_"++atom_to_list(Name) end, ",", Constructors) ++
     ": "++?Term++" -> Bool\n",
   "var\n",
   map(fun({Type,Vars}) -> 
	       "     "++withsep(fun(V) -> V end, ",", Vars)++": "++Type++"\n"
       end,
       %% All the pairs {variable,type} in the Constructors
       foldl(fun({Name,Args},Dict) ->
		     foldl(fun({_,V,T},D) -> 
				   adduniq(T,V,D) 
			   end,
			   Dict,
			   Args)
	     end,
	     [],
	     Constructors)),
   "rew\n",
   map(fun({Name,_}) ->
	       map(fun({N,[]}) -> 
			   "     is_"++atom_to_list(Name)++
			       "("++atom_to_list(N)++") = "++
			       case N==Name of
				   true -> "T\n";
				   false -> "F\n"
			       end;
		      ({N,Args}) -> 
			   "     is_"++atom_to_list(Name)++
			       "("++atom_to_list(N)++"("++
			       withsep(fun({_,V,_}) -> V end,",",Args)++ ")) = "++
			       case N==Name of
				   true -> "T\n";
				   false -> "F\n"
			       end
		   end,
		   Constructors)
       end,
       Constructors)
  ].

destructors(Constructors) ->
  ["\n% DESCTRUCTORS\n\n",
   "map\n",
   foldl(fun({Name,[]},Ds) -> 
              Ds;
            ({Name,Args},Ds) ->
              map(fun({Nr,_,Type}) ->
                     "     "++ atom_to_list(Name)++integer_to_list(Nr)++
                     ": "++?Term++" -> "++Type++"\n"
                  end,Args)++Ds
         end,[],Constructors),
   "var\n",
    map(fun({Type,Vars}) ->
           "     "++withsep(fun(V) -> V end, ",", Vars)++": "++Type++"\n"
         end,foldl(fun({Name,Args},Dict) ->
                      foldl(fun({_,V,T},D) -> adduniq(T,V,D) end,Dict,Args)
                   end,[],Constructors)),
   "rew\n",
   foldl(fun({Name,[]},Ds) -> 
               Ds;
             ({Name,Args},Ds) ->
               map(fun({Nr,Var,_}) ->
                      "     "++ atom_to_list(Name)++integer_to_list(Nr)++
                      "("++atom_to_list(Name)++"("++
                      withsep(fun({_,V,_}) -> V end,",",Args)++
                      ")) = "++Var++"\n"
                   end,Args)++Ds
          end,[],Constructors)
  ].


equalityrules(Constructors) ->
  ["\n% EQUALITY and IF-THEN-ELSE\n\n",
   "map\n",
   "     eq:  "++?Term++" # "++?Term++" -> Bool\n",
   "     if: Bool # "++?Term++" # "++?Term++" -> "++?Term++"\n",
   "var\n",
    map(fun({Type,Vars}) ->
           "     "++withsep(fun(V) -> V end, ",", Vars)++": "++Type++"\n"
         end,foldl(fun({Name,Args},Dict) ->
                      foldl(fun({_,V,T},D) -> adduniq(T,V,D) end,Dict,Args)
                   end,[{?Term,["MCRLTerm1","MCRLTerm2"]},
                        {"Bool",["MCRLBool"]}],Constructors)),
   "rew\n",
   "     if(T,MCRLTerm1,MCRLTerm2) = MCRLTerm1\n",
   "     if(F,MCRLTerm1,MCRLTerm2) = MCRLTerm2\n",
   %"     if(MCRLBool,MCRLTerm1,MCRLTerm1) = MCRLTerm1\n", % Removed this!!
   map(fun({Name,[]}) ->
            "     eq("++atom_to_list(Name)++",MCRLTerm2) = is_"++
              atom_to_list(Name)++"(MCRLTerm2)\n"++
            "     eq(MCRLTerm1,"++atom_to_list(Name)++") = is_"++
              atom_to_list(Name)++"(MCRLTerm1)\n";
          ({Name,Args}) -> 
            "     eq("++atom_to_list(Name)++"("++
              withsep(fun({_,V,_}) -> V end,",",Args)++ "),MCRLTerm2) = "++
            andclause(
                     ["is_"++atom_to_list(Name)++"(MCRLTerm2)"|
                      map(fun({Nr,A,_}) ->
                             "eq("++A++","++
                              atom_to_list(Name)++integer_to_list(Nr)++
                              "(MCRLTerm2))"
                          end,Args)])++"\n"++
            "     eq(MCRLTerm1,"++atom_to_list(Name)++"("++
              withsep(fun({_,V,_}) -> V end,",",Args)++")) = "++
            andclause(
                     ["is_"++atom_to_list(Name)++"(MCRLTerm1)"|
                      map(fun({Nr,A,_}) ->
                             "eq("++atom_to_list(Name)++integer_to_list(Nr)++
                              "(MCRLTerm1),"++A++")"
                          end,Args)])++"\n"
       end,Constructors)
  ].

  
andclause([Term]) ->
  Term;
andclause([Term|Terms]) ->
  "and("++Term++","++andclause(Terms)++")".

adduniq(Key,Value,[]) ->
  [{Key,[Value]}];
adduniq(Key,Value,[{Key,Values}|Rest]) ->
  case member(Value,Values) of
       true ->
         [{Key,Values}|Rest];
       false ->
         [{Key,[Value|Values]}|Rest]
  end;
adduniq(Key,Value,[{K,Vs}|Rest]) ->
  [{K,Vs}|adduniq(Key,Value,Rest)].
  

seq(N,M) when N>M ->
  [];
seq(N,M) ->
  [N|seq(N+1,M)].

to_natural(0) ->
  "0";
to_natural(N) when N>0 ->
  "s("++to_natural(N-1)++")".



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% print the side effect free functions in mCRL syntax
%    The functions have been simplified already
%
pp({function,Line,Name,Arity,Clauses}) ->
    map(fun({clause,L,Head,Guards,Body}) ->
		case Guards of
		    [] ->
			ok;
		    _ ->
			?ERROR(L,"guards not allowed in function ~p/~p~n",
			    [Name,Arity])
			    end,
		Expression =
		    case Body of
			[Expr] ->
			    Expr;
			_ ->
			    ?ERROR(L,"sequential operator not understood ~p/~p~n",
				[Name,Arity]),
			    hd(Body)
		    end,
		"     "++expr({call,Line,{atom,Line,Name},Head})++" = "++
		    expr(Expression)++"\n"
	end,
      Clauses);
pp(_) ->
  "\n".

expr(E) ->
  case E of
       {var,_,V} ->
          atom_to_list(V);
       {atom,_,A} ->
          atom_to_list(A);
       {float,Line,F} ->
          ?ERROR(Line,"floating points not allowed ~p~n",[F]),
          "ERROR:"++float_to_list++":ERROR";
       {integer,Line,N} when N<0->
          ?WARNING(Line,"negative number ~p inconvenient~n",[N]),
          "int(minus(0,"++to_natural(N)++"))";
       {integer,Line,N} when N>50->
          ?WARNING(Line,"large natural number ~p inconvenient~n",[N]),
          "int("++to_natural(N)++")";
       {integer,Line,N} ->
          "int("++to_natural(N)++")";
       {nil,_} ->
          "nil";
       {cons,_,H,T} ->
          "cons("++expr(H)++","++expr(T)++")";
       {tuple,Line,Es} ->
          case Es of
               [] ->
                  ?ERROR(line,"empty tuple not accepted~n",[]),
                  "ERROR:{}:ERROR";
               _ -> 
                 tuple(Es)
          end;
       {call,_,{atom,_,pid},[{integer,_,N}]} ->
          "pid("++to_natural(N)++")";
       {call,_,{atom,_,Name},Args} ->
          atom_to_list(Name)++
          case Args of
               [] ->
                  " ";
               _ -> 
                  "("++withsep(fun(A) -> expr(A) end,",",Args)++")"
          end;
       {call,Line,{remote,_,{atom,_,Mod},{atom,_,Fun}},Args} ->
          case member({Mod,Fun,length(Args)},?See_as_Bifs) of
               true ->
                 atom_to_list(Fun)++
                 case Args of
                      [] ->
                         " ";
                      _ -> 
                         "("++withsep(fun(A) -> expr(A) end,",",Args)++")"
                 end;
               false ->
                 ?ERROR(Line,"imported function ~p:~p/~p~n",
                        [Mod,Fun,length(Args)]),
                 "ERROR:"++atom_to_list(Mod)++"_"++atom_to_list(Fun)++":ERROR"
         end;
       {op,Line,Op,Arg} ->
         atom_to_list(Op)++"("++expr(Arg)++")"; 
       {op,Line,Op,Arg1,Arg2} ->
         case lists:keysearch(Op,1,?BIN_OPERATORS) of
              {value,{_,Operator}} ->
                Operator++"("++expr(Arg1)++","++expr(Arg2)++")";
              false ->
                ?WARNING(Line,"unknown operator ~p~n",[Op]),
                atom_to_list(Op)++"("++expr(Arg1)++","++expr(Arg2)++")"
         end;
       _ ->
          ?ERROR(element(2,E),"unrecognized control structure ~p~n",
                 [element(1,E)]),
          "ERROR:"++atom_to_list(element(1,E))++":ERROR"
  end.

tuple([E]) ->
  "tuplenil("++expr(E)++")";
tuple([E|Es]) ->
  "tuple("++expr(E)++","++tuple(Es)++")".
