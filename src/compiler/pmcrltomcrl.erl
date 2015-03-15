% Generate data structures for mCRL that correspond to
%   Erlang data structures
%
%% <p>Thomas Arts. July 2002</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(pmcrltomcrl).

-export([file/2,file/3,forms/2]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

file(Dir,PMCRLFile) ->
  File = filename:join(Dir,PMCRLFile),
  ?DEBUG("reading ~p~n",[File]),
  {ok,AbsForms} = 
    epp:parse_file(File,[Dir],[]),
  forms(AbsForms,[]).

file(Dir,PMCRLFile,Dest) ->
  file:write_file(Dest,file(Dir,PMCRLFile)).

forms(AbsForms,Options) ->
    CodeDir = filename:dirname(code:which(?MODULE)),
    Sorts   = filename:join(CodeDir,"../mCRL"),
    {TopAbsForms,SefAbsForms,Actions} = split_code(AbsForms),
    
    MaxBuffer = 
	case lists:keysearch(buffer,1,Options) of
	    {value,{_,Max}} ->
		Max;
	    false ->
		unbounded
	end,
    
    %% List with all the atoms used in AbsForms in alphabetical order
    Atoms = sort(collect:atoms(AbsForms)),
    %% TODO: This could be moved into mcrlterms:forms, as it is done
    %% for the variables

    [include(Sorts,"bool.mcrl"),
     include(Sorts,"natural.mcrl"),
     include(Sorts,"observe_messages.mcrl"),				   
     %% nrprocs calculates the number of mcrl processes that are going
     %% to be created      
     %% natural_constants is going to create the naturals for using as
     %% pids inside the mcrl specification
     natural_constants(lists:seq(1,nrprocs(TopAbsForms)))]++
	mcrlterms:forms(SefAbsForms,Atoms)++ 
	[include(Sorts,"termstack.mcrl"),
	 case MaxBuffer of
	     none -> % synchronous communication (no buffer)
		 include(Sorts,"nobuffer.mcrl");
	     _ ->
		 [include(Sorts,"gsbuffer.mcrl"),
		  maxbuffer(MaxBuffer),
		  include(Sorts,"gsbuffer_proc.mcrl")]
	 end,
	 add_actions(Actions),
	 "proc\n\n",
	 map(fun(AbsForm) -> [proc_erl_pp:form(AbsForm),"\n"] end, TopAbsForms)].

%% Reads the Filename and converts it into a string

include(Dir,FileName) ->
  ?DEBUG("reading ~p~n",[filename:join(Dir,FileName)]),
  case file:read_file(filename:join(Dir,FileName)) of
       {ok,Data} ->
          binary_to_list(Data);
       {error,Reason} ->
          io:format("Error: cannot open ~p (~p)~n",[FileName,Reason]),
          []
  end.

nrprocs(AbsForms) ->
  case [ C || {function,_,init,0,[C]}<-AbsForms ] of
       [{clause,_,_,_,Body}] ->
          length(Body);
       _ -> % defensive programming, it should not happen
         ?MaxInt
  end.


%% @spec natural_constants(Natural::[integer()]) -> string()
%%
%% @doc
%%
%% These numbers are going to be used as pids in mcrl. The numbers are
%% declared as functions of arity zero over the sort of naturals

natural_constants(Naturals) ->
    ["map\n     "++ 
     %% withsep creates a string "Natural1,Natural2,...,NaturalN"
     withsep(fun(N) -> integer_to_list(N) end, ",", Naturals) ++
     ": -> Natural\n" ++
     "rew\n"|
     map(fun(N) -> "     "++integer_to_list(N)++" = "++mcrl_natural(N)++"\n"
	 end,
	 Naturals)++
     "\n\n\n"].



maxbuffer(N) when integer(N) ->
  "   maxbuffer(B1) = maxsize(B1," ++ mcrl_natural(N) ++ ")\n\n";
maxbuffer(_) ->
  "   maxbuffer(B1) = F\n\n".

mcrl_natural(0) ->
  "0";
mcrl_natural(N) ->
  "s("++mcrl_natural(N-1)++")".

withsep(F,Sep,[]) ->
  [];
withsep(F,Sep,[X]) ->
  F(X);
withsep(F,Sep,[X|Xs]) ->
  F(X) ++ Sep ++ withsep(F,Sep,Xs).

add_actions(Actions) ->
  ["act\n",
   "     assertion: " ++ ?Term++"\n",
   "     "++atom_to_list(?conftau)++"\n"|

   foldl(fun({erlang,F,A},G) -> %% they are removed because their
                                %% implementation would be taken from
                                %% a BIF.mcrl module instead. The
                                %% compiler should check that the
                                %% funtions are in fact implemented
                                %% there or give a warning otherwise.
		 ?DEBUG("built in function ~p/~p~n",[F,A]),
		 G;
	    ({lists,F,A},G) ->
		 ?DEBUG("external lists function ~p/~p~n",[F,A]),
		 G;
	    ({M,F,A},G) ->
		 case incomm({M,F,A},?SIDEEFFECTS) of 
		     true -> % If the function is in ?SIDEEFFECTS
			 G;
		     false -> 
			 ["     "++atom_to_list(M)++"_"++atom_to_list(F)++
			  case A of
			      0 -> "";
			      _ -> ": "++?Term++[" # "++?Term || X<-seq(2,A)]
			  end ++ "\n"|
			  G]
             end
	 end,
	 [],
	 Actions)].


split_code(AbsForms) ->
  until_copyright(AbsForms,[]).

until_copyright([{attribute,_,copyright,{actions,Acts}}|AbsForms],Sef) ->
  {AbsForms,Sef,Acts};
until_copyright([AbsForm|AbsForms],Sef) ->
  until_copyright(AbsForms,Sef++[AbsForm]).

incomm({M,F,A},[]) ->
  false;
incomm({M,F,A},[{MF1,MF2,_,_}|Rest]) ->
  case ({M,F,A}==MF1) or ({M,F,A}==MF2) or ({F,A}==MF1) or ({F,A}==MF2) of
       true ->
         true;
       false ->
         incomm({M,F,A},Rest)
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

seq(N,M) when N=<M ->
  [N|seq(N+1,M)];
seq(N,M) -> 
  [].

