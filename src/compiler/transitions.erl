% 
% Translating labels in transition system to Erlang syntax
%
% with shell call support (May 2001)
% in shell:  erl -noshell -s $MODULE aut -file $FILENAME -s erlang halt
% 
%
% Thomas Arts
% May 2001

-module(transitions).

-export([aut/0,file/1,file/2,from_trace/2]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").


%% Used for executing transitions from the Erlang shell
%%
%% Obtains the list of filenames and calls file/1 for all of them
aut() ->
  {ok,[Args]} = init:get_argument(file),
  map(fun(File) -> file(File) end, Args).

%% Used when no Procs are specified

file(FileName) ->
  file(FileName,[]).

%% Filename: name of the .?MCRLExt.aut file 
%% Procs: list of integers with the processes numbers

file(FileName,Procs) ->
    Filter = % List with ["pid(Proc1)","pid(Proc2)",...]
	[ "pid("++integer_to_list(P)++")"||P<-Procs],
    case Filter of
	[] ->
	    ok;
	_ ->
	    io:format("proc activity mapped to `i': ~p~n",[Filter])
    end,
    RootName = filename:rootname(FileName),
    case filename:extension(RootName) of
	?MCRLExt ->
	    lines(FileName,filename:rootname(RootName)++".aut",[],[],
		  fun(S,N) -> {convert(S,Filter),N+1} end);
	Other ->
	    {error,"extension not "++?MCRLExt++".aut"}
    end.

from_trace(FileName,MaxLines) ->       
  % needs des (BeginState, NumberLines, EndState+1) as startline
  % which is: des (0, NrLines+1, NrLines)
  RootName = filename:rootname(FileName),
  {ok,NrLines} =
  lines(FileName,RootName++".tmp",[],[],
        fun(S,N) ->
           case (N rem 400) of
                0 -> io:format(".");
                _ -> ok
           end,
           Info = string:substr(S,7,length(S)-7),
           {io_lib:format("(~w,\"~s\",~w)~n",[N,Info,N+1]),N+1}
	end),
  Lines = 
    case NrLines > MaxLines of
         true -> MaxLines+1;
         false -> NrLines
    end,
  lines(RootName++".tmp",RootName++".aut",
        io_lib:format("des (0, ~w, ~w)~n",[Lines+1,Lines+1]),
        io_lib:format("(~w,\"terminated\",~w)~n",[Lines,Lines]),
        fun(S,N) -> {S,case N<MaxLines of
                            true -> N+1;
                            false -> -1
                       end} end).

convert([$d,$e,$s|Rest],Procs) -> 
  "des"++Rest;
convert(Trans,Procs) ->
  L = string:chr(Trans,$,),
  R = string:rchr(Trans,$,),
  [string:substr(Trans,1,L),
   case R-L of
        2 ->
          "i";
        D when D>2 ->
         Expr = string:sub_string(Trans,L+2,R-2),
         {ok,Tokens,_} = erl_scan:string(Expr),
         {ok,[AbsExpr]} = erl_parse:parse_exprs(Tokens++[{dot,1}]),
         case lists:flatten(erl_pp:expr(rewrite(AbsExpr))) of
              "tau" ->
                "i";
              Other ->
                "\""++filterproc(Procs,Other)++"\""
         end
   end,
   string:substr(Trans,R)].

filterproc([],String) ->
  String;
filterproc([S|Ss],String) ->
  case string:str(String,S) of
       0 ->
         filterproc(Ss,String);
       _ ->
         "i"
  end.

rewrite({call,Line,{atom,_,communication},[Arg1,Arg2]}) ->
  {op,Line,'!',rewrite(Arg1),rewrite(Arg2)};
rewrite({call,Line,{atom,_,int},[Arg]}) ->
  rewrite(Arg);
rewrite({call,Line,{atom,_,s},[Arg]}) ->
  {integer,_,I} = rewrite(Arg),
  {integer,Line,I+1};
rewrite({call,Line,{atom,_,tuple},[{atom,_,mcrlrecord},Tuple]}) ->
  {call,_,{atom,_,tuple},[{atom,_,Name},Fields]} = Tuple,
  Values = mcrltuple_to_list(Fields),
  {record,Line,Name,map(fun(F) -> {record_field,Line,F} end, Values)};
  %{op,0,'#',rewrite(Tuple)};   % we have no information of field names
rewrite({call,Line,{atom,_,tuple},[Arg1,Arg2]}) ->
  NewArg1 = rewrite(Arg1),
  NewArg2 = mcrltuple_to_list(Arg2),
  {tuple,Line,[NewArg1|NewArg2]};
rewrite({call,Line,{atom,_,tuplenext},[Arg1,Arg2]}) ->
  NewArg1 = rewrite(Arg1),
  NewArg2 = rewrite(Arg2),
  case NewArg2 of
       {tuplenext,Args} ->
          {tuplenext,[NewArg1|Args]};
       _ ->
          {tuplenext,[NewArg1,NewArg2]}
  end;
rewrite({call,Line,{atom,_,cons},[Head,Tail]}) ->
  {cons,Line,rewrite(Head),rewrite(Tail)};
%rewrite({call,Line,{atom,_,pid},[Number]}) ->
%  {integer,_,N} = rewrite(Number),
%  {string,Line,"<.,"++integer_to_list(N)++",.>"};
rewrite({call,Line,{atom,_,F},Args}) ->
  %io:format("func ~p~n",[F]),
  {call,Line,{atom,Line,F},map(fun(A) -> rewrite(A) end, Args)};
rewrite({atom,Line,nil}) ->
  {nil,Line};
rewrite(Other) ->
  Other.

mcrltuple_to_list({call,_,{atom,_,tuplenil},[Arg1]}) ->
  [rewrite(Arg1)];
mcrltuple_to_list({call,_,{atom,_,tuple},[Arg1,Arg2]}) ->
  [rewrite(Arg1)|mcrltuple_to_list(Arg2)].


%-------- Ulf's fileio.erl -----------------------------

lines(InFile, OutFile, Header, Trailer, Fun) ->
    case file:open(InFile, [read]) of
	 {ok, In} ->
	    case file:open(OutFile, [write]) of
		 {ok, Out} ->
	            case Header of
                         [] -> ok;
                         _ -> io:put_chars(Out, Header)
                    end,
		    Result = process_files(In, Out, Fun),
	            case Trailer of
                         [] -> ok;
                         _ -> io:put_chars(Out, Trailer)
                    end,
                    file:close(In),
                    file:close(Out),
                    Result;
		 {error, Reason} ->
		    file:close(In),
		    {error, {Reason, OutFile}}
	    end;
	 {error, Reason} ->
	    {error, {Reason, InFile}}
    end.


process_files(In, Out, Fun) ->
    (catch process(In, Out, Fun, 0)).  % counter for state

process(In, Out, Fun, M) ->
    case io:get_line(In, "") of
	eof ->
	    {ok,M};
	Line ->
            {String,N} = Fun(Line,M),
	    case M>=0 of
                 true ->
                   ok = io:put_chars(Out, String),
	           process(In, Out, Fun, N);
                 false ->
                   {ok,M}
            end
    end.

