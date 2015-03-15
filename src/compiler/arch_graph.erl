%% @doc
%% <p>arch_graph - translate program graph in arch_graph</p>
%%
%% <p>Juanjo Sánchez. November 2003</p> 
%%
%% <p>Takes a .aut file as input and generates a new graph where the
%% nodes are the processes in the system architecture and the
%% messages, the same ones as in the original one. The labels in the
%% input graph are assumed to contain the process source and
%% destination for every message. Identity transitions are removed.</p>
%%
%% @end
%%
%% with shell call support 
%% in shell:  erl -noshell -s $MODULE aut -file $FILENAME -s erlang halt

-module(arch_graph).

-export([aut/0,file/1]).

-import(lists,[sort/1,map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

%% @doc
%%
%% <p>Used for executing arch_graph from the Erlang shell</p>
%%
%% <p>Obtains the list of filenames and calls file/1 for all of
%% them</p>
%%
%% @end

aut() ->
  {ok,[Args]} = init:get_argument(file),
  map(fun(File) -> file(File) end, Args).

%% @doc
%%
%% <p>Filename: name of the .?MCRLExt.aut file</p>
%%
%% <p>Generates the new graph as output with extension .arch.aut</p>
%%
%% @end

file(FileName) ->
    RootName = filename:rootname(FileName),
    lines(FileName,RootName++".arch.aut",[],[],
	  fun(S,N, State) -> convert(S,N,State) end).

convert([$d,$e,$s|Rest],N, StateInfo) -> 
  {"des"++Rest,N+1, StateInfo};
convert(Trans,N, StateInfo) ->
    L = string:chr(Trans,$,), % Index of the first ',' in the string Trans
    R = string:rchr(Trans,$,),% Index of the last ',' in the string Trans
    case R-L of 
	2 ->
	    {remove,N,StateInfo}; % Remove the 'i' transitions
	_ ->
	    Expr = string:sub_string(Trans,L+2,R-2),
	    {ok,Tokens,_} = erl_scan:string(Expr),
	    {ok,[AbsExpr]} = erl_parse:parse_exprs(Tokens++[{dot,1}]),
	    
	    %% We extract Source process, destination process and
	    %% Message from the AbsExpr of the label in the transition
	    {Source, Destination, Message} = rewrite(AbsExpr),	    

	    %% StateInfo contains {StateNumber, StateDict}, and it is
	    %% updated by state_from_info in case a new state is
	    %% created in the architecture graph
	    {NewStateInfo, NewSource} = 
		state_from_info(StateInfo, 
				lists:flatten(erl_pp:expr(Source))),
	    
	    {NewNewStateInfo, NewDest} = 
		state_from_info(NewStateInfo,
				lists:flatten(erl_pp:expr(Destination))),
	    
	    {"("++NewSource++
	     ",\""++lists:flatten(erl_pp:expr(Message))++
	     "\","++NewDest++")\n", 
	     N+1, 
	     NewNewStateInfo}
    end.

state_from_info({StateNumber, StateDict}, String) ->
    case dict:find(String, StateDict) of
	{ok, Value} ->
	    {{StateNumber, StateDict}, Value};
	_ ->	    	    
	    NewDict = dict:append(String, integer_to_list(StateNumber), StateDict),    
	    {{StateNumber+1, NewDict}, integer_to_list(StateNumber)}
    end.

rewrite({call,Line,{atom,_,_},[Dest,Msg,Source]}) ->
    {Source, Dest, Msg};
rewrite(Other) ->
    {"error","error",Other}.

%%-------- Ulf's fileio.erl -----------------------------

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
    (catch process(In, Out, Fun, 0, {0, dict:new()})).  % counter for state

process(In, Out, Fun, M, StateInfo) ->
    case io:get_line(In, "") of
	eof ->
	    {ok,M};
	Line ->
            {String,N,NewStateInfo} = Fun(Line,M,StateInfo),
	    case M>=0 of
		true ->
		    case String of 
			remove ->
			    process(In, Out, Fun, N, NewStateInfo);
			_ ->
			    ok = io:put_chars(Out, String),
			    process(In, Out, Fun, N, NewStateInfo)
		    end;
		false ->
		    {ok,M}
            end
    end.

