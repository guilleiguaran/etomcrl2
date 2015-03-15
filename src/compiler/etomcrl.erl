%% @doc
%% <p>etomcrl - translate Erlang to mCRL</p>
%%
%% <p>with scripting possibilities
%%  UNIX shell scripting sucks</p>
%%
%% <p>Thomas Arts. June 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>
%%
%% <p>This module acts as the interface between the user and the etomcrl
%% tool. It contains high level functions that allow to use the
%% compilator inside the Erlang shell or from the command line of any
%% other shell.</p>
%% @end


-module(etomcrl).

-export([supervisor/3,instantiator/3,supervisor/6,
         script/0, batch/0]).

-include("etomcrl.hrl").

-import(lists,[map/2,foreach/2,foldl/3,keysearch/3,reverse/1]).

%% @doc
%% <p>Execute the function supervisor without starting the Erlang shell.
%% It obtaines the arguments from the string given as a parameter after 
%% the -start option.</p> 
%% Example:
%% <code>erl -noshell -s etomcrl script -start "mod:function([arguments])"</code>
%% @end

script() ->
  {ok,[Args]} = init:get_argument(start),
  case Args of
       [StartTerm] ->
         {ok,Tokens,_} = erl_scan:string(StartTerm),
         case Tokens of
              [{atom,_,Mod},{':',_},{atom,_,Fun},{'(',_}|ArgsPar] ->
                case parse_exprs(dotlast(ArgsPar)) of
                     {ok,AbsTerms} ->
                       Terms =
                         map(fun(T) -> erl_parse:normalise(T) end, AbsTerms),
                       MCRLFile = supervisor(Mod,Fun,Terms),
                       io:format("mCRL file written (~p)~n",[MCRLFile]);
                     {error,Reason} ->
                       io:format("Error: use \"Mod:Fun(ArgList)\"~n~p ~p~n",
                                  [Reason,ArgsPar])
                end;
              _ ->
                io:format("Error: use ~p \"Mod:Fun(ArgList)\"~n",[?MODULE])
         end;
       _ ->
         io:format("Error: use ~p \"Mod:Fun(ArgList)\"~n",[?MODULE])
  end.

%% @doc
%% batch/0 and batch/2 allow to check a list of properties against a list 
%% of configurations. To do so, it calls the muCRL tools needed to 
%% generate the LTS and the CADP tools to model check the properties.
%% Example:
%% erl -noshell -s etomcrl batch -file "file1" -property "file2"
%% file1 should contain a list of "mod:function([arguments])". Those are 
%% the programs one wants to verify.
%% file2 should contain a list of properties expressed in the alternation-free
%% mu-calculus used by the CADP toolset.

%% batch/0 takes the command line arguments, reads the contents of the given 
%% files and calls batch/2 which would perform all the other operations.


batch() ->
  case init:get_argument(file) of
       {ok,StartTermsFile} ->
         case init:get_argument(property) of
              {ok,PropertyFiles} ->
                case file:read_file(StartTermsFile) of
                     {ok,Binary} ->
                       CharList = binary_to_list(Binary),
                       Properties =
                         map(fun(Property) ->
                                filename:join(?MCRLDir,Property++".mcl")
                             end,hd(PropertyFiles)),
                       io:format("batch starts for ~p~n",[Properties]),
                       batch(string:tokens(CharList,[10]),Properties);
                     {error,Reason} ->
                       io:format("Error: cannot read ~p ~p~n",
                                 [StartTermsFile,Reason])
                end;
              _ ->
               io:format(
                "Error: use ~p -batch -file ErlangTermsFile "++
                "-property PropertyFiles~n",[?MODULE])
         end;
       _ -> 
         io:format(
           "Error: use ~p -batch -file ErlangTermsFile "++
           "-property PropertyFiles~n",[?MODULE])
  end.

batch([],Properties) ->
  io:format("batch done for ~p~n",[Properties]);
batch([""|Strs],Properties) ->
  batch(Strs,Properties);
batch([Str|Strs],Properties) ->
  case erl_scan:string(Str) of
       {ok,[{atom,_,Mod},{':',_},{atom,_,Fun},{'(',_}|ArgsPar],_} ->
         case parse_exprs(dotlast(ArgsPar)) of
              {ok,AbsTerms} ->
                 Terms = map(fun(T) -> erl_parse:normalise(T) end, AbsTerms),
                 {ok,Here} = file:get_cwd(),
                 StartTime = now(),
                 MCRLFile = 
                   filename:basename(supervisor("",?TempDir,Mod,Fun,Terms,[])),
                 file:set_cwd(?TempDir),
                 io:format("mCRL file written for ~s (~s)~n",[Str,MCRLFile]),
                 Linearise = 
                   os:cmd("mcrl -tbfile "++MCRLFile),
                 ?DEBUG("instantiator: ~s~n",[Linearise]),
                 Instance = 
                   os:cmd("instantiator "++MCRLFile),
                 ?DEBUG("instantiator: ~s~n",[Instance]),
                 io:format("instantiator: ~p~n",
                    [hd(reverse(string:tokens(Instance,[10])))]),
                 transitions:file(MCRLFile++".aut"),
                 os:cmd("bcg_io "++MCRLFile++".aut -parse "++MCRLFile++".bcg"),
                 file:delete(MCRLFile++".aut"),
                 Results = 
                   map(fun(Property) ->
                          {Property++"\nproperty: "++os:cmd("cat "++Property),
                           hd(reverse(string:tokens(
                              os:cmd("bcg_open "++MCRLFile++
                                     ".bcg evaluator -verbose "++
                                     Property),[10])))}
                       end,Properties),
                 file:delete(MCRLFile++".bcg"),
                 lists:foreach(fun({Cat,Result}) ->
                                  io:format("~sevaluator: ~p~n",
                                            [Cat,Result])
                               end,Results),
                 io:format("Real time spent: ~p sec~n~n",
                           [time_difference(StartTime,now())]),
                 file:set_cwd(Here);
               {error,Reason} ->
                 io:format("Error: parsing batch ~p ~p~n",[Str,Reason])
          end,
          batch(Strs,Properties);
        _ ->
          io:format("Error: skipped entry ~p in batch~n",[Str]),
          batch(Strs,Properties)
  end.

%% @doc
%% Auxiliar function used by batch/2 to calculate the time transcurred between 
%% operations. The arguments are the result of calling the BIF now/0 in 
%% two different moments during the excution of batch/2. 
%% now/0 returns the tuple {MegaSecs, Secs, Microsecs} 
%% which is the elapsed time since 00:00 GMT, January 1, 1970

time_difference({H1,M1,_},{H2,M2,_}) ->
  (H2-H1)*1000000+(M2-M1).

%% @doc
%% Change: erl_parse:parse_expr/1
%%
%% empty sequence, i.e. [{dot,1}] not parsed to empty list []
%% @end

parse_exprs([{dot,_}]) ->
    {ok,[]};
parse_exprs(Exprs) ->
    erl_parse:parse_exprs(Exprs).

%% @doc
%% Auxiliar function used to re-arrange the output of the function 
%% erl_scan:string/1. 
%% If the string does not contain a dot at the end, it is added.
%% In any case, the last parenthesis is removed.
%% Examples:
%% 1> erl_scan:string("module:func([Arg1,Arg2])").
%% {ok,[{atom,1,module},
%%      {':',1},
%%      {atom,1,func},
%%      {'(',1},
%%      {'[',1},
%%      {var,1,'Arg1'},
%%      {',',1},
%%      {var,1,'Arg2'},
%%      {']',1},
%%      {')',1}],
%%     1}
%% dotlast/1 is called with 
%%      [{'[',1},
%%      {var,1,'Arg1'},
%%      {',',1},
%%      {var,1,'Arg2'},
%%      {']',1},
%%      {')',1}]
%% 2> erl_scan:string("module:func([Arg1,Arg2]).").
%% {ok,[{atom,1,module},
%%      {':',1},
%%      {atom,1,func},
%%      {'(',1},
%%      {'[',1},
%%      {var,1,'Arg1'},
%%      {',',1},
%%      {var,1,'Arg2'},
%%      {']',1},
%%      {')',1},
%%      {dot,1}],
%%     1}
%% dotlast/1 is called with 
%%      [{'[',1},
%%      {var,1,'Arg1'},
%%      {',',1},
%%      {var,1,'Arg2'},
%%      {']',1},
%%      {')',1},
%%      {dot,1}]
%%@end
 
dotlast([_]) ->
    [{dot,1}];
dotlast([_,{dot,_}]) ->
    [{dot,1}];
dotlast([H|T]) ->
    [H|dotlast(T)].

%% @spec supervisor(SrcDir::string(),DestDir::string(),Mod::atom(),Fun::atom(),Args::[term()],Options::options()) -> 
%%                     string()
%%
%%                options() = [{atom(),term()}]
%% @doc
%% This function starts the compilation process. 
%% <dl>
%% <dt>ScrDir</dt> 
%%    <dd>is the directory where the source code is located</dd>
%% <dt>Destdir</dt>
%%     <dd>is the directory where the resulting file with mCRL
%% spec.  is located. The file is named after the name of the module
%% given as a third argument for the supervisor/6 function and it has
%% a mCRL extension.</dd>
%% <dt>Mod </dt>
%%     <dd>is an atom representing the name of the module. This module 
%%   contains the implementation of the root of the supervision tree</dd>
%% <dt>Fun</dt>
%%     <dd>is the function that starts the supervision tree</dd>
%% <dt>Args</dt>
%%      <dd>is the list of the arguments that are passed to Fun.</dd>
%% <dt>Options</dt> 
%%      <dd>is a list of tuples with options for the compiler. </dd>
%%   <dl>Supported options are:
%%      <dt>{file,Directory}</dt> 
%%          <dd>to store intermediate files. These files are created 
%%              at different stages during the compilation.</dd> 
%%      <dt>{buffer,N}</dt> 
%% <dd>to set the size of buffer to int N. This buffer is used to
%%           implement the asynchronous communication between
%%           processes in mCRL.  This is only used in the last phase
%%           of the compilation, when the Erlang program is fully
%%           translated to mCRL. N could also be none, meaning
%%           synchronous communication</dd> %% </dl> %%</dl> 
%% Return:the name of the file where the mCRL spec is written
%%           
%%@end

supervisor(SrcDir,DestDir,Mod,Fun,Args,Options) ->
    {ok,CurrentDir} = file:get_cwd(),
    file:set_cwd(SrcDir),
    AbsFormsList = etoe:supervisor(Mod,Fun,Args), 
    %% first phase of the compiler. It returns a list with the
    %% abstract forms for each of the modules that implement the
    %% processes that are started by the supervision tree.  The
    %% abstract forms for each module have the attribute "copyright"
    %% separating the SEF part from the part with side-effects
    file:set_cwd(CurrentDir),    
    
    case keysearch(file,1,Options) of 
	%% writes the list with the abstract forms to the TempDir if the
	%% option file was specified
	{value,{file,TempDir}} -> 
	    foreach(fun({Name,AFs}) ->
			    Dest = 
				filename:join(TempDir,atom_to_list(Name)++".erl"),
			    file:write_file(Dest,
					    map(fun(AF) ->
							[erl_pp:form(AF),"\n"]
						end, AFs))
		    end,AbsFormsList);
	false ->
	    ok
    end,
    
    %% Second phase in the compilation.  
    %% The Abstract Forms resulting from each module in the first phase
    %% are combined in a single Abstract Forms structure. This is then
    %% translated to a new one with pre-mCRL syntax.
    AbsForms = 
	%% Takes away the name of the module from the Abstract forms
	etopmcrl:forms(foldl(fun({_,AFs},RAFs) -> 
				     [AFs|RAFs]
			     end,[],AbsFormsList)),
    
    
    
    case lists:keysearch(file,1,Options) of 
	%% writes the pre-mCRL abstract forms to the TempDir if the option
	%% file was specified
	{value,{file,Temp}} -> 
	    Dest = filename:join(Temp,?PMCRLFile++".erl"),
	    file:write_file(Dest,
			    map(fun(AF) ->
					[erl_pp:form(AF),"\n"]
				end, AbsForms));
	false ->
	    ok
    end,
    
    %% Third phase in the compiler. 
    %% The pre-mCRL abstract forms are transformed to mCRL code and written to a file

    MCRLCode = pmcrltomcrl:forms(AbsForms,Options),
    MCRLFile = filename:join(DestDir,atom_to_list(Mod)++?MCRLExt),
    file:write_file(MCRLFile,MCRLCode),
    MCRLFile.

%% @doc
%% If no source and destination directories are specified, then the
%% current directory is taken by default as source directory and for
%% the destination directory the directory specified in the etomcrl.h
%% module
%% @end

supervisor(Mod,Fun,Args) ->
    supervisor("",?MCRLDir,Mod,Fun,Args,[]).

%% @doc
%% Script that generates the mCRL file from the Erlang source files
%% and then calls the mCRL tools to generate the corresponding LTS.
%% @end

instantiator(Mod,Fun,Args) ->
    MCRLFile = supervisor(Mod,Fun,Args),
    MCRLBase = filename:basename(MCRLFile),
    io:format("mCRL file written, now building transition diagram~n"),
    {ok,Here} = file:get_cwd(),
    file:copy(MCRLFile,?TempDir),
    file:set_cwd(?TempDir),
    io:format("~s",[os:cmd("mcrl -tbfile "++MCRLBase)]),
    io:format("~s",[os:cmd("instantiator "++MCRLBase)]),
    transitions:file(MCRLBase++".aut"),
    file:set_cwd(Here),
    os:cmd("cp "++filename:join(?TempDir,MCRLBase)++".aut .").

