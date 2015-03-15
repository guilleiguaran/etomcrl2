%% @doc
%% <p>static analysis of application</p>
%%
%% <p>Thomas Arts. November 2000</p>
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

%% PRECOND:
%% 
%% Either:
%%
%% The name of the modulo where the supervision tree is defined, the
%% function that starts the supervision tree and its arguments. 
%% 
%% or
%%
%% The name of the file where the application is stored. The .app file
%% should be readable and the sources are either in ../src/ from the
%% directory in which .app is situated or in the same directory as
%% .app file.
%%
%% In both cases, the children of the supervision tree should be
%% linked to their supervisors (e.g., they are defined to be started
%% with the "start_link" function).

%% Potentially, the start function could call other auxiliar functions
%% before starting the process but, following the design principles,
%% these functions should not have side effects. However, these
%% functions are still translated in the current implementation
%% (i. e., they are not ignored as they should)

%% INVARIANTS:
%%
%% The Erlang semantics are preserved

%% 
%% POSTCOND:

%% Returns the information about all the processes started by the
%% supervision tree. In this information, the starting function and
%% the value of its arguments are included.
%% The info returned is as follows:
%%    - {supervisor,SupervisorName,Children}
%% where Children are either:
%%    - {Type,Name,{{Mod,Fun,Args},_,Behaviour,Opts}}
%%    - {Type,Name,{{Mod,Fun,Args},_,Behaviour}}
%% where Behaviour can be: gen_server, gen_fsm, gen_event or
%% worker
%% and Opts can be: [{started,[{Start,length(Args)}]}],
%% [{registered,Name},{started,[..]}


%% @end

-module(etoe_app).

-include("etomcrl.hrl").

-export([start/1,
         start/2,
         nonapp/3,
         nonapp/4,
         parse/2]).

-import(lists,[map/2]).

%% app:start(App) should be called instead
%%    of application:start(App)
%% be sure the .app file is readable and the sources are either in
%%    ../src/ from the directory in which .app is situated or
%%    in the same directory as .app file.
%%
%% app:nonapp(Mod,StartArgs) should be called instead
%%    of supervision:start_link(Mod,StartArgs)
%% be sure the Mod file and all calling sources are in present dir

start(Application) ->
    start([],Application).

start(IncludePath,Application) ->
    Directory =
	find_app(Application), % Finds out the directory in which the app is
    AppSpec =
	%% {application, Name, Spec} Spec is the standard way of specifying
	%% an Erlang application
	parse(Directory,Application),
    analyse_app(IncludePath,Directory,AppSpec).

%% nonapp/4
%%
%% The same as nonapp/3 but a working directory is given

nonapp(Dir,Module,Func,Args) ->
    {ok,CurrentDir} = file:get_cwd(),
    file:set_cwd(Dir),
    Result = nonapp(Module,Func,Args),
    file:set_cwd(CurrentDir),
    Result.

%% nonapp/3
%%
%% When no application is used in the source Erlang program, an
%% artificial unknown one is created to call analyse_to_sup/7 (this
%% way the same function is used both for the applications and for the
%% programs started as supervision trees)

nonapp(Module,Func,Args) ->
    analyse_to_sup([],".",{application,unknown,[]},top,Module,Func,Args).

%% analyse_app/3
%%
%% This function determines which module in the application spec is
%% specified as the one starting the program, and also which arguments
%% is using when starting the module. 
%%
%% The starting module name and arguments are included in the
%% application spec as follows:
%%
%%    {application, Application,
%%      [...
%%        {mod,          {Module, StartArgs}},
%%      ...]]

analyse_app(IncludePath,Dir,AppSpec) ->
    {application,Name,Spec} = AppSpec,
    case lists:keysearch(mod,1,Spec) of
	{value,{mod,{Mod,Arg}}} ->
	    {application,Name,
	     [analyse_to_sup(IncludePath,Dir,AppSpec,app_master,
			     Mod,start,[normal,Arg])]};
	_ ->
	    ?ERRORSTRING(["cannot determine start module"])
    end.

%% @doc
%%
%% analylse_to_sup/7
%% <dl>
%% <dt>IncludePath</dt>
%% </dl>

analyse_to_sup(IncludePath,Dir,AppSpec,SupName,Mod,Func,Args) ->
    %% the Mod:Func(Args) function should now evaluate
    %% to a process that is the top of the supervisor tree
    ?DEBUG("~p:~p/~p should lead to supervisor:start_link~n",
	[Mod,Func,length(Args)]),
  case readprog(IncludePath,Dir,Mod) of 
      %% return the AbsForms of the root of the supervision tree
       {ok,AbsForms} ->
         case evaluate(IncludePath,Dir,AppSpec,AbsForms,Func,Args) of
              {value,{supervisor,start_link,[M,A]},_} -> 
		 %% M is the module where the particular supervision
		 %% tree is defined and A are the arguments given to
		 %% the start_link
                {supervisor,SupName,analyse_sup(IncludePath,Dir,AppSpec,M,A)};
              {value,{supervisor,start_link,[SN,M,A]},_} ->
                {supervisor,SN,analyse_sup(IncludePath,Dir,AppSpec,M,A)};
              {value,ignore,_} ->
                {supervisor,ignored,[]};
              Other ->
                ?ERRORSTRING(["no supervisor started",Other])
         end;
       {error,Reason} ->
         ?ERRORSTRING(["parse_error module "++atom_to_list(Mod)++".erl", Reason])
  end.


analyse_sup(IncludePath,Dir,AppSpec,Mod,Arg) ->
  ?DEBUG("computing supervisor structure ~p:init(~p)~n",[Mod,Arg]),
  case readprog(IncludePath,Dir,Mod) of 
       {ok,AbsForms} ->
         % the Mod:init(Arg) function should evaluate to a
         % data structure describing the supervisor specification
         case catch evaluate(IncludePath,Dir,AppSpec,AbsForms,init,[Arg]) of
              {value,{ok,{{SupType,_,_},ChildSups}},_} -> 
                 map(fun(X)->   
                        analyse_worker(IncludePath,Dir,AppSpec,SupType,X)
                     end,ChildSups);
              Other ->
                ?ERRORSTRING(["supervisor wrong return value for init/1", Other])
         end;
       {error,Reason} ->
         ?ERRORSTRING(["parse_error module "++atom_to_list(Mod)++".erl", Reason])
  end.

analyse_worker(IncludePath,Dir,AppSpec,SupType,
               {Name,{Mod,Start,Args},Restart,_,supervisor,_}) ->
    %% The last argument describes a supervisor process. It is still
    %% not a worker, so we need to partially evaluate it again to
    %% extrat its children
  analyse_to_sup(IncludePath,Dir,AppSpec,Name,Mod,Start,Args);

analyse_worker(IncludePath,Dir,AppSpec,SupType,
               {Name,{Mod,Start,Args},Restart,_,worker,_}) ->
  ?DEBUG("computing worker ~p:~p/~p~n",[Mod,Start,length(Args)]),
  case readprog(IncludePath,Dir,Mod) of
       {ok,AbsForms} ->
        % case grepbehaviour(AbsForms) of
        %      none ->
        %        {SupType,Name,{{Mod,Start,Args},Restart,worker}};
        %      Behaviour ->
        % end 
        % THIS IS DANGEROUS, the function could loop infinitely
	  case catch evaluate(IncludePath,Dir,AppSpec,AbsForms,Start,Args) of
	      {value,{gen_server,start,[M,As,_]},_} -> 
		  %% workers should be linked to a supervisor
		  {SupType,Name,nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_server,start,[SName,M,As,_]},_} ->
		  %% workers should be linked to a supervisor
		  {SupType,checkname(Mod,Start,length(Args),Name,SName),
		   nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_server,start_link,[M,As,_]},_} ->
		  {SupType,Name,{{M,init,[As]},Restart,gen_server,
                 [{started,[{Start,length(Args)}]}
                 ]}};
	      %% Start (the variable with the name of the function that
	      %% starts the module) is added to the result as one of the
	      %% 'started' functions. This means that they are only used
	      %% before calling to the process initialisation. These
	      %% functions are going to be ignored in the translation.
             {value,{gen_server,start_link,[SName,M,As,_]},_} ->
               CheckedName = 
                 checkname(Mod,Start,length(Args),Name,SName),
               {SupType,CheckedName,
                {{M,init,[As]},Restart,gen_server,
                 [{registered,CheckedName},
                  {started,[{Start,length(Args)}]}
                 ]}};
	      {value,{gen_fsm,start,[M,As,_]},_} ->
		  {SupType,Name,nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_fsm,start,[SName,M,As,_]},_} ->
		  {SupType,checkname(Mod,Start,length(Args),Name,SName),
		   nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_fsm,start_link,[M,As,_]},_} ->
		  {SupType,Name,{{M,init,[As]},Restart,gen_fsm,
				 [{started,[{Start,length(Args)}]}
				 ]}};
	      {value,{gen_fsm,start_link,[SName,M,As,_]},_} ->
		  CheckedName = 
		      checkname(Mod,Start,length(Args),Name,SName),
		  {SupType,CheckedName,
		   {{M,init,[As]},Restart,gen_fsm,
                  [{registered,CheckedName},
                   {started,[{Start,length(Args)}]}
                  ]}};
	      {value,{gen_event,start,[]},_} ->
		  {SupType,Name,nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_event,start,[SName]},_} ->
		  {SupType,checkname(Mod,Start,length(Args),Name,SName),
		   nolink(Mod,Start,length(Args),Name)};
	      {value,{gen_event,start_link,[]},_} ->
		  {SupType,Name,{{gen_event,start_link,[]},Restart,gen_event}};
	      {value,{gen_event,start_link,[SName]},_} ->
		  CheckedName = 
		      checkname(Mod,Start,length(Args),Name,SName),
		  {SupType,CheckedName,
		   {{gen_event,start_link,[SName]},Restart,gen_event,
		    [{registered,CheckedName}]}};
	      {value,{spawn,As},_} ->
		  {SupType,Name,returntype_error(Mod,Start,length(Args),Name)};
	      {value,{spawn_link,As},_} ->
		  {SupType,Name,returntype_error(Mod,Start,length(Args),Name)};
	      {value,{ok,{spawn,[M,F,As]}},_} ->
		  {SupType,Name,nolink(Mod,Start,length(Args),Name)};
	      {value,{ok,{spawn,[Node,M,F,As]}},_} ->
		  {SupType,Name,nolink(Mod,Start,length(Args),Name)};
	      {value,{ok,{spawn_link,[M,F,As]}},_} ->
		  {SupType,Name,{{M,F,As},Restart,worker,
				 [{started,[{Start,length(Args)}]}
                 ]}};
	      {value,{ok,{spawn_link,[Node,M,F,As]}},_} ->
		  {SupType,Name,{{M,F,As},Restart,worker,
				 [{started,[{Start,length(Args)}]}
				 ]}};
	      Other ->
		  io:format("Unrecognized spawning: ~p~n",[Other]),
		  {SupType,Name,{{Mod,Start,Args},Restart,worker}}
	  end;
      {error,enoent} ->   % worker defined in other application
	  {SupType,Name,{{Mod,Start,Args},Restart,{worker,Mod}}};
      {error,Reason} ->
	  ?ERRORSTRING(["parse_error module "++atom_to_list(Mod)++".erl", Reason])
	      end.

%% @spec readprog(IncludePath::[string()],Dir::string(),Module::atom()) ->
%%               syntaxTree()
%%
%%                 syntaxTree() = erl_syntax:syntaxTree()
%%
%% @doc
%%
%% Reads the abstract forms from the file corresponding to the module
%% given as argument. It looks for the file in
%% <code>Dir++"../src"</code>, and if it is not there, in
%% <code>Dir</code>.
%%
%% @end

readprog(IncludePath,Dir,Module) ->
  File = atom_to_list(Module)++".erl",
  case file:read_file_info(filename:join([Dir,"../src",File])) of
       {ok,_} ->
         ?DEBUG("reading file ~p~n",[filename:join([Dir,"../src",File])]),
         NewDir=filename:join([Dir,"../src"]),
         epp:parse_file(filename:join([NewDir,File]),
                        [Dir,NewDir|IncludePath],[]);
       _ ->
         case file:read_file_info(filename:join([Dir,File])) of
              {ok,_} ->
                ?DEBUG("reading file ~p~n",[filename:join([Dir,File])]),
                epp:parse_file(filename:join([Dir,File]),[Dir|IncludePath],[]);
              Error ->
                ?DEBUG("eval mod "++File++" (~p)~n",[Error]),
                Error
         end
  end.

checkname(Mod,Start,Arity,Name,SName) ->
  case SName of
       Name ->
         Name;
       {local,Name} ->
         Name;
       {global,Name} ->
         Name;
       _ ->
         io:format("Warning: named worker ~p registered as ~p in "++
                   atom_to_list(Mod)++":"++
                   atom_to_list(Start)++"/"++
                   integer_to_list(Arity)++"~n",
                   [Name,SName]),
         SName
 end.

grepbehaviour([]) ->
  none;
grepbehaviour([{attribute,_,behaviour,Behaviour}|AbsForms]) ->
  Behaviour;
grepbehaviour([_|AbsForms]) ->
  grepbehaviour(AbsForms).

nolink(Mod,Start,Arity,Name) ->
  Reason = 
     io_lib:format("Error: ~p not linked to parent in "++ 
                   atom_to_list(Mod)++":"++
                   atom_to_list(Start)++"/"++
                   integer_to_list(Arity), [Name]),
  io:format("~s~n",[Reason]),
  {error,lists:flatten(Reason)}.

returntype_error(Mod,Start,Arity,Name) ->
  Reason = 
    io_lib:format(
       "Error: ~p started wrongly, returntype should be {ok,Pid} in "++
       atom_to_list(Mod)++":"++ atom_to_list(Start)++"/"++
       integer_to_list(Arity), [Name]),
  io:format("~s~n",[Reason]),
  {error,lists:flatten(Reason)}.


%% @spec evaluate(IncludePath::[string()], Dir::string(), AppSpec::appspec(), 
%%                AbsForms::syntaxTree(), Name::atom(), Arguments::[term()]) -> [Clauses]
%%
%%                  appspec() = {atom(),atom(),[term()]}
%%
%% @doc
%% This function extracts the clauses of the function which name,
%% Name, is given as a parameter and returns the value of the
%% variables present in the clauses.
%% @end

evaluate(IncludePath,Dir,AppSpec,AbsForms,Name,Arguments) ->
 
    %% First, the function handler that is going to be used for
    %% evaluating the supervision tree and getting the modules
    %% inplementing the workers, is defined
    LocalFunctionHandler =
	fun({io,format},Args,Bindings) ->
		{value,ok,Bindings};
	   ({M,F},Args,Bindings) ->
		case readprog(IncludePath,Dir,M) of
		    {ok,NewAbsForms} ->
			{value,V,Bs} = evaluate(IncludePath,Dir,AppSpec,
						NewAbsForms,F,Args),
			{value,V,Bindings};
		    _ -> % An application may have another application inside
			case {M,F,Args} of
			    {application,get_env,[Key]} ->
				{value,extract(AppSpec,Key),Bindings};
			    {application,get_env,[App,Key]} ->
				case AppSpec of
				    {application,App,Spec} ->
					{value,extract(AppSpec,Key),Bindings};
				    _ ->  % different application
					{value,apply(M,F,Args),Bindings} 
					%% apply returns the result of
					%% applying the function F in
					%% module M on Args
				end;
			    _ ->
				{value,apply(M,F,Args),Bindings}
			end
		end;
	   (F,Args,Bindings) when atom(F) ->
		{value,V,Bs} = evaluate(IncludePath,Dir,AppSpec,AbsForms,F,Args),
		{value,V,Bindings}
	end,
    %%
    case [ Body || {function,_,Fun,Arity,Body}<-AbsForms, 
		   Name==Fun, length(Arguments)==Arity ]          of
	%% The clauses of the function given as argument are extracted
	%% from the abstract forms of the module. The first time this
	%% function is called, the name of Fun is going to be 'start'
	%% for the applications and 'start_link' for the nonapp programs
	[ Clauses ] ->
	    etoe_eval:case_clauses(list_to_tuple(Arguments),
			      map(fun({clause,L,Ps,Gs,B}) ->
					  %% Hack needed because the
					  %% eval used is the one from
					  %% Erlang R7
					  {clause,L,[{tuple,L,Ps}],Gs,B}
				  end,Clauses),
			      [],{value,LocalFunctionHandler});
	Other -> % If the starting function is not in the abstract forms
	    exit({AbsForms,Other,"undefined function "++ atom_to_list(Name)++
		  "/"++integer_to_list(length(Arguments))})
    end.



%%%-----------------------------------------------------------


%% find_app/1 Calls find_app/2 with the application name plus the
%% right extension as the first argument, and the list of directories
%% configured in the system path (UNIX $PATH variable) as second
%% argument

find_app(AppName) ->
  find_app(atom_to_list(AppName)++".app",code:get_path()).

%% find_app/2 
%%
%% Auxiliar function used to find out in which of the directories
%% given as second argument (path to the files) is the file we are
%% looking for (first argument to the function)

find_app(File,[]) ->
  exit("cannot find "++File);
find_app(File,[Dir|Dirs]) ->
  case file:read_file_info(filename:join(Dir,File)) of
       {ok,Info} ->
          Dir;
       _ ->
         find_app(File,Dirs)
  end.

%% parse/2
%%
%% - Dir: The directory in which the app is string()
%% - Application: Atom with the name of the application atom()
%%
%% This function reads the app file and extracts its content
%% interpreted as an erlang term. Then, it calls check_app/3 with the
%% Term, the application name and the complete app filename

parse(Dir,Application) ->
  File = filename:join(Dir,atom_to_list(Application)++".app"),
  ?DEBUG("reading file ~p~n",[File]),
  case file:read_file(File) of
       {ok,Bin} ->
          case erl_scan:string(binary_to_list(Bin)) of
               {ok,Tokens,Line} ->
                 case erl_parse:parse_term(Tokens) of
                      {ok,Term} -> 
			 %% Term is the content of the app file
			 %% interpreted as an erlang term
                         check_app(Term,Application,File);
                      {error,ParseError} ->
                         exit({"error parsing file "++File,ParseError})
                 end;
               Error ->
                 exit({"error reading file "++File,Error})
          end;
       {error,Reason} ->
          exit({"error opening file "++File,Reason})
  end.

%% check_app/3
%%
%% - _Argument1: tuple with three elements that specifies an Erlang application
%% - Application: the name of the Erlang application
%% - File: the complete filename of the application
%%
%% This function checks if the application name given as a parameter
%% is the same as the one inside the tuple given as first argument

check_app({application,AppName,Spec},Application,File) ->
  {application,
     case AppName of
          Application ->
            AppName;
          _ ->
            ?WARNING(0,"name conflict ~p called ~p in ~p~n",
                     [Application,AppName,File]),
            Application
     end,
     Spec};
check_app(Other,Application,File) ->
  exit({"error in format "++File,Other}).

%% 
extract({application,_,Spec},Key) ->
  case lists:keysearch(env,1,Spec) of
       {value,{env,Vars}} ->
         case lists:keysearch(Key,1,Vars) of
              {value,{_,Value}} ->
                {ok,Value};
              _ ->
                ?WARNING(0,"application variable ~p undefined in .app file~n",
                         [Key]),
                undefined
         end;
       _ ->
         ?WARNING(0,"application variable ~p undefined in .app file~n",[Key]),
         undefined
  end.

