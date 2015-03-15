%% Module: etoe_observe_messages
%% Author: Juanjo Sánchez <juanjo@dc.fi.udc.es>
%% Date: September 2003
%%
%% Plug-in for the etomcrl compiler
%%
%% In oder to install this plug-in in the etomcrl compiler: 
%%
%%     1) add a call to etoe_observe_messages:forms in the readprog/1
%%     function of etoe module
%%
%% @doc
%% 
%% introduces a delta (an action that never synchronizes) when the
%% message matches the given pattern while sybolically executing the code
%%
%% Source to source transformation for adding message checking
%%
%% Receives the implementation of a generic server. The list of abstract
%% forms can contain a set of observe_messages attributes:
%%
%% -observe_messages(message_type1,[{_,_,tag1}]).
%% -observe_messages(message_type2,[{_,tag2,_},{tag3,_,_,_}]).
%%
%% This lines are removed from the abstract forms
%%
%% A new function observe_messages_check/1 is added to the abstract
%% forms. This function receives a message and returns true if it
%% matches any of the patterns specified in the observe_messages
%% attribute
%%
%% All the reply messages in the handle_call functions are substituted
%% by:
%%  
%%   case observe_messages_check({PatternType,Message}) of
%%      true -> observe_messages:PatternType(Message)
%%      false -> {reply,Message,NewState}
%%
%% observe_messages module doesn't exist, what is used later in the
%% transformation to mcrl in order to create an action
%%
%% If no observe_messages patterns are specified, no changes are
%% performed on the abstract forms

-module(etoe_observe_messages).

-export([forms/1, file/1, file/2]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").

-define(ATT_NAME, observe_messages).
-define(ATT_NAME_SHOW, observe_messages_show).
-define(CHECK_FUN, observe_messages_check).

%% @spec forms([abs_form()]) ->
%%                        [abs_form()]
%%
forms(AbsForms) ->    
    %% All the abstract forms for observe_messages attribute 
    ObserveMessagesAttributeList = [{attribute,Line,?ATT_NAME, Expr}  || 
				       {attribute,Line,?ATT_NAME, Expr}<- AbsForms],

    %% All the pattern-messages for all the attributes in a single list
    ObserveMessages = [{MessageType,Pattern} || 				        
				       {attribute,Line2,?ATT_NAME,
					{MessageType,PatternList}}<- AbsForms,
				       Pattern <- PatternList],
    
    io:format(atom_to_list(?ATT_NAME) ++ " attributes: ~p~n",[ObserveMessages]),
    
    case ObserveMessages of
	[] -> % No patterns for messages-to-observe specified
	    AbsForms;
	_ -> % Let's introduce the changes for observing the messages
	    AbsFormsTemp = 
		map(fun(AbsForm) ->
			    introduce_message_checking(AbsForm) 
			    %% Introduce calls to the special checking
			    %% function in all the absforms
		    end,
		    lists:subtract(AbsForms,ObserveMessagesAttributeList)),
	    
	    %% We add the special function for handling the bottlenecks
	    AbsFormsTemp ++ [create_checking_function(ObserveMessages,0)]    
    end.

%% @spec file(filename()) -> [abs_form()]
%%
%% @doc
%%
%% Receives a filename (as a string) and returns the abstract form,
%% modified by forms/1
%%
%% Searches for the file in the current directory
 
file(FileName) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms).

%% @spec file(filename(),filename()) -> ok
%%
%% @doc
%%
%% Receives the source filename, reads the abstract forms and writes
%% them to a file after modifying using forms/1

file(Source,Dest) ->
    AbsForms = tl(file(Source)), % We remove -file from the abstract forms
    ok = 
	file:write_file(Dest, 
			map(fun(A) -> erl_pp:form(A) end, AbsForms)).

%%%%%%%%%%%%%%%%%%%%%%%%% Internal functions %%%%%%%%%%%%%%%%%%%%%%%%%

%% @spec introduce_message_checking (absform()) -> absform()
%% 
%% @doc
%%
%% Substitutes reply messages in a handle_call function by a call to
%% the checking function

introduce_message_checking({function,Line,handle_call,3,Clauses}) ->
    {function, Line, handle_call, 3, 
     map(fun(Clause) ->
		 introduce_checking_hcclauses(Clause)
	 end,Clauses)};

introduce_message_checking(Expr) ->
    Expr.

%% @spec introduce_checking_hcclauses ([absform()]) -> [absform()]
%% 
%% @doc
%%
%% Substitutes any occurrence of 
%%
%%   {reply,Message,NewState} 
%%
%% in the list of abstract forms, by 
%%  
%%   case observe_messages_check({PatternType,Message}) of
%%      true -> observe_messages:PatternType(Message)
%%      false -> {reply,Message,NewState}

introduce_checking_hcclauses(Expr) ->
    case Expr of
	Exprs when list(Exprs) ->
	    map(fun(E) -> introduce_checking_hcclauses(E) end,Exprs);
	
	{clause,Line,Pats,Guards,E} ->
	    {clause,Line,Pats,Guards,introduce_checking_hcclauses(E)};
	
	{tuple,Line,[{atom,L,reply},Message, NewState]} ->	    
	    {'case', L,  
	     {call, L, {atom,L,?CHECK_FUN}, [Message]},
	     [   
		 {clause, L,
		  [{tuple, L, [{atom,L,true},{var,L,'OM_MessageType'}]}],
		  [],
		  [{call, L, {atom,L,?ATT_NAME_SHOW},
		    [{var,L,'OM_MessageType'},Message]},
		   {tuple,Line,[{atom,L,reply},Message, NewState]}]},		 
		 {clause, L,
		  [{tuple, L, [{atom,L,false},{var,L,'_'}]}],
		  [], 
		  [{tuple,Line,[{atom,L,reply},Message, NewState]}]
		 }
		]
	    };
	
	{match,Line,E1,E2} ->
	    {match,Line,E1,introduce_checking_hcclauses(E2)};
	
	{'case',Line,E,Clauses} ->
	    {'case',Line,E,introduce_checking_hcclauses(Clauses)};
	
	{'if',Line,Clauses} ->
	    {'if',Line,introduce_checking_hcclauses(Clauses)};
	
	%% TODO: list comprehensions should also be considered, like records
	
	_ ->
	    Expr
    end.


%% @spec create_checking_function ([absform()],integer()) -> absform()
%%
%% @doc
%%
%% Receives a list of pattern expressions, and constructs the abstract
%% form of a new Erlang function that returns true for all the
%% messages matching with any pattern in the list and false in any
%% other case
     
create_checking_function(Exprs, Line) ->
    {function, Line, ?CHECK_FUN, 1, 
     [{clause, Line,
       [{var, Line, 'OM_Message'}],
	[],
	[{'case', Line,  	 
	  {var, Line,'OM_Message'},
	  build_clauses(Line,Exprs)
	 }]
       }
      ]
     }.

%% @spec build_clauses(Line::integer(),[string()]) -> [absform()] 
%%
%% @doc
%%
%% Line is introduced as line number for the new code that is going to
%% be created (the abstract form)
%%
%% String has the list of patterns that are going to be used to create
%% the clauses (they are going to be transformed in a list of abstract
%% forms)
%%
%% The following clauses are created:
%% 
%% (Msg1) -> true
%% (...) -> true
%% (Msgn) -> true
%% (_) -> false
%%
%% The new Erlang function is going to return false only if the
%% message received as argument doesn't pattern match with the list of
%% patterns specified in the original attribute

build_clauses(L,[]) ->
    [{clause, L,
      [{var,71,'_'}], % Pattern
      [], % Guards
      [{tuple, L, [{atom, L, false},{atom,L, notype}]}] % Body
     }];
build_clauses(L,[{MsgType,Msg}|Msgs]) ->
    [
     {clause, L,
      [parse(Msg)], % Pattern
      [], % Guard
      [{tuple, L, [{atom,L,true},{atom, L, MsgType}]}] % Body
     } 
    |build_clauses(L,Msgs)].

%% @spec parse(string()) -> absform()
%%
%% @doc
%% 
%% Transforms a string containing an Erlang term into its abstract
%% form, using erl_scan:string and erl_parse:parse_exprs.
%%
%% Direct parsing will not work, since erl_parse:term/1 does not
%% accept variables or underscore

parse(String) ->
    {ok,Tokens,_} = erl_scan:string(String++"."),
    {ok,[AbsForm]} = erl_parse:parse_exprs(Tokens),
    AbsForm.

