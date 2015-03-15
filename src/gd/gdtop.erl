-module(gdtop).

%%% External interface
-export([start/1, start/4, supertree/2,
	 new_graph/2]).

%%% Internal interface
-export([init/4, callback/2]).

-import(lists, [foldl/3
	       ]).


%%%================================================================
%%%
%%%	User Interface
%%%
-include("gd.hrl").
-include("gdtop.hrl").

start(CallBack) -> start(CallBack, [], #gdtop_options{}, #gd_options{}).

start(CallBack, UsersData, GDtop_options, GD_options) -> 
    spawn(?MODULE, init, [CallBack, UsersData, GDtop_options, GD_options]).

% added by Thomas (June 2001)
supertree(CallBack,UsersData) ->
    spawn(?MODULE, init, 
          [CallBack, UsersData,
           #gdtop_options{title = "Supervision Tree"},
           #gd_options{cyclic = false,
                       horizontal = false,
                       graph_font={screen,16}, algorithm=tree}]).
    
new_graph(Pid, Graph) when record(Graph, gd_graph) ->
    Pid ! {graph, Graph, self()}.


%%%================================================================
%%%
%%%	Internal records and macros
%%%

-define(empty_moving, {[],[]}).

%%% Graphical state
-record(g, 
	{pid_gd,
	 options,				% #gdtop_options{}
	 callback,
	 users_data,
	 rearrange=false,			% User may move things around
	 trace = #trace{},

	 %% Movement:
	 moving = ?empty_moving,		% Objects that are moving now
	 pos={0,0},				% last pointer pos
	 sum_move={0,0},			% total movment

	 %% Selection
	 selected_nodes = ordsets:new(),	% Objs which are selected
	 selected_arcs = ordsets:new(),	% Arc Objs which are selected
	 sel_area				% Used when selecting many
	}).

-define(user_option(G, Id), (G#g.options)#gdtop_options.Id).
	 
-define(opt2N(Rec,Opt), listpos(Opt, record_info(fields,Rec))+1).

%%%================================================================
%%%
%%%	Trace functions, macros and records
%%%

-record(trace, {
	  print_g = false,
	  print_unknown_events = false,
	  print_events = false,
	  print_callbacks = false,
	  print_call_user = false
	 }).

-define(print_trace(Format,Vals),
	io:format('~w ~w: ~s\n', [?MODULE,?LINE,io_lib:format(Format,Vals)])).

-define(set_trace_option(G,Id,Value),
	G#g{trace = setelement(?opt2N(trace,Id),G#g.trace,Value)}.
	
-define(trace_option(Id,G), (G#g.trace)#trace.Id).
-define(if_trace(Id,G,Expr), if  ?trace_option(Id,G)==true -> Expr;
				  true -> ok
			      end).
-define(print_if_trace(Id,G,Format,Vals),     
	?if_trace(Id,G,?print_trace(Format, Vals))).

%%%================================================================
%%%
%%%	Internal top functions
%%%

init(CallBack, UsersData, GDtop_options, GD_options) ->
    G = #g{options = GDtop_options,
	   callback = CallBack,
	   users_data = UsersData
	  },
    PidGD = create_main(G, GD_options),
    ?print_trace("gd pid = ~w", [PidGD]),
    link(PidGD),
    loop(G#g{pid_gd = PidGD}).

loop(bye) -> exit(bye);
loop(G) -> 
    ?print_if_trace(print_g, G, "loop/1 g=~p", [G]),
    loop(
      case receive
	       Event -> ?print_if_trace(print_events,G,
					'Event ~p\n', [Event]),
			Event
	   end of
%%%      receive
	  %% button clicks for gd
	  {gs,_,click,{check,Id},[_,_,_,V]} -> send_event({set_option,Id,V},G);
	  {gs,_,click,{radio,V},[_,_,Id|_]} -> send_event({set_option,Id,V},G);

	  {gs,_,click,refresh,_} -> send_event(refresh,G);
	  {gs,_,click,redraw,_} -> send_events([clear,refresh],G);

	  {gs,_,click,rearrange,[_,_,_,Value]} -> 
	      gs:config(select_m, {enable,Value}),
	      send_event({rearrange,Value}, G),
	      G#g{rearrange=Value};

	  {gs,_,click,{select,Which},_} -> send_event({select,Which}, G);

	  {gs,_,click,{trace,gd,Opt},[_,_,_,V]} -> send_event({trace,Opt,V},G);

	  %% button clicks for gdtop
	  {gs,_,click,{trace,gdtop,Id},[_,_,_,V]} -> ?set_trace_option(G,Id,V);

	  {gs,_,click,print,_} -> send_event(print,G);
	  {gs,_,click,exit,_} -> bye;
	  {gs,_,click,{help,hints},_} ->
	      gd_txtwin:pop_up_text_window(gs:read(win,id), 
					   "Help", 
					   {load,"gdtophelp.txt"}),
	      G;

	  %% "system"
	  {gs,_,configure,[],_} -> G;		% occurs on PCs !
	  {gs,_,configure,F,[W,H|_]} ->
	      gs:config(F,[{width,W},{height,H}]),
	      G;

	  {gs,win,destroy,_,_} -> bye;

	  %% Try our user:
	  
%	  {gs, Obj, click, Data, Args} ->
%	      case call_user({event, {gs,Obj,click,Data,Args}}, G) of
%		  {none, _} ->
%		      ?print_if_trace(print_unknown_events, G, 
%				      '*** got unknown event ~p\n', []),
%		      G;
%		  {ok, G1} ->
%		      G1
%	      end;

	  {callback, X, Pid} ->
	      ?print_if_trace(print_callbacks, G, "callback ~p", [X]),
	      {Answ, G1} = call_user(X,G),
	      Pid ! {callback_answer, Answ},
	      ?print_if_trace(print_callbacks, G, "callback ~p returned ~p", 
			      [X,Answ]),
	      G1;

	  Others ->
	      case 
		  case Others of
		      {gs,Obj,click,Data,Args} ->
			  case call_user({event,Others}, G) of
			      {ok, G1} -> {ok,G1};
			      _ -> {none,G}
			  end;
		      _ -> none
		  end of
		  {ok, G2} -> G2;
		  _ -> ?print_if_trace(print_unknown_events, G, 
				       '*** got unknown event ~p\n', [Others]),
		       G
	      end
      end).

%%%----------------------------------------------------------------
%%% 
send_event(Event, G) -> gd:event(Event,G#g.pid_gd), G.

send_events(Events, G) -> foldl(fun send_event/2, G, Events).

%%%----------------------------------------------------------------
%%% creates the main window

create_main(G, GD) ->
    Width = ?user_option(G,main_width),
    Height = ?user_option(G,main_height),
    Title =  ?user_option(G,title),
    WH = [{width,Width},{height,Height}],
    Win = gs:window(win,gs:start(),[{configure,true},{title,Title}|WH]),
    MB = menu_bar(?user_option(G,menubar_items), GD),
    PidGD = drawing_area(Win, gs:read(MB,height), G, GD),
    gs:config(win,[{data,packer},{map,true}]),
    gs:config(select_m, {enable,G#g.rearrange}),
    PidGD.
    

menu_bar(UserItems, GD) ->
    gs:create_tree(win,
		   [{menubar,mb,[],
		     [file_menu(), edit_menu(), options_menu(GD)] ++ 
		     UserItems ++ 
		     [help_menu(), trace_menu(), trace_step_button()]}]),
    gs:read(mb,id).

file_menu() ->
    {menubutton, [{label, {text,"File"}}],
     [{menu, [],
       [{menuitem, [{data,print}, {label,{text,"Print"}}]},
	{menuitem, [{data,exit}, {label,{text,"Exit"}}]}
       ]}]}.

edit_menu() ->
    {menubutton, [{label, {text,"Edit"}}],
     [{menu, [],
       [{menuitem, [{data,refresh}, {label,{text,"Refresh"}}]},
	{menuitem, [{data,redraw}, {label,{text,"Redraw"}}]},
	{menuitem, [{data,rearrange}, {label, {text,"Rearrange Manually"}},
		    {itemtype,check}]},
	{menuitem, select_m, [{label,{text,"Select"}}, {itemtype,cascade}],
	 [{menu,[],
	   [{menuitem,[{data,{select,all}},{label,{text,"Select All"}}]},
	    {menuitem,[{data,{select,none}},{label,{text,"De-select All"}}]}
	   ]}]}
       ]}]}.


		    
-define(selvO(Id,Val), if GD#gd_options.Id==Val -> [{select,true}];
			 true -> []
		      end).
-define(checkbO(Label,Id),
	{menuitem, [{label,{text,Label}}, {data,{check,Id}},{itemtype,check}
		    | ?selvO(Id,true)]}).
-define(radiobO(Label,Group,Id),
	{menuitem, [{label,{text,Label}}, {data,{radio,Id}},{itemtype,radio},
		    {group,Group} | ?selvO(Group,Id)]}).
options_menu(GD) ->
    {menubutton,[{label,{text,"Options"}}],
     [{menu,[],
       [?radiobO("Hierarchic Graph (Sugiyama)", algorithm, {graph,sugiyama}),
	?radiobO("Hierarchic Tree (Radack)", algorithm, tree),
	{menuitem, [{itemtype,separator}]},
	?checkbO("Horizontal",horizontal),
	?checkbO("Center root nodes",center_parents),
	?checkbO("Family style edges for trees",family_tree)
	]}]}.

-define(checkbT(Label,Where,Id),
	{menuitem, [{label,{text,Label}},{data,{trace,Where,Id}},
		    {itemtype,check}]}).
trace_menu() ->
    {menubutton, [{label,{text,"DEBUG"}},{side,right}],
     [{menu,[],
       [{menuitem, [{label,{text,"gdtop"}}, {itemtype,cascade}],
	 [{menu,[],
	   [?checkbT("Print g", gdtop, print_g),
	    ?checkbT("Print unknown events", gdtop, print_unknown_events),
	    ?checkbT("Print all events", gdtop, print_events),
	    ?checkbT("Print callbacks", gdtop, print_callbacks),
	    ?checkbT("Print call user", gdtop, print_call_user)
	   ]}]},
	{menuitem, [{label,{text,"gd"}}, {itemtype,cascade}],
	 [{menu,[],
	   [?checkbT("Print g", gd, print_g),
	    ?checkbT("Print unknown events", gd, print_unknown_events),
	    ?checkbT("Print most events", gd, print_most_events),
	    ?checkbT("Print all events", gd, print_events),
	    ?checkbT("Print call user", gd, print_call_user),
	    ?checkbT("Print digraph repr", gd, print_digraph_repr)
	   ]}]}
	]}]}.

trace_step_button() ->
    {menubutton, [{data,trace_step},{label,{text,"Step"}},
		  {buttonrelease,true},{enable,false},{side,right}]}.

help_menu() ->
    {menubutton, [{label, {text,"Help"}},{side,right}],
     [{menu, [],
       [{menuitem, [{data,{help,about}}, {label,{text,"About"}}]},
	{menuitem, [{data,{help,hints}}, {label,{text,"Some hints"}}]}
       ]}]}.

drawing_area(Win, HeightMenuBar, G, GD) ->
    WidthWin = gs:read(Win, width),
    HeightWin = gs:read(Win, height),
    Height = HeightWin - (HeightMenuBar+3),
    Width = WidthWin,
    Y = HeightMenuBar+3,
    Packer = gs:frame(packer,Win, [{y,Y},
				   {packer_x,[{stretch,1,50}]},
				   {packer_y,[{stretch,1,50},{fixed,25}]}]),
    Pid = gd:create(Packer, [{width,Width},{height,Height},{pack_xy,{1,1}}], 
		    GD, {?MODULE,callback}, self()),
    gs:config(packer, [{width,Width}, {height,Height}]),
    Pid.

%%%----------------------------------------------------------------
%%% calls from the graph drawer

callback(X, GDtopPid) ->
    GDtopPid ! {callback, X, self()},

    R = receive
	    {callback_answer, Answ} -> {Answ, GDtopPid}
	end,

%    R = case X of
%	    _ -> call_user(X, G)
%	end,
    R.


%%%----------------------------------------------------------------
%%% call the user program

call_user(X, G) -> call_user(X,G,none).

call_user(X, G, Default) ->
    {M,F} = G#g.callback,
    ?print_if_trace(print_call_user, G, "call_user ~w:~w(~w,~w)", 
		    [M,F,X,G#g.users_data]),
    Result = 
	case catch M:F(X) of
	    {'EXIT',_} ->
		case catch M:F(X,G#g.users_data) of
		    none -> {value(Default),G};
		    {none,UD} -> {value(Default), G#g{users_data=UD}};
		    {'EXIT',_} -> {value(Default),G};
		    {R,UD} -> {R,G#g{users_data=UD}}
		end;
	    none -> {value(Default),G};
	    R -> {R,G}
	end,
    ?if_trace(print_call_user, G,
	      case Result of
		  {'EXIT',_} -> 
		      ?print_trace("~w:~w(~w..) not handled)", [M,F,X]);
		  none -> ?print_trace("~w:~w(~w..) no answer)", [M,F,X]);
		  {Answ,_} -> ?print_trace("~w:~w(~w..) = ~w)", [M,F,X,Answ])
	      end),
    Result.

value(F) when function(F) -> F();
value(V) -> V.

%%%----------------------------------------------------------------
%%% Misc
    
listpos(Elem,L) -> length(lists:takewhile(fun(F) -> F =/= Elem end, L)) + 1.

