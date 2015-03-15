%% File    : gd.erl
%%% Author  : Hans Nilsson <hans@erix.ericsson.se>
%%% Purpose : 
%%% Created : 19 Mar 1998 by Hans Nilsson <hans@erix.ericsson.se>

-module(gd).
-author('hans@erix.ericsson.se').

%%% external interface
-export([create/5, 
	 request/2,
	 event/2]).

%%% interface for graph algorithms
-export([trim_edges/1,
	 node_WH/2,
	 draw_node/3]).

%%% internal interface
-export([init/5]).


-import(lists, [map/2, mapfoldl/3, foreach/2, filter/2, max/1, min/1,
		foldl/3]).

-import(ordsets, [new/0, from_list/1, 
		  is_element/2, add_element/2, del_element/2,
		  intersection/2, subtract/2]).

-import(gd_lib, [zip/1, zip/2, unzip/1,
		 minmax/1,
		 addD/2, addD/1,
		 subD/2,
		 divD/2,
		 mulD/2,
		 truncD/1,
		 meanD/1,
		 distance/2]).


%%%================================================================
%%%
%%%	User Interface
%%%

-include("gd.hrl").

%% creates a gs canvas and enters an event loop
create(GSparent, GeomSpec, Options, CallBack, UsersData) 
  when record(Options,gd_options) ->
    spawn(?MODULE, init, [GSparent,GeomSpec,Options,CallBack,UsersData]).


request(Request,To) ->
    To ! {request, Request, self()},
    receive
	{answer, Answer, To} -> Answer
    end.

event(Event, To) -> To ! {event,Event,self()}.

%%%================================================================
%%%
%%%	Internal records and macros
%%%

%%% things common with the different drawing algorithms
-include("gd_algs.hrl").

-define(empty_moving, {[],[]}).

%%% Graphical state
-record(g,
	{users_latest_graph = #gd_graph{},	% Practical at crashes
	 graph,					% digraph reference
	 del_objs = [],				% gs objects to delete at patch
	 new_objs = [],				% gs objects to be old at patch
	 wh_minmax,				% {Xmin,Xmax,Ymin,Ymax}
	 options = #gd_options{},
	 cyclic,
	 directed,

	 %% Movement:
	 moving = ?empty_moving,
	 pos={0,0},				% last pointer pos
	 sum_move={0,0},			% total movment

	 %% Selection
	 rearrange = false,			% Allow user layout change
	 selected_nodes = new(),	% Objs which are selected
	 selected_arcs = new(),	% Arc Objs which are selected

	 trace = #trace{},
	 callback,
	 users_data
	}).

%%% the visible counterpart of a vertex
-record(node, {
	  name,					% non-GS reference
	  shape,
	  unsel_attributes = [],		% save of attrs when selected
	  associated_objs = []			% OBJ of the label etc
	 }).

-record(label, {
	  name,					% non-GS reference
	  full_string,
	  short_string,
	  node_obj
	 }).

%%% the visible counterpart of an edge
-record(arc, {
	  obj,
	  arc,					% non GS reference
	  from_obj,				% GS reference
	  to_obj,				% GS reference
	  objs = []				% For line markers
	 }).

-define(opt2N(Rec,Opt), listpos(Opt, record_info(fields,Rec))+1).

-define(user_opt(G,Id), (G#g.options)#gd_options.Id).

-define(set_user_opt(G,Id,Value), 
	G#g{options = (G#g.options)#gd_options{Id = Value}}).

-define(set_user_opt_dyn(G,Id,Value),
	G#g{options = setelement(?opt2N(gd_options,Id),G#g.options,Value)}.

-define(user_opt_dyn(G,Id), element(?opt2N(gd_options,Id),G#g.options)).

-define(opt_from_user(G,Attr,Id), 
	call_user({Attr,Id},G,?user_opt(G,Attr))).

-define(opt_from_user_dyn(G,Attr,Id), 
	call_user({Attr,Id},G,?user_opt_dyn(G,Attr))).

-define(pi,3.14159).

%%% shapes
-record(rectangle_shape, {
	  angels_points = [],
	  posUL = {0,0},
	  center = {0,0}
	 }).

-record(polygon_shape, {
	  angels_points = [],
	  p1 = {0,0},
	  center = {0,0}
	 }).

-record(oval_shape, {
	  lx = {0,0},
	  ly = {0,0}
	 }).


%%%================================================================
%%%
%%%	Trace functions, macros and records
%%%
-record(trace, {
	  print_g = false,
	  print_unknown_events = false,
	  print_most_events = false,
	  print_events = false,
	  print_call_user = false,
	  print_digraph_repr = false
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

-define(print_digraph_repr(G),
	?print_if_trace(print_digraph_repr, G, 
			"---- Digraph ----\nVertices\n~p\nEdges\n~p\n",
			[map(fun(V) -> digraph:vertex(G#g.graph,V) end,
			     digraph:vertices(G#g.graph)),
			 map(fun(E) -> digraph:edge(G#g.graph,E) end,
			     digraph:edges(G#g.graph))])).

%%%================================================================
%%%
%%%	Internal top functions
%%%

init(GSparent, GeomSpec, Options, CallBack, UsersData) ->
    G = create_graph_canvas(GSparent, GeomSpec, #g{options = Options,
						   callback = CallBack,
						   users_data = UsersData}),
    event(refresh, self()),
    loop(G#g{options = Options}).

loop(G) ->
    ?print_if_trace(print_g, G, "g=~p", [G]),
    loop(
      case receive
	       Event when ?trace_option(print_events,G)==true -> 
		   ?print_trace('Event ~p', [Event]),
		   Event;

	       Event when ?trace_option(print_most_events,G)==true,
			  element(1,Event)==gs -> 
		   case element(3,Event) of
		       motion -> Event;
		       _ -> ?print_trace('Event ~p', [Event]), Event
		   end;

	       Event ->
		   Event
	   end of
%%%      receive
	  %% Motion
	  %% ------
	  %%     1: start moving the selected nodes
	  {gs,_,buttonpress,_,[3,X,Y|_]} when G#g.selected_nodes =/= [],
					      G#g.moving==?empty_moving ->
	      drag_move({X,Y}, G);

	  %% Select a group of nodes
	  %% -----------------------
	  {gs,canvas,buttonpress,_,[1,X,Y|_]} when G#g.rearrange == true ->
	      click(drag_selection_area({X,Y}), G);

	  %% Enter-Leave abbreviated nodes
	  %% -----------------------------
	  {gs,Obj,enter,L,_} when record(L,label) ->
	      gs:config(Obj, [{text,L#label.full_string}, raise]),
	      G;

	  {gs,Obj,leave,L,_} when record(L,label) ->
	      gs:config(Obj, {text,L#label.short_string}),
	      G;
	
	  %%% Others
	  %%% ------

	  {gs,canvas,motion,[],[X,Y|_]} -> G;	% skip

	  {event, {set_option,Opt,Value}, From} -> set_option(Opt,Value,G);
	  {event, {set_options,New}, From} -> set_options(New, G);
	  {event, refresh, From} -> refresh(G);
	  {event, clear, From} -> clear(G);
	  {event, {trace,Id,Value}, From} -> ?set_trace_option(G,Id,Value);

	  {event, {rearrange,Value}, From} -> G#g{rearrange=Value};
	  {event, {select,Which}, From} -> select(Which, G);

	  {request, get_options, From} -> answer(G#g.options,From,G);

	  {event, print, From} -> print_graph(G);

	  Others ->
	      ?print_if_trace(print_unknown_events, G, 
			      '*** got unknown event ~p\n',[Others]),
	      G
      end).

%%%================================================================
%%%
%%%	Internal help functions
%%%

%%%----------------------------------------------------------------
%%%
answer(Answer,To,G) ->
    To ! {answer,Answer,self()},
    G.

%%%----------------------------------------------------------------
%%%
set_options(New,  G) when record(New,gd_options) ->
    Old = G#g.options,
    Keys = record_info(fields, gd_options),
    L = zip([Keys, tl(tuple_to_list(Old)), tl(tuple_to_list(New))]),
    {OptsL,Action} =
	mapfoldl(
	  fun({{Key,O,N},A}) when O==N -> {O,A}; % no change
	     ({{algorithm,_,N},A}) -> {N,redraw};
	     ({{bg_color,_,N},A}) -> gs:config(canvas,{bg,N}), {N,A};
	     ({{_,_,N},A}) -> {N,A}		% no action at all, just save
	  end, no_redraw, L),
    Gnew = G#g{options=from_list([gd_options|OptsL])},
    case Action of
	redraw -> redraw(Gnew);
	_ -> Gnew
    end.

set_option(Opt,Value,G) ->
    case ?user_opt_dyn(G,Opt) of
	Value -> G;				% skip it (already set)
	_ -> ?print_trace('Changed option ~w to ~w\n', [Opt,Value]),
	     ?set_user_opt_dyn(G,Opt,Value)
    end.

%%%----------------------------------------------------------------
%%% selection handling

select(none, G) -> 
    click(G#g.selected_nodes, G);
select(all, G) -> %% select the ones that are not already selected
    NewObjs = subtract(from_list(get_all_type(node)),
			       G#g.selected_nodes),
    click(NewObjs, G).

click(Objs, G) when list(Objs) -> foldl(fun click/2, G, Objs);
click(Obj, G) ->    
    D = gs:read(Obj,data),
    Id = D#node.name,
    case is_element(Obj, G#g.selected_nodes) of
	true ->
	    gs:config(Obj, D#node.unsel_attributes),
	    G#g{selected_nodes = del_element(Obj,G#g.selected_nodes)};
	false ->
	    {Attr,G1} = ?opt_from_user(G,select_node_attributes,Id),
	    OldAttr = get_old_attrs(Attr, Obj),
	    gs:config(Obj, [{data,D#node{unsel_attributes=OldAttr}}
			    | Attr]),
	    G1#g{selected_nodes = add_element(Obj,G1#g.selected_nodes)}
    end.

get_old_attrs(L, Obj) ->
    map(fun({Attr,_}) ->
		{Attr, gs:read(Obj,Attr)}
	end, L).


drag_selection_area(Pos0) ->
    O = gs:rectangle(canvas, [{coords,[Pos0,addD(Pos0,{1,1})]},
			      {bw,1}, {fill,none},
			      {fg,orange}]),
    drag_selection_area(Pos0, O).

drag_selection_area(Pos0, O) ->
    receive
	{gs,canvas,motion,_,[X,Y|_]} ->
	    gs:config(O, {coords,[Pos0,{X,Y}]}),
	    drag_selection_area(Pos0, O);

	{gs,canvas,buttonrelease,_,[1,X,Y|_]} ->
	    gs:destroy(O),
	    Coords = case {X,Y} of
			 Pos0 -> Pos0;
			 Pos1 -> [Pos1, Pos0]
		     end,
	    HitObjs = gs:read(canvas,{hit,Coords}),
	    foldl(fun(Obj,S) ->
			  case type(Obj) of
			      node -> add_element(Obj,S);
			      label -> L = gs:read(Obj,data),
				       add_element(L#label.node_obj,S);
			      Other -> 
				  S
			  end
		  end, new(), HitObjs);

	{gs,_,_,_,_} ->
	    drag_selection_area(Pos0, O)
    end.

%%%----------------------------------------------------------------
%%% motion handling

drag_move(Pos0, G) ->
    {WholeArcs,PartsArcs} = arcs_to_move(G, G#g.selected_nodes),
    do_move(Pos0, {0,0},
	    G#g.selected_nodes++associated_objs(G#g.selected_nodes)++WholeArcs,
	    PartsArcs,
	    ?user_opt(G,horizontal)),
    G.

do_move(Pos0, Sum0, MoveWhole, MoveParts, Horizontal) ->
    receive
	{gs,_,motion,_,[X,Y|_]} ->
	    Pos = {X,Y},
	    Delta = subD(Pos, Pos0),
	    Sum = addD(Sum0, Delta),
	    foreach(fun(Obj) -> gs:config(Obj,{move,Delta}) end, MoveWhole),
	    foreach(fun({Obj,Spec})->
			    move_parts(Obj,Spec,Sum,Horizontal) 
		    end,MoveParts),
	    do_move(Pos, Sum, MoveWhole, MoveParts, Horizontal);

	{gs,_,buttonrelease,_,[3,X,Y|_]} ->
	    foreach(fun({Obj,Spec}) ->
			    trim_ends(Obj,Spec,Horizontal) 
		    end, MoveParts);

	{gs,_,_,_,_} ->
	    do_move(Pos0, Sum0, MoveWhole, MoveParts, Horizontal)
    end.

move_parts(Obj, Ps, Sum, Horizontal) ->
    NewCoords =
	case Ps of
	    [{fix,_},{move,_}]-> trim_ends_coords(Obj,Horizontal);
	    [{move,_},{fix,_}]-> trim_ends_coords(Obj,Horizontal);
	    _ ->
		map(fun({move,P}) -> addD(P,Sum);
		       ({fix,P}) -> P;
		       ({fix,x,{X,Y}}) -> {X,Y+element(2,Sum)};
		       ({fix,y,{X,Y}}) -> {X+element(1,Sum),Y};
		       (P) -> P
		    end, Ps)
	end,
    gs:config(Obj, {coords,NewCoords}).


trim_ends(Obj, [_,_], Horizontal) -> 
    gs:config(Obj, {coords,trim_ends_coords(Obj,Horizontal)});
trim_ends(Obj, _, _) -> 
    nyi.

trim_ends_coords(Obj, Horizontal) ->
    A = gs:read(Obj,data),
    From = A#arc.from_obj,
    To = A#arc.to_obj,
    start_end_point(From,To,Horizontal).
    

%%% Find wich lines to move and which ends to stay fix
arcs_to_move(G, SelectedNodeObjs) ->
    foldl(fun(O, Acc) ->
		  test_to_move_arc(O, SelectedNodeObjs, Acc, G)
	  end, {[],[]}, get_all_type(arc)).    

test_to_move_arc(O, SelectedNodeObjs, {WholeAcc,PartsAcc}, G) ->
    A = gs:read(O,data),
    From = A#arc.from_obj,
    To = A#arc.to_obj,
    ArcPoints = from_list([From,To|A#arc.objs]),
    case intersection(ArcPoints,SelectedNodeObjs) of
	[] -> %% Don't move anything on this line 
	    {WholeAcc,PartsAcc};

	ArcPoints -> %% Move the whole line
	    {[O|WholeAcc], PartsAcc};

	Move -> %% Move only parts of the line
	    Coords = gs:read(A#arc.obj, coords),
	    FromPos = hd(Coords),
	    ToPos = lists:last(Coords),
	    MiddlePoss = middle(Coords),
	    F = {aps(From,Move),FromPos},
	    T = {aps(To,Move),ToPos},
	    M = case false of %%?user_opt(G,family) of
		    false -> ms(MiddlePoss,A#arc.objs,SelectedNodeObjs);
		    true -> 
			XY = case ?user_opt(G,horizontal) of
				 true -> x;
				 false -> y
			     end,
			case is_element(From,Move) of
			    true ->
				[{fix,XY,hd(MiddlePoss)}, 
				 ms(tl(MiddlePoss),
				    A#arc.objs,SelectedNodeObjs)];
			    false ->
				case is_element(To,Move) of
				    true ->
					Ml = lists:last(MiddlePoss),
					[ms(MiddlePoss--[Ml],
					    A#arc.objs,SelectedNodeObjs),
					 {fix,XY,Ml}];
				    false ->
					ms(MiddlePoss,
					   A#arc.objs,SelectedNodeObjs)
				end
			end
		end,
	    {WholeAcc,
	     [{A#arc.obj, lists:flatten([F,M,T])}  |  PartsAcc]}
    end.

aps(Node, Selected) ->
    case is_element(Node,Selected) of
	true -> move;
	false -> fix
    end.

ms([Pos|Poss], [Node|Nodes], Selected) -> 
    [{aps(Node,Selected), Pos} | ms(Poss,Nodes,Selected)];
ms(Poss, _, _) -> 
    [{fix,Pos} || Pos <- Poss].

%%%----------------------------------------------------------------
%%%
print_graph(G) ->
    {ok,D} = file:open("graph.ps",write),
    io:format(D, '~s\n', [gd_ps:ps(canvas)]),
    file:close(D),
    G.

%%%----------------------------------------------------------------
%%%
redraw(G) -> refresh(clear(G)).

refresh(G) when G#g.graph==undefined ->		% new drawing
    case call_user(graph,G) of
	{Graph,G1} when record(Graph,gd_graph) -> 
	    G2 = new_drawing(Graph,G1),
	    G2#g{users_latest_graph = Graph};
	{X,_} -> 
	    msg("*** Bad user program reply on callback 'graph': ~w\n", [X]),
	    G
    end;

refresh(G) when G#g.graph=/=undefined ->	% update an existing drawing
    case call_user(graph,G) of
	{New,G1} when record(New,gd_graph) -> 
	    G2 = patch_old_graph(graph_diff(G1#g.users_latest_graph,New), G1),
	    G2#g{users_latest_graph = New};
		  
	{GraphUpdates,G1} when record(GraphUpdates,gd_graph_update) ->
	    G2 = patch_old_graph(GraphUpdates, G1),
	    G2#g{users_latest_graph = graph_union(G1#g.users_latest_graph,
						  GraphUpdates)}
    end.
                                                                                
-define(graph_option(Graph,Opt,G),
	case Graph#gd_graph.Opt of
	    true -> true;
	    false -> false;
	    _ -> ?user_opt(G,Opt)
	end).
		 
new_drawing(Graph, G0) ->
    G = G0#g{cyclic = ?graph_option(Graph,cyclic,G0),
	     directed = ?graph_option(Graph,directed,G0)
	    },
    Type = 
	if G#g.cyclic==true -> cyclic;
	   G#g.directed==false -> cyclic; % allow dual edges as repr.
	   true -> acyclic
	end,
    G1 = enter_new_graph(Graph, G#g{graph=digraph:new([protected,Type])}),
    ?print_digraph_repr(G1), 

%    Tg = digraph:new([protected,Type]),
%    foreach(fun(V) ->
%		    digraph:add_vertex(Tg,V)
%	    end, digraph:vertices(G1#g.graph)),
%    foreach(fun({V1,V2}) ->
%		    digraph:add_edge(Tg,{V1,V2},V1,V2,[])
%	    end, digraph:edges(G1#g.graph)),
%    io:format('CC: ~p\n', [cc:cc_components(Tg)]),
    
    case ?user_opt(G1,algorithm) of
	tree when G1#g.cyclic==false ->
	    SVs = start_vertices(tree, Graph#gd_graph.start_vertices, G1),
	    ?print_if_trace(print_digraph_repr,G1,"start_vertices=~p\n",[SVs]),
	    gd_alg_tree:design_new_tree(SVs,
					G1#g.graph,
					G1#g.options),
	    G2 = draw_levels_nodes(G1, old_node_attributes),
	    draw_arcs(G2, old_arc_attributes);

	tree -> 
	    msg("**** ERROR: can't use a tree algorithm for a cyclic graph\n",
		[]),
	    G1;

	{graph,sugiyama} ->
	    Opts = G1#g.options,
	    SVs = start_vertices(graph, Graph#gd_graph.start_vertices, G1),
	    gd_alg_sugiyama:design(
	      SVs,
	      G1#g.graph,
	      Opts#gd_options{cyclic=?graph_option(Graph,cyclic,G),
			      directed=?graph_option(Graph,directed,G)}),
	    %%	    trim_edges(G1),
	    ?print_digraph_repr(G1), 
	    G2 = draw_levels_nodes(G1, old_node_attributes),
	    G3 = draw_arcs(G2, old_arc_attributes),
	    G4 = delete_placeholders(G3),
	    ?print_digraph_repr(G1), 
	    G4;

	A -> 
	    msg('**** ERROR: algorithm ~w not implemented\n',[A]),
	    G1
    end.


start_vertices(tree, UsersStartVs, G) when G#g.directed==true ->
    InDegZero = all_in_degree(0, G#g.graph, digraph:vertices(G#g.graph)),
    UsersRealStartVs = all_in_degree(0, G#g.graph, UsersStartVs),
    case UsersRealStartVs of
	UsersStartVs -> ok;
	_ -> msg("*** Invalid start vertices in directed tree: ~p\n",
		 [UsersStartVs--UsersRealStartVs])
    end,
    UsersRealStartVs ++ (InDegZero--UsersRealStartVs);

start_vertices(graph, [], G) ->
    digraph:vertices(G#g.graph);

start_vertices(_, UsersStartVs, G) ->
    UsersStartVs.
    

all_in_degree(Degree, Graph, Vertices) ->
    filter(fun(V) -> 
		   digraph:in_degree(Graph,V) == Degree
	   end, Vertices).
    


patch_old_graph(GU, Ga) when record(GU,gd_graph_update) ->
    G = foldl(
	   fun(O,G0) -> 
		   case gs:read(O,data) of
		       D when record(D,node) ->
			   {Attrs,G01} =
			       ?opt_from_user(G0,old_node_attributes,
					      D#node.name),
			   gs:config(O, Attrs),
			   G01;
		       D when record(D,arc) ->
			   {_,_,_,E} = digraph:edge(G0#g.graph,D#arc.arc),
			   {Attrs,G01} =
			       ?opt_from_user(G0,old_arc_attributes,
					      {D#arc.arc,E#edge.level_diff}),
			   gs:config(O, Attrs),
			   G01;
		       _ ->
			   G0
		   end
	   end, Ga#g{new_objs=[]}, Ga#g.new_objs),

    %% Destroy all gs objects already marked as deleted:
    foreach(fun(O) -> gs:destroy(O) end, G#g.del_objs),

    Objs = gs:read(canvas,children),

    %% Mark the newly deleted edges and vertices as deleted:
    DelEdge = fun(Id,G00,D) ->
		      {Attrs,G01}=?opt_from_user(G00,del_arc_attributes,
						 {Id,D#edge.level_diff}),
		      gs:config(D#edge.obj, Attrs),
		      G01#g{del_objs=[D#edge.obj|G01#g.del_objs]}
	      end,
    G1 = foldl(
	   fun(Id,G0) ->
		   case digraph:edge(G0#g.graph, Id) of
		       {_,_,_,D} -> DelEdge(Id,G0,D);
		       false when G0#g.directed==false ->
			   {F,T} = Id,
			   case digraph:edge(G#g.graph,{T,F}) of
			       {_,_,_,D1} -> DelEdge({F,T},G0,D1);
			       false -> G0
			   end;
		       false ->
			   G0
		       end
	       end, G#g{del_objs=[]}, foldl(	% delete edges to/from the vs.
					fun(V,Acc) -> 
						digraph:in_edges(G#g.graph,V) ++ 
						    digraph:out_edges(G#g.graph,
								      V) ++ Acc
					end, GU#gd_graph_update.deleted_edges, 
					GU#gd_graph_update.deleted_vertices)),
    G2 = foldl(
	   fun(Id,G0) ->
		   case digraph:vertex(G#g.graph, Id) of
		       {_,D} -> 
			   {Attrs,G01}= ?opt_from_user(G0,
						       del_node_attributes,Id),
			   gs:config(D#vertex.node_obj, Attrs),
			   NodeObjs = [D#vertex.node_obj |
				       associated_objs(D#vertex.node_obj)],
			   G01#g{del_objs = NodeObjs ++ G01#g.del_objs};
		       false ->
			   G0
		   end
	   end, G1, GU#gd_graph_update.deleted_vertices),

    %%% update the digraph:
    foreach(fun(V) ->
		    digraph:add_vertex(G2#g.graph, V, #vertex{})
	    end, GU#gd_graph_update.new_vertices),

    foreach(
      fun({F,T}) ->
	      case digraph:edge(G2#g.graph,{F,T}) of
		  {_,_,_,D} -> 
		      case G2#g.directed of
			  false ->
			      case digraph:edge(G2#g.graph,{T,F}) of
				  false ->
				      digraph:add_edge(G#g.graph,{T,F}, T, F, 
						       #edge{type=reversed_copy});
				  _ -> ok
			      end;
			  true ->
			      ok
		      end;
		  false -> 
		      digraph:add_edge(G2#g.graph, {F,T}, F, T,
				       #edge{type=original}),
		      case G2#g.directed of
			  false ->
			      case digraph:edge(G2#g.graph,{T,F}) of
				  false ->
				      digraph:add_edge(G#g.graph,{T,F}, T, F, 
						       #edge{type=reversed_copy});
				  _ -> ok
			      end;
			  true ->
			      ok
		      end
	      end
      end, GU#gd_graph_update.new_edges),

    %% place the new vertices:
    gd_alg_patch:patch_place_new_vertices(
	   GU#gd_graph_update.new_vertices, G2#g.graph, G2#g.options, G2),
    trim_edges(G2#g.graph),

    %% draw the new edges:
    G4 = draw_arcs(G2, new_arc_attributes, GU#gd_graph_update.new_edges),

    %% and finally delete the edges and vertices that is gone:
    foreach(fun(Id) ->
		    case digraph:edge(G4#g.graph, Id) of
			{_,_,_,_} -> digraph:del_edge(G4#g.graph,Id);
			false when G4#g.directed==false ->
			   {F,T} = Id,
			   case digraph:edge(G4#g.graph,{T,F}) of
			       {_,_,_,_}-> digraph:del_edge(G4#g.graph,{T,F});
			       false -> ok
			   end;
		       false -> ok
		    end
	    end, GU#gd_graph_update.deleted_edges),

    foreach(fun(Id) ->
		    digraph:del_vertex(G4#g.graph,Id)
	    end, GU#gd_graph_update.deleted_vertices),


    G4#g{new_objs = gs:read(canvas,children) -- Objs}.




graph_diff(Old, New) ->
    DelVs = Old#gd_graph.vertices -- New#gd_graph.vertices,
    #gd_graph_update{
	    new_vertices = New#gd_graph.vertices -- Old#gd_graph.vertices,
	    deleted_vertices = DelVs,
	    new_edges = New#gd_graph.edges -- Old#gd_graph.edges,
	    deleted_edges = Old#gd_graph.edges -- New#gd_graph.edges --
		            [ {F,T} || {F,T} <- Old#gd_graph.edges,
				       (lists:member(F,DelVs) or
					lists:member(T,DelVs)) ]
	   }.

graph_union(Old, GU) ->
    #gd_graph{edges = from_list(Old#gd_graph.edges ++ 
				  GU#gd_graph_update.new_edges --
				  GU#gd_graph_update.deleted_edges),
	      vertices = from_list(Old#gd_graph.vertices ++ 
				     GU#gd_graph_update.new_vertices --
				     GU#gd_graph_update.deleted_vertices),
	      start_vertices = Old#gd_graph.start_vertices -- 
			       GU#gd_graph_update.deleted_vertices
	     }.


trim_edges(Graph) ->
    foreach(fun(E) ->
		    catch trim_one_edge_pair(E,Graph) 
	    end, digraph:edges(Graph)).

%% might cause exception badmatch
trim_one_edge_pair({F,F}, Graph) ->		% cycle, leave it
    ok;
trim_one_edge_pair({F,T}, Graph) ->
    E1 = {F,T},
    E2 = {T,F},
    {_,_,_,D1} = digraph:edge(Graph,E1),	% this might fail if the
    {_,_,_,D2} = digraph:edge(Graph,E2),	% .. copy is deleted already
    case {D1#edge.type, D2#edge.type} of
	{placed,placed} -> keep_both;
	{placed,_} -> digraph:del_edge(Graph,E2);
	{_,placed} -> digraph:del_edge(Graph,E1);
	{original,_} -> digraph:del_edge(Graph,E2);
	_ -> digraph:del_edge(Graph,E1)
    end.
	      

%%%----------------------------------------------------------------
clear(G) -> 
    foreach(fun(O) -> gs:destroy(O) end, gs:read(canvas,children)),
    case G#g.graph of
	undefined -> ok;
	Ref -> digraph:delete(Ref)
    end,
    G#g{users_latest_graph = #gd_graph{},
	graph = undefined,
	selected_nodes = [],
	moving=?empty_moving,
	del_objs = []
       }.

%%%----------------------------------------------------------------
%%%
enter_new_graph(Graph, G) ->
    {WHs,G1} = 
	foldl(
	  fun(Id,{WHs0,G0}) ->
		  {ShortString,FullString,G01} = name_string(Id, G0),
		  WH = node_WH(ShortString, ?user_opt(G01,graph_font)),
		  digraph:add_vertex(G#g.graph, Id,
				     #vertex{wh = WH,
					     short_string= ShortString,
					     full_string= FullString}),
		  {[WH|WHs0],G01}
	  end, {[{0,0}],G}, Graph#gd_graph.vertices),
    G2 = G1#g{wh_minmax = minmax(WHs)},

    foreach(
      fun({F,T}) ->
	      case digraph:edge(G2#g.graph,{F,T}) of
		  {_,_,_,D} when D#edge.type==original -> ok;
		  {_,_,_,D} when D#edge.type==placed -> ok;
		  _ -> digraph:add_edge(G2#g.graph, {F,T}, F, T,
					#edge{type=original}),
		       case G2#g.directed of
			   false ->
			       case digraph:edge(G2#g.graph,{T,F}) of
				   false ->
				       digraph:add_edge(G#g.graph,{T,F}, T, F, 
							#edge{type=
							      reversed_copy});
				   _ -> ok
			       end;
			   true ->
			       ok
		       end
	      end
      end, Graph#gd_graph.edges),
    G2.

%%%----------------------------------------------------------------
%%%

draw_levels_nodes(G, AttrName) ->
    Names = digraph:vertices(G#g.graph),
    LevelStarts = level_starts(Names,G),
    {Wmin,Wmax,Hmin,Hmax} = G#g.wh_minmax,
    P0 = {Wmax,Hmax},
    foldl(
      fun(Name,G0) ->
	      {_,D} = digraph:vertex(G#g.graph,Name),
	      {value, {_,LevelStart}} = lists:keysearch(D#vertex.level,1,
							LevelStarts),
	      XY = levels_pos_to_xy(D#vertex.level, D#vertex.level_pos, 
				    LevelStart, G0),
	      draw_node(Name, addD(P0,XY), G, AttrName)
      end, G, Names).


level_starts(Names, G) ->
    level_starts(
      lists:sort(map(fun(Name) ->
			     {_,D} = digraph:vertex(G#g.graph, Name),
			     {D#vertex.level, D#vertex.wh}
		     end, Names)),
      0, {0,0}, []).

level_starts([{Lev,WH}|T], Lprev, Sum, WHacc) when Lev==Lprev ->
    level_starts(T, Lev, Sum, [WH|WHacc]);

level_starts([{Lev,WH}|T], Lprev, LevelStart, WHacc) when Lev=/=Lprev ->
    {Wmin,Wmax,Hmin,Hmax} = minmax(WHacc),
    NextLevelStart = addD([?level_separation,LevelStart,{Wmax,Hmax}]),
    [{Lprev,LevelStart} | level_starts(T, Lev, NextLevelStart, [WH])];

level_starts([], Lprev, Sum, WHacc) ->
    [{Lprev,Sum}].

    
levels_pos_to_xy(Level, PosInLevel, {X0,Y0}, G) ->
    case ?user_opt(G,horizontal) of
	true -> {X0, round(PosInLevel)};
	false-> {round(PosInLevel), Y0}
    end.

%%%----
node_WH(String, Font) ->
    addD(gs:read(canvas, {font_wh,{Font,String}}),{6,3}).

%%%----
draw_node(Id, Pos, G) -> 
    draw_node(Id, Pos, G, new_node_attributes).

draw_node(Id, Pos, G, AttrName) ->
    {Attr,G0} = ?opt_from_user_dyn(G,AttrName,Id),
    {Shape,G1} = ?opt_from_user(G0,shape,Id),
    {LabelObj,WH,LabelData,G2,NodePos} = make_label(Id,Pos,G1),
    {FinalShape, NodeObj} = draw_node(Shape, Id, WH, NodePos, G2),
    gs:config(LabelObj, [raise,{data, LabelData#label{node_obj=NodeObj}}]),
    gs:config(NodeObj, lists:flatten(
			 [Attr,
			  {data,#node{name=Id,
				      shape=FinalShape,
				      associated_objs=[LabelObj]}}])),
    {_,D} = digraph:vertex(G#g.graph,Id),
    digraph:add_vertex(G#g.graph, Id, D#vertex{node_obj=NodeObj}),
    G2.
    
draw_node(oval, Id, WH, Pos, G) ->
    {X1,Y1} = PosUpperLeft = subD(Pos,{5,5}),
    {X2,Y2} = PosLowerRight = addD([PosUpperLeft,WH,{6,3},{10,10}]),
    Lx = (X2-X1) / 2, %% The ellipses axis
    Ly = (Y2-Y1) / 2,
    {#oval_shape{lx=Lx,
		 ly=Ly		},
     gs:oval(canvas,[{coords,[PosUpperLeft,PosLowerRight]}])};

draw_node(rectangle, Id, WH, Pos, G) ->
    {X1,Y1} = PosUpperLeft = Pos,
    {X2,Y2} = PosLowerRight = addD([PosUpperLeft,WH,{6,3}]),
    Polygon = [{X1,Y1}, {X2,Y1}, {X2,Y2}, {X1,Y2}],
    Center = meanD(Polygon),
    Angles = map(fun(P) -> angel(Center,P) end, Polygon),
    {#rectangle_shape{angels_points = lists:sort(zip(Angles,Polygon)),
		      posUL = PosUpperLeft,
		      center = Center},
     gs:rectangle(canvas,[{coords,[PosUpperLeft,PosLowerRight]}])};

draw_node({polygon,Points}, Id, WH, Pos, G) ->
    Center = meanD(tl(Points)),
    Delta = subD(Pos, Center),
    Coords = map(fun(P) -> addD(P,Delta) end, Points),
    Angles = map(fun(P) -> angel(Center,P) end, tl(Points)),
    {#polygon_shape{angels_points=lists:sort(zip(Angles,tl(Points))),
		    p1=hd(Points),
		    center=Center},
     gs:polygon(canvas, [{coords,Coords}])};

draw_node(Shape, Id, WH, Pos, G) ->
    ?print_trace("Unknown Shape: ~w", [Shape]),
    draw_node(rectangle, Id, WH, Pos, G).


make_label(Id, CenterPos, G) ->
    {ShortString,FullString,G1} = name_string(Id, G),
    {W,H}=WH= gs:read(canvas,{font_wh, {?user_opt(G,graph_font),ShortString}}),
    NodePos = case ?user_opt(G,horizontal) of
		  true -> subD(CenterPos, {0,H div 2});
		  false-> subD(CenterPos, {W div 2,0})
	      end,
    PosUpperLeft = addD(NodePos, {3,2}),
    UseEnterLeave = ShortString =/= FullString,
    Data = #label{name=Id,
		  short_string=ShortString,
		  full_string=FullString},
    Obj = gs:text(canvas, [{coords,[PosUpperLeft]}, {text,ShortString},
			   {enter,UseEnterLeave},{leave,UseEnterLeave},
			   {data, Data}]),
    {Obj,WH,Data,G1,NodePos}.
    

name_string(Name,G) ->
    DefaultFun = fun() when atom(Name) -> atom_to_list(Name);
		    () -> case catch from_list(Name) of
			      A when atom(A) -> Name;
			      _ -> io_lib:write(Name)
			  end
		 end,

    case call_user({name_string,Name},G,DefaultFun) of
	{String, G1} -> {String, String, G1};
	{ShortString,FullString,G1} -> {ShortString,FullString,G1}
    end.
	     

%%%----------------------------------------------------------------
%%%
draw_arcs(G) -> 
    draw_arcs(G, new_arc_attributes).

draw_arcs(G, AttrName) -> 
    draw_arcs(G, AttrName, digraph:edges(G#g.graph)).

draw_arcs(G, AttrName, Edges0) ->
    Edges = collect_make_long_arcs(Edges0, G),
    set_level_differences(G,Edges),
    ?print_digraph_repr(G), 
    foldl(fun(E,G0) ->
		  {_,_,_,D} = digraph:edge(G0#g.graph,E),
		  LineAttrs = case G#g.directed of
				  true -> [{arrow,D#edge.arrow_place}];
				  false -> []
			      end,
		  case D#edge.obj of
		      undefined -> 
			  {Attr,G1} = 
			      ?opt_from_user_dyn(G0, AttrName, 
						 {E,D#edge.level_diff}),
			  draw_arc(E,G1,Attr++LineAttrs);
		      _ -> 
			  G0
		  end
	  end, G, Edges).


set_level_differences(G, Edges) ->
    foreach(
      fun(E) ->
	      {_,F,T,D} = digraph:edge(G#g.graph,E),
	      {_,Df} = digraph:vertex(G#g.graph,F),
	      {_,Dt} = digraph:vertex(G#g.graph,T),
	      LevelDiff = 
		  case catch (Dt#vertex.level-Df#vertex.level) of
		      I when integer(I) -> I;
		      _ -> undefined
		  end,
	      digraph:add_edge(G#g.graph,E,F,T,D#edge{level_diff=LevelDiff})
      end, Edges).
    

delete_placeholders(G) ->
    foreach(
      fun(?placeholder(N)) -> 
	      {_,D} = digraph:vertex(G#g.graph, ?placeholder(N)),
	      D1 = gs:read(D#vertex.node_obj, data),
	      foreach(fun(O) -> gs:destroy(O) end,
		      [D#vertex.node_obj | D1#node.associated_objs]),
	      digraph:del_vertex(G#g.graph, ?placeholder(N));
	 (_) ->
	      keep
      end, digraph:vertices(G#g.graph)),
    G.


collect_make_long_arcs(Edges0, G) ->
    foldl(
      fun({?placeholder(_),_}, Es) -> 
	      Es;

	 ({N1,?placeholder(N2)}, Es) ->
	      ?print_trace("long arc ~p -> ~p -> ...", [N1,?placeholder(N2)]),
	      NamesRev = follow_long_arc(?placeholder(N2), G, [N1]),
	      Names = lists:reverse(NamesRev),
	      Nhead = hd(Names),
	      Ntail = hd(NamesRev),
	      Edge = {Nhead,Ntail},
	      digraph:add_edge(G#g.graph, Edge, Nhead, Ntail,
			       #edge{type=placed, 
				     long_names=tl(Names)--[Ntail]}),
	      [Edge |Es];

	 (_,Es) -> 
	      Es
      end, Edges0, Edges0).


draw_arc({?placeholder(_),_}, G, Attr) -> 
    G;

draw_arc({_,?placeholder(_)}, G, Attr) -> 
    G;

draw_arc({Name,Name}, G, Attr) ->
    ?print_trace("~p to itself", [Name]),
    {_,Dv} = digraph:vertex(G#g.graph, Name),
    NodeObj = Dv#vertex.node_obj,
    Do = gs:read(NodeObj,data),
    case Do#node.shape of
	S when record(S,rectangle_shape) ->
	    Coords = self_ref_coords_rect(gs:read(NodeObj,coords), G),
	    Obj = gs:line(canvas, [{coords,Coords},{smooth,true},lower
				   | Attr]),
	    Edge = {Name,Name},
	    gs:config(Obj, [{data,#arc{arc = Edge,
				       obj = Obj,
				       from_obj = NodeObj,
				       to_obj = NodeObj}}]),
	    {_,_,_,D} = digraph:edge(G#g.graph, Edge),
	    digraph:add_edge(G#g.graph, Edge, Name, Name, 
			     D#edge{obj = Obj});
	    
	Shape ->
	    ?print_trace("can't make self ref arc for ~p", [Shape])
    end,
     G;

draw_arc(Edge, G, Attr) ->
    {_,_,_,D} = digraph:edge(G#g.graph,Edge),
    Alg = ?user_opt(G,algorithm),
    case D#edge.long_names of
	undefined when D#edge.type==placed, 
		       Alg==tree,
		       ?user_opt(G,family_tree)==true ->
	    draw_family_arc(Edge, G, Attr);

	undefined -> 
	    draw_straight_arc(Edge, G, Attr);

	Names when list(Names) ->
	    draw_long_arc(Edge, G, Attr)
    end.
					       

follow_long_arc(?placeholder(N1), G, Acc) ->
    [N2] = digraph:out_neighbours(G#g.graph, ?placeholder(N1)),
    follow_long_arc(N2, G, [?placeholder(N1)|Acc]);

follow_long_arc(N1, G, Acc) ->
    [N1|Acc].


draw_family_arc({NameFrom,NameTo}, G, Attr) ->
    {_, DataF} = digraph:vertex(G#g.graph, NameFrom),
    {_, DataT} = digraph:vertex(G#g.graph, NameTo),
    Edge = {NameFrom,NameTo},
    {XFmin,XFmax,YFmin,YFmax} = minmax(gs:read(DataF#vertex.node_obj,coords)),
    {XTmin,XTmax,YTmin,YTmax} = minmax(gs:read(DataT#vertex.node_obj,coords)),
    Coords =
	case ?user_opt(G,horizontal) of
	    false-> Xf = XFmin + ((XFmax-XFmin) div 2),
		    Yf = YFmax,
		    Xt = XTmin + (XTmax-XTmin) div 2,
		    Yt = YTmin,
		    Ym = Yf + (Yt-Yf) div 2,
		    [{Xf,Yf}, {Xf,Ym}, {Xt,Ym}, {Xt,Yt}];
	    true -> Xf = XFmax,
		    Yf = YFmin + (YFmax-YFmin) div 2,
		    Xt = XTmin,
		    Yt = YTmin + (YTmax-YTmin) div 2,
		    Xm = Xf + (Xt-Xf) div 2,
		    [{Xf,Yf}, {Xm,Yf}, {Xm,Yt}, {Xt,Yt}]
	end,
    Obj = gs:line(canvas, [{coords,Coords}|Attr]),    
    gs:config(Obj, {data,#arc{arc = Edge,
			      obj = Obj,
			      from_obj = DataF#vertex.node_obj,
			      to_obj = DataT#vertex.node_obj}}),
    {_,_,_,D} = digraph:edge(G#g.graph, Edge),
    digraph:add_edge(G#g.graph, Edge, NameFrom, NameTo, 
		     D#edge{obj = Obj}),
    G.

draw_straight_arc({NameFrom,NameTo}, G, Attr) ->
    {_, DataF} = digraph:vertex(G#g.graph, NameFrom),
    {_, DataT} = digraph:vertex(G#g.graph, NameTo),
    Edge = {NameFrom,NameTo},
    Obj = gs:line(canvas, [{coords, start_end_point(DataF#vertex.node_obj,
						    DataT#vertex.node_obj,
						    ?user_opt(G,horizontal))},
			   lower | Attr]),
    gs:config(Obj, [{data,#arc{arc = Edge,
			       obj = Obj,
			       from_obj = DataF#vertex.node_obj,
			       to_obj = DataT#vertex.node_obj}}]),
    {_,_,_,D} = digraph:edge(G#g.graph, Edge),
    digraph:add_edge(G#g.graph, Edge, NameFrom, NameTo, 
		     D#edge{obj = Obj}),
    G.

draw_long_arc(Edge, G, Attr) ->
    {NameFrom,NameTo} = Edge,
    {_, DataF} = digraph:vertex(G#g.graph, NameFrom),
    {_, DataT} = digraph:vertex(G#g.graph, NameTo),
    {_,_,_,D} = digraph:edge(G#g.graph, Edge),
    MiddleNames = D#edge.long_names,
    {_, DataF1} = digraph:vertex(G#g.graph, hd(MiddleNames)),
    {_, DataT1} = digraph:vertex(G#g.graph, lists:last(MiddleNames)),
    Names = [NameFrom | MiddleNames] ++ [NameTo],
    MiddleCoords = 
	map(fun(V) ->
		    {_,D1} = digraph:vertex(G#g.graph, V),
		    {_,C,_} = node_data(D1),
		    C
		 end, MiddleNames),
    [CoordF,_] = start_end_point(DataF,DataF1,?user_opt(G,horizontal)),
    [_,CoordT] = start_end_point(DataT1,DataT,?user_opt(G,horizontal)),
    Coords = [CoordF | MiddleCoords] ++ [CoordT],
    Obj = gs:line(canvas, [{coords, Coords},{smooth,true}, lower | Attr]),
    gs:config(Obj, [{data,#arc{arc = Edge,
			       obj = Obj,
			       from_obj = DataF#vertex.node_obj,
			       to_obj = DataT#vertex.node_obj
			      }}]),
    digraph:add_edge(G#g.graph, Edge, NameFrom, NameTo, 
		     D#edge{obj = Obj}),
    G.


%%%----------------
start_end_point(ObjF, ObjT, Horizontal) ->
    start_end_point1(node_data(ObjF), node_data(ObjT), Horizontal).

start_end_point1({ShapeF,_,CoordsF}, 
		 {ShapeT,_,CoordsT},
		 Horizontal) when record(ShapeF,rectangle_shape),
				  record(ShapeT,rectangle_shape) ->
    Cf = side_pos(f,Horizontal,CoordsF),
    Ct = side_pos(t,Horizontal,CoordsT),
    [Cf,Ct];

start_end_point1({ShapeF,_,CoordsF}, {ShapeT,Ct,_},
		 Horizontal) when record(ShapeF,rectangle_shape) ->
    Cf = side_pos(f,Horizontal,CoordsF),
    AlphaF = angel(Cf,Ct),
    AlphaT = case (AlphaF + ?pi) of
		 A when A<2*?pi -> A;
		 A -> A-2*?pi			% 0=<A A<3*?pi
	     end,
    [Cf, truncD(intersect(Ct,AlphaT,ShapeT,Cf))];

start_end_point1({ShapeF,Cf,_}, {ShapeT,_,CoordsT},
		 Horizontal) when record(ShapeT,rectangle_shape) ->
    Ct = side_pos(t,Horizontal,CoordsT),
    AlphaF = angel(Cf,Ct),
    AlphaT = case (AlphaF + ?pi) of
		 A when A<2*?pi -> A;
		 A -> A-2*?pi			% 0=<A A<3*?pi
	     end,
    [truncD(intersect(Cf,AlphaF,ShapeF,Ct)), 
     Ct];

start_end_point1({ShapeF,Cf,CoordsF}, {ShapeT,Ct,CoordsT}, Horizontal) ->
    AlphaF = angel(Cf,Ct),
    AlphaT = case (AlphaF + ?pi) of
		 A when A<2*?pi -> A;
		 A -> A-2*?pi			% 0=<A A<3*?pi
	     end,
    [truncD(intersect(Cf,AlphaF,ShapeF,Ct)), 
     truncD(intersect(Ct,AlphaT,ShapeT,Cf))].

node_data(D) when record(D,vertex) -> node_data(D#vertex.node_obj);
node_data(Obj) ->
    N = gs:read(Obj,data), 
    Coords = gs:read(Obj,coords),
    C = center(N#node.shape,Coords),
    {N#node.shape,C,Coords}.

center(S,Coords) when record(S,polygon_shape) -> 
    addD(S#polygon_shape.center, subD(hd(Coords),S#polygon_shape.p1));

center(_, Coords) -> meanD(Coords).



side_pos(f,true,[{Xul,Yul},{Xlr,Ylr}])  -> {Xlr, (Yul+Ylr) div 2};
side_pos(t,true,[{Xul,Yul},{Xlr,Ylr}])  -> {Xul, (Yul+Ylr) div 2};
side_pos(f,false,[{Xul,Yul},{Xlr,Ylr}]) -> {(Xul+Xlr) div 2, Ylr};
side_pos(t,false,[{Xul,Yul},{Xlr,Ylr}]) -> {(Xul+Xlr) div 2, Yul}.


intersect(Origo, Alpha, {polygon,AngelsPoints,_,Center}, Pt) ->
    {Pt1,Pt2} = find_line(Alpha, AngelsPoints),
    Delta = subD(Origo,Center),
    Lp1 = addD(Delta,Pt1),
    Lp2 = addD(Delta,Pt2),
    case line_intersect(Lp1,Lp2, Origo,Pt) of
	none -> Origo;
	P -> P
    end;
intersect(Origo, Alpha, S, Pt) when record(S,rectangle_shape) ->
    {Pt1,Pt2} = find_line(Alpha, S#rectangle_shape.angels_points),
    Delta = subD(Origo,S#rectangle_shape.center),
    addD(meanD([Pt1,Pt2]), Delta);
intersect({X0,Y0}, Alpha, S, Pt) when record(S,oval_shape) ->
    X = X0 + S#oval_shape.lx*math:cos(Alpha),
    Y = Y0 + S#oval_shape.ly*math:sin(Alpha),
    {round(X),round(Y)};
intersect(P, _, _, _) ->
    P.


%%%----------------
rect_middle_side(ObjF, ObjT) ->
    [{Xful,Yful},{Xflr,Yflr}] = gs:read(ObjF,coords),
    [{Xtul,Ytul},{Xtlr,Ytlr}] = gs:read(ObjT,coords),
    Hf2 = (Yflr-Yful) div 2,
    Ht2 = (Ytlr-Ytul) div 2,
    Wf2 = (Xflr-Xful) div 2,
    Wt2 = (Xtlr-Xtul) div 2,
    if
        Xflr < Xtul -> [{Xflr, Yful+Hf2},
                        {Xtul, Ytul+Ht2}];
        Xtlr < Xful -> [{Xful, Yful+Hf2},
                        {Xtlr, Ytul+Ht2}];
        Yflr < Ytul -> [{Xful+Wf2, Yflr},
                        {Xtul+Wt2, Ytul}];
        Ytlr < Yful -> [{Xful+Wf2, Yful},
                        {Xtul+Wt2, Ytlr}];
        true -> [{Xful,Yful}, {Xtul,Ytul}]
    end.

%%%----------------
find_line(A, L) -> 
    case find_line(A, tl(L), hd(L)) of
	{line,P1,P2} -> {P1,P2};
	{last,P1} -> {P1,element(2,hd(L))};
	{first,P1} -> {element(2,lists:last(L)),P1}
    end.

find_line(A, _,           {A1,P1}) when A=<A1 -> {first,P1};
find_line(A, [{A2,P2}|L], {A1,P1}) when A=<A2 -> {line,P1,P2};
find_line(A, [{A2,P2}|L], _      ) -> find_line(A, L, {A2,P2});
find_line(A, [],          {A1,P1}) -> {last,P1}.

%%%----------------
line_intersect(P11,P12, P21,P22) ->
    case catch try_line_intersect(P11,P12, P21,P22) of
	{'EXIT',{{badmatch,_},_}} -> none;	% crossing is outside ranges
	parallel -> none;
	{vertical, P11,P12} -> line_intersect_vertical(P11,P12, P21,P22);
	{vertical, P21,P22} -> line_intersect_vertical(P21,P22, P11,P12);
	{X,Y} -> {X,Y}
    end.

try_line_intersect(P11,P12, P21,P22) ->
    K1M1 = k_m(P11,P12),
    K2M2 = k_m(P21,P22),
    P = try_line_intersect(K1M1, K2M2),
    true = on_line(P, P11,P12),
    true = on_line(P, P21,P22),
    P.

try_line_intersect({K1,M1}, {K2,M2}) when K1=/=K2 ->
    X = (M2-M1)/(K1-K2),
    Y = if (K1>K2) -> X*K1 + M1;
	   true -> X*K2 + M2
	end,
    {X,Y};
try_line_intersect({K1,M1}, {K2,M2}) when K1==K2 ->
    throw(parallel).
	    
line_intersect_vertical({Xv,Yv1},{Xv,Yv2}, P1,P2) ->
    case catch k_m(P1,P2) of
	{vertical,_,_} -> none;			% both vertical (Xv=X1 maybe)
	{K,M} -> {Xv, K*Xv+M}
    end.

k_m({X1,Y1}, {X2,Y2}) when X1=/=X2 -> 
    K = (Y2-Y1)/(X2-X1),
    M = Y2 - K*X2,
    {K,M};
k_m({X1,Y1}, {X2,Y2}) when X1==X2 ->
    throw({vertical,{X1,Y1}, {X2,Y2}}). 
    
on_line({X,Y}, {X1,Y1},{X2,Y2}) -> 
    (if X1<X2 -> (X1=<X) and (X=<X2);
	true -> (X2=<X) and (X=<X1)
     end) and
    (if Y1<Y2 -> (Y1=<Y) and (Y=<Y2);
	true -> (Y2=<Y) and (Y=<Y1)
     end).

%%%----------------
self_ref_coords_rect([{Xul,Yul},{Xlr,Ylr}], G) ->
    Pf = {Xlr, (Ylr+Yul) div 2},
    Pt = {Xul, (Ylr+Yul) div 2},
    R = 20,
    D0 = distance(Pf,Pt),
    {Alfa, Beta, Origo} =
	case ?user_opt(G,horizontal) of
	    true ->
		{D,P1} = 
		    if D0<2*R -> {D0, {Xlr,Ylr}};
		       true -> {2*R, {Xlr-D0/2+R, Ylr}}
		    end,
		A = 2*math:asin(D/(2*R)),
		{A, 
		 (math:pi()-A)/2, 
		 subD(P1, {round(R*math:sin(A/2)),
			   -round(R*math:cos(A/2))})};
	    false ->
		{D,P1} = 
		    if D0<2*R -> {D0, {Xul,Ylr}};
		       true  -> {2*R, {Xul, Ylr-D0/2+R}}
		    end,
		A = 2*math:asin(D/(2*R)),
		{A,
		 -A/2,
		 subD(P1, {round(R*math:cos(A/2)),
			   round(R*math:sin(A/2))})}
	end,
    Num = R div 2,
    Step = (2*math:pi()-Alfa)/Num,
    foldl(
      fun(N, Acc) ->
	      V = Beta - N*Step,
	      [addD(Origo, {round(R*math:cos(V)), 
			    -round(R*math:sin(V))}) | Acc]
      end, [], lists:seq(Num,0,-1)).

%%%----------------------------------------------------------------
%%%
create_graph_canvas(GSparent, GeomSpec, G) ->
    gs:canvas(canvas,GSparent,
	      [{bg, ?user_opt(G,bg_color)},
	       {motion,true},
	       {buttonrelease,true},{buttonpress,true},
	       {default,line,{buttonpress,true}},
	       {default,line,{buttonrelease,true}},
	       {default,rectangle,{buttonpress,true}},
	       {default,rectangle,{buttonrelease,true}},
	       {default,text,{font,?user_opt(G,graph_font)}},
	       {default,text,{buttonpress,true}},
	       {default,text,{buttonrelease,true}},
	       {vscroll,true},{hscroll,true}
	       | GeomSpec]),
    G.

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

%%%---- 
get_all_type(Type, Objs) -> filter(fun(O) -> type(O) == Type end, Objs).
    
get_all_type(Type) -> get_all_type(Type, gs:read(canvas,children)).
     
type(Obj) ->
    case gs:read(Obj,data) of
	Data when tuple(Data) -> element(1,Data);
	_ -> none
    end.

associated_objs(NodeObjs) when list(NodeObjs) -> 
    lists:flatten(map(fun associated_objs/1, NodeObjs));

associated_objs(NodeObj) -> 
    (gs:read(NodeObj,data))#node.associated_objs.


%%%---- list
middle(L) -> tl(L) -- [lists:last(L)].

listpos(Elem,L) -> length(lists:takewhile(fun(F) -> F =/= Elem end, L)) + 1.

%%%---- geometry
angel(Origo, P) ->
    {X,Y} = subD(P,Origo),
    A = math:atan2(Y,X),
    if A<0 -> 2*?pi + A;
       true -> A
    end.

%%%---- very misc

msg(F) -> msg(F,[]).
msg(F,V) -> gs:config(canvas,beep), io:format(F,V), no.


