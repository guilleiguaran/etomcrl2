-module(gd_alg_patch).
-author('hans@erix.ericsson.se').

-export([patch_place_new_vertices/4]).

-import(lists, [map/2, foreach/2, max/1, min/1,	foldl/3, foldr/3,
		filter/2]).

-import(ordsets, [from_list/1, is_element/2, add_element/2,
		  subtract/2]).

-import(gd_lib, [zip/2, unzip/1,
		 addD/2, addD/1,
		 subD/2,
		 divD/2,
		 mulD/2,
		 truncD/1,
		 meanD/1]).

-include("gd.hrl").
-include("gd_algs.hrl").

%%% The algorithm for patching a drawn graph in the graph drawer gd.

%%%================================================================
%%%
%%%  Update an existing drawing by checking the places near the ancestors
%%%  of the new nodes.
%%%
%%%================================================================

patch_place_new_vertices(NewVertices, Graph, Opt, G) ->
    StartNodes = children_to_placed(NewVertices,Graph),
    patch_place_new_vertices(StartNodes, NewVertices--StartNodes,
			     Graph, Opt, G).


patch_place_new_vertices([], [], _, _, _) ->		% ready
    ok;

patch_place_new_vertices([], NotPlaced, Graph, Opt, G) ->
    %% No relatives. Put them anywhere
    foreach(fun(Id) ->
		    patch_place_new_node(Id,Graph,Opt,G)
	    end, NotPlaced);

patch_place_new_vertices(StartNodes, NotPlaced, Graph, Opt, G) -> 
    %% Has relatives
%%    foldl(fun patch_place_new_node/2, Graph, StartNodes),
    foreach(fun(Id) ->
		    patch_place_new_node(Id,Graph,Opt,G)
	    end, StartNodes),
    patch_place_new_vertices(children_to_placed(NotPlaced,Graph),
			     NotPlaced -- StartNodes,
			     Graph, Opt, G).

children_to_placed(Vs, Graph) ->
    filter(fun(V) ->
		   placed_neighbours(V,Graph) =/= []
	   end, Vs).

placed_neighbours(Name, Graph) ->
    Neighbs = 
	from_list(digraph:in_neighbours(Graph,Name) ++
		    digraph:out_neighbours(Graph,Name)),
    filter(fun(V) ->
		   case digraph:vertex(Graph,V) of
		       {_,D} when D#vertex.node_obj =/= undefined -> true;
		       _ -> false
		   end
	   end, Neighbs).


patch_place_new_node(Name, Graph, Opt, G) ->
    WH = addD(gd:node_WH(Name,Opt#gd_options.graph_font), ?level_separation),
    Parents = placed_neighbours(Name, Graph),
    case try_each_parent(Parents,Name,WH,Graph,Opt) of
	{ParentName, Pos} -> gd:draw_node(Name, Pos, G);
	false -> gd:draw_node(Name, try_all_xys(WH), G)
    end.

%%%----------------
try_each_parent([Pname|Ps], Child, WH, Graph, Opt) ->
    case find_free_pos_around(Pname, Child, WH, Graph, Opt) of
	false -> try_each_parent(Ps, Child, WH, Graph, Opt);
	Pos -> {Pname,Pos}
    end;
try_each_parent([], Child, WH, Graph, Opt) ->
    false.

find_free_pos_around(Pname, Child, WH, Graph, Opt) ->
    Children = digraph:out_neighbours(Graph,Pname),
    GrandChildren = foldl(fun(V,Acc) -> 
				  digraph:out_neighbours(Graph,V)++Acc
			  end, [], Children),
    Parents = digraph:in_neighbours(Graph,Pname),
    {_,D} = digraph:vertex(Graph, Pname),
    Pcoords = gs:read(D#vertex.node_obj,coords),
    case try_each([poss_of(Children,Graph)], WH, meanD(Pcoords), Opt) of
	false ->
	    [Ppos] = poss_of([Pname],Graph),
	    {W,H} = WH,
	    P1 = case Children--[Child] of
		     [] when Opt#gd_options.horizontal == true -> 
			 [addD(Ppos, {W+15,0})];
		     [] -> [addD(Ppos, {0,H+15})];
		     _ -> []
		 end,
	    case try_each([P1], WH, meanD(Pcoords), Opt) of
		false ->
		    try_each([poss_of(GrandChildren,Graph),
			      [Ppos],
			      poss_of(Parents,Graph)],
			     WH, meanD(Pcoords), Opt);
		Pos ->
		    {_,_,_,De} = digraph:edge(Graph, {Pname,Child}),
		    digraph:add_edge(Graph, {Pname,Child}, Pname, Child,
				     De#edge{type=placed}),
		    Pos
	    end;
	Pos ->
	    {_,_,_,De} = digraph:edge(Graph, {Pname,Child}),
	    digraph:add_edge(Graph, {Pname,Child}, Pname, Child,
			     De#edge{type=placed}),
	    Pos
    end.
    
try_each([L|Ls], WH, PosM, Opt) ->
    case try_one(unzip(L),WH,PosM,Opt) of
	false -> 
	    try_each(Ls,WH,PosM,Opt);
	{X,Y} when Opt#gd_options.horizontal==true -> 
	    {W,H} = WH,
	    {X, Y+H div 2};
	{X,Y} ->
	    {W,H} = WH,
	    {X+W div 2, Y}
    end;
try_each([],_,_,_) ->
    false.

try_one({Xs0,Ys0}, {W,H}, {Xm,Ym}, Opt) when Opt#gd_options.horizontal==true ->
    try_poss(foldl(fun(X,Acc) ->
			   possible_poss({X,Ym},20,1,{0,H div 2}) ++ Acc
		   end, [], from_list(Xs0)),
	     {W,H});
try_one({Xs0,Ys0}, {W,H}, {Xm,Ym}, Opt) when Opt#gd_options.horizontal==false->
    try_poss(foldl(fun(Y,Acc) ->
			   possible_poss({Xm,Y},40,1,{W div 4,0}) ++ Acc
		   end, [], from_list(Ys0)),
	     {W,H}).
    
poss_of(L, Graph) -> 
    foldl(fun(V,Acc) ->
		  case digraph:vertex(Graph, V) of
		      {_,D} when D#vertex.node_obj=/=undefined ->
			  [Pos|_] = gs:read(D#vertex.node_obj,coords),
			  [Pos | Acc];
		      _ -> 
			  Acc
		  end
	  end, [], L).
    
    
possible_poss(Pos0, Nmax, N, Delta) when N<Nmax ->
    D = mulD(N,Delta),
    [subD(Pos0,D), addD(Pos0,D) | possible_poss(Pos0,Nmax,N+1,Delta)];
possible_poss(Pos0, _, _, _) ->
    [].
    
try_poss([Pos|Poss], WH) ->
    case is_free([Pos,addD(Pos,WH)]) of
	false -> 
%%	    gs:rectangle(canvas, [{fg,blue}, {coords,[Pos,addD(Pos,WH)]}]),
%%	    gs:rectangle(canvas, [{fill,blue}, {coords,[Pos,addD(Pos,{1,1})]}]),
	    try_poss(Poss, WH);
	true -> 
%%	    gs:rectangle(canvas, [{fg,orange}, {coords,[Pos,addD(Pos,WH)]}]),
%%	    gs:rectangle(canvas, [{fill,orange}, {coords,[Pos,addD(Pos,{2,2})]}]),
	    Pos
    end;
try_poss([], WH) ->
    false.

%%%----------------
try_all_xys(WH) -> try_all_xys({{0,0},x},WH).

try_all_xys({Pos,Next}, WH) ->
    case is_free(Pos,WH) of
	true -> Pos;
	false -> try_all_xys(next_xy(Pos,Next),WH)
    end.

next_xy({X,Y},x) -> {{X+10,Y},y};
next_xy({X,Y},y) -> {{X,Y+10},x}.
		    
%%%----------------
is_free(Rect) ->
    [Pul,Plr] = Rect,
    case Pul of
	{X,Y} when X<0 -> false;
	{X,Y} when Y<0 -> false;
	_ -> 
	    lists:all(fun(O) ->
			      gs:read(O,data)==[]
		      end, gs:read(canvas, {hit,Rect}))
   end.
	      

is_free(Pos,WH) -> 
    case Pos of
	{X,Y} when X<0 -> false;
	{X,Y} when Y<0 -> false;
	_ -> 
	    lists:all(
	      fun(O) ->
		      gs:read(O,data)==[]
	      end, 
	      gs:read(canvas, {hit,[subD(Pos,?level_separation),
				    addD([Pos,WH,?level_separation])]}))
    end.

