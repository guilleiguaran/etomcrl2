-module(gd_alg_sugiyama).
-author('hans@erix.ericsson.se').

-export([design/3]).

-import(lists, [map/2, foreach/2, max/1, min/1,	foldl/3, foldr/3,
		mapfoldl/3]).

-import(ordsets, [from_list/1, is_element/2, add_element/2, del_element/2,
		  subtract/2, union/2, union/1, intersection/2]).

-import(gd_lib, [zip/2, unzip/1, addD/2]).


-include("gd.hrl").
-include("gd_algs.hrl").

%%% A classical graph placement algorithm.


design(Roots, Graph, Opt) ->
    assign_levels(Roots, Graph, Opt),
    insert_extra_nodes(Graph),
    Levels = more_bc_passes(Graph, first_bc_passes(Graph)),
    %%---- temporary position-in-level assignment:
    MaxLen = max(map(fun(L) -> length(L) end, Levels)),
    foreach(
      fun(Ls) ->
	      case length(Ls) of
		  MaxLen -> do_nothing;
		  Len ->
		      Delta = (MaxLen-Len) div 2,
		      foreach(
			fun({V,_}) ->
				{_,D} = digraph:vertex(Graph, V),
				{A,B} = D#vertex.bc,
				digraph:add_vertex(Graph, V,
						   D#vertex{bc={A+Delta,
								B+Delta}})
			end, Ls)
	      end
      end, Levels),
    {Pre, Post} =  lists:splitwith(fun(L) -> length(L) =/= MaxLen end,
				   Levels),
    {SepX,SepY} = ?level_separation,
    Sep = if Opt#gd_options.horizontal==true -> SepY;
	     true -> SepX
	  end,
    assign_poss(Post, MaxLen, Graph, Opt, Sep, 2),
    assign_poss(lists:reverse(Pre), MaxLen, Graph, Opt, Sep, 1).
    
					   
assign_poss([Lev|Ls], MaxLen, Graph, Opt, Sep, Elem) when length(Lev)==MaxLen->
    foldl( 
      fun({V,INs_OUTs}, P) ->
	      {_,D} = digraph:vertex(Graph, V),
	      digraph:add_vertex(Graph, V, D#vertex{bc={P,P},
						    level_pos=P}),
	      {W,H} = D#vertex.wh,
	      P + Sep + 
		  if Opt#gd_options.horizontal==true ->  H;
		     true -> W
		  end
      end, 1, Lev),
    assign_poss(Ls, MaxLen, Graph,Opt,  Sep, Elem);
assign_poss([Lev|Ls], MaxLen, Graph, Opt, Sep, Elem) ->
    foldl( 
      fun({V,INs_OUTs}, Pos) ->
	      {_,D} = digraph:vertex(Graph, V),
	      P = 
		  case mean_bcs(Graph, Elem, INs_OUTs, Pos) of
		      BC when BC>=Pos -> BC;
		      BC when BC<Pos -> Pos
		  end,
	      digraph:add_vertex(Graph, V, D#vertex{bc={P,P},
						    level_pos=P}),
	      {W,H} = D#vertex.wh,
	      P + Sep + 
		  if Opt#gd_options.horizontal==true ->  H;
		     true -> W
		  end
      end, 1, Lev),
    assign_poss(Ls, MaxLen, Graph,Opt,  Sep, Elem);
assign_poss([], _, _, _, _, _) ->
    [].
	      
%%%----------------
assign_levels(Roots, Graph, Opt) -> 
    assign_levels(from_list(Roots), Graph, Opt, 0, []).


assign_levels([], Graph, Opt, Nlastlevel, Placed) 
  when Opt#gd_options.directed==true ->
    Nlastlevel;

assign_levels([], Graph, Opt, Nlastlevel, Placed) ->
    %% push vertices upwards
    foreach(
      fun(V) ->
	      {_,D} = digraph:vertex(Graph,V),
	      Ns = digraph:in_neighbours(Graph,V) ++
		  digraph:out_neighbours(Graph,V),
	      Ls = foldl(fun(Nb,Acc) ->
				 {_,D1} = digraph:vertex(Graph,Nb),
				 add_element(D1#vertex.level, Acc)
			 end, [], Ns),
	      Lev = first_hole(Ls),
	      if Lev < D#vertex.level ->
		      digraph:add_vertex(Graph,V,D#vertex{level=Lev});
		 true ->
		      ok
	      end
      end, digraph:vertices(Graph)),
    %% delete unnessecary backward links
    foreach(fun(E) ->
		    {_,F,T,D} = digraph:edge(Graph,E),
		    {_,Df} = digraph:vertex(Graph,F),
		    {_,Dt} = digraph:vertex(Graph,T),
		    if 
			Df#vertex.level >  Dt#vertex.level ->
			    digraph:del_edge(Graph, E);
			true ->
			    keep_it
		    end
	    end, digraph:edges(Graph)),
    Nlastlevel;

assign_levels(Roots, Graph, Opt, N, Placed) ->
    ThisLevel = foldl(
		  fun(V,Lev) ->
			  INs =
			      del_element( %% self ref is ok.
				V,
				from_list(digraph:in_neighbours(Graph,V))),
			  case intersection(INs,Lev) of
			      [] ->
				  Lev;
			      _ -> 
				 del_element(V,Lev)
			  end
		  end, Roots, Roots),
    %% set the levels
    foreach(fun(V) ->
		    {_,D} = digraph:vertex(Graph,V),
		    digraph:add_vertex(Graph,V,D#vertex{level=N})
	    end, ThisLevel),
    %% get all candidates for the next level
    Children0 = 
	foldl(
	  fun(V,Acc) ->
		  ONs = 
		      del_element( %% beware of self-ref.
			V,
			from_list(digraph:out_neighbours(Graph,V))),
		  union(ONs,Acc)
	  end, [], ThisLevel),
    Children = subtract(Children0, Placed),
    assign_levels(union(Children, subtract(Roots,ThisLevel)),
		  Graph, Opt, N+1, union(ThisLevel,Placed)).



first_hole(Ls) -> first_hole(tl(Ls), hd(Ls)).

first_hole([H|T], E) -> case E+1 of
			    H -> first_hole(T, H);
			    E1 -> E1
			end;
first_hole([], E) -> E+1.
    

%%%----------------
insert_extra_nodes(Graph) ->
    foldl(
      fun(E,N) ->
	      {_,F,T,D} = digraph:edge(Graph,E),
	      {_,Df} = digraph:vertex(Graph,F),
	      {_,Dt} = digraph:vertex(Graph,T),
	      case (Dt#vertex.level-Df#vertex.level) of
		  1 -> 
		      digraph:add_edge(Graph,E,F,T,D#edge{type=placed}),
		      N;
		  I when integer(I), I>1 ->	% insert extra node(s)
		      break_edge(Df#vertex.level, Dt#vertex.level,
				 F, T, Graph, N, last),
		      digraph:del_edge(Graph,E),
		      N + I-1;

		  -1 ->				% backward edge, reverse it
		      digraph:del_edge(Graph,E),
		      digraph:add_edge(Graph,{T,F},T,F,
				       D#edge{arrow_place=first,
					      type=placed}),
		      N;
		  I when integer(I), I< -1 ->	% long backward edge
		      break_edge(Dt#vertex.level, Df#vertex.level,
				 T, F, Graph, N, first),
		      digraph:del_edge(Graph,E),
		      N + I-1;
		  0 -> %% self ref node
		      N
	      end
      end, 0, digraph:edges(Graph)).
    

break_edge(LevelF,LevelT, F,T, Graph, N, Apos) ->
    NewNames =
	  map(fun(Lev) ->
		      New = ?placeholder(N+Lev-LevelF-1),
		      digraph:add_vertex(Graph,New,#vertex{level=Lev}),
		      New
	      end, lists:seq(LevelF+1,LevelT-1)),
    LastName =
	foldl(
	  fun(Name,PrevName) ->
		  digraph:add_edge(Graph, {PrevName,Name}, PrevName,Name,
				   #edge{arrow_place=Apos,
					 type=placed}),
		  Name
	  end, F, NewNames),
    digraph:add_edge(Graph, {LastName,T}, LastName,T, #edge{arrow_place=Apos,
							    type=placed}).


%%%----------------------------------------------------------------
initialize_bcs(Graph) ->
    get_neighbours(sort_by_level(Graph), Graph).


%%%----
sort_by_level(Graph) ->
    Nodes = 
	lists:keysort(1, map(fun(V) ->
				     {_,D} = digraph:vertex(Graph,V),
				     {D#vertex.level, V}
			     end, digraph:vertices(Graph))),
    Levels = collect_levels(Nodes, [], none),
    foreach(
      fun(Ns) ->
	      foldl(
		fun(V,N) -> 
			{_,D} = digraph:vertex(Graph,V),
			digraph:add_vertex(Graph,V,D#vertex{bc={N,N}}),
			N+1
		end, 1, Ns)
      end, Levels),
    Levels.
    
		   
collect_levels([{L,V}|Ns], Acc, L) ->
    collect_levels(Ns, [V|Acc], L);

collect_levels([{L,V}|Ns], Acc, Lold) when integer(Lold) ->
    [Acc | collect_levels(Ns,[V],L)];

collect_levels([{L,V}|Ns], Acc, none) ->
    collect_levels(Ns, [V], L);

collect_levels([], Acc, _) ->    
    [Acc].

%%%----
get_neighbours(Ls, Graph) ->
    map(fun(Ns) ->
		map(fun(V) -> {V, 
			       {digraph:out_neighbours(Graph,V)--[V],
				digraph:in_neighbours(Graph,V)--[V]}
			      }
		    end, Ns)
	end, Ls).

%%%----------------------------------------------------------------
first_bc_passes(Graph) -> 
    one_pass(Graph, initialize_bcs(Graph)).

more_bc_passes(Graph, Levels) -> more_bc_passes(Graph, Levels, 10).

%%%--------
more_bc_passes(Graph, Levels, 0) ->
    Levels;
more_bc_passes(Graph, Levels, Count) ->
    case one_pass(Graph, Levels) of
	Levels -> Levels;
	NewLevels -> more_bc_passes(Graph, NewLevels, Count-1)
    end.

one_pass(Graph, Levels) ->
    one_sweep(one_sweep(Levels,Graph,2,[]), Graph, 1, []).

one_sweep([Lev|Ls], Graph, Elem, Acc) ->
    {R,_} = mapfoldl(
	      fun({BC, V, INs_OUTs}, Pos) ->
		      {_,D} = digraph:vertex(Graph,V),
		      digraph:add_vertex(Graph,V,D#vertex{bc={Pos,BC}}),
		      {{V,INs_OUTs}, Pos+1}
	      end, 1, lists:keysort(1,do_one_level(Graph,Lev,Elem))),
    one_sweep(Ls, Graph, Elem, [R|Acc]);
one_sweep([], _, _, Acc) ->
    Acc.

do_one_level(Graph, Ns, Elem) ->
    {R, _} =
	mapfoldl(
	  fun({V,INs_OUTs}, Pos) -> 
		  BC = mean_bcs(Graph, Elem, INs_OUTs, Pos),
		  {{BC,V,INs_OUTs}, Pos+1}
	  end, 1, Ns),
    R.

mean_bcs(Graph, Elem, INs_OUTs, Pos) ->
    case element(Elem,INs_OUTs) of
	[] -> 
	    Pos;
	L ->
	    Sum =
		foldl(fun(V,Acc) ->
			      {_,D} = digraph:vertex(Graph,V),
			      {RelPos,_} = D#vertex.bc,
			      Acc +  RelPos
		      end, 0, L),
	    R = Sum / length(L),
	    R
    end.
