-module(gd_alg_tree).
-author('hans@erix.ericsson.se').

-export([design_new_tree/3]).

-import(lists, [map/2, foreach/2, max/1, min/1,	foldl/3, foldr/3]).

-import(ordsets, [from_list/1, is_element/2, add_element/2,
		  subtract/2]).

-import(gd_lib, [zip/2, unzip/1]).


-include("gd.hrl").
-include("gd_algs.hrl").

%%% The tree placement algorithm for the graph drawer gd.


%%%================================================================
%%%
%%% Hierarchic tree placement
%%% 
%%%   @article{Kennedy:trees,
%%%     author        = "A. J. Kennedy",
%%%     title         = "Functional Pearls: Drawing Trees",
%%%     journal       = "Journal of Functional Programming",
%%%     volume        = 6,
%%%     number        = 3,
%%%     year          = 1996,
%%%     month         = "May",
%%%     pages         = "527--534",
%%%     publisher     = "Cambridge University Press"
%%%   }
%%%
%%%   http://ultralix.polytechnique.fr/~kennedy/trees.html
%%%   
%%%   G. M. Radack. Tidy drawing of M-ary trees.
%%%   Tecnhnical Reprort CES-88-24, Department of Computer Engineering and
%%%   Science, Case Western Reserve Univnersity, Cleveland, Ohio,
%%%   November 1988.
%%
%%%================================================================

design_new_tree(Roots, Graph, Opt) ->
    Vertices = digraph:vertices(Graph),
    Params = {Opt#gd_options.node_separation, Opt#gd_options.center_parents},
    Design =
	case mk_tree(Roots,Graph,Opt,from_list(Vertices)) of
	    [Tree] -> abs_design(Tree, Params);
	    Trees -> abs_design({?pseudo_root,0,lists:reverse(Trees)}, Params)
	end,
    gd:trim_edges(Graph),
    tree_levels_poss(Design,Graph).

%%%----
mk_tree(Roots, Graph, Opt, Vertices) ->
    case mk_trees(Roots,Graph,Opt,[],[]) of
	{L,Vertices} ->
	    L;
	{Trees, Visited} -> 
	    NotVisited = subtract(Vertices,Visited),
	    Trees ++ mk_tree([hd(NotVisited)],Graph,Opt,NotVisited)
    end.

mk_trees([R|Rs], Graph, Opt, Visited, Acc) ->
    case is_element(R,Visited) of
	true ->
	    mk_trees(Rs,Graph,Opt,Visited,Acc);
	false ->
	    {Sts,Visited1} = mk_trees(digraph:out_neighbours(Graph,R),Graph,
				      Opt, add_element(R,Visited),[]),
	    foreach(
	      fun({Node,_,_}) ->
		      E1 = {R,Node},
%%		      E2 = {Node,R},
		      {_,_,_,D1} = digraph:edge(Graph, E1),
%%		      {_,_,_,D2} = digraph:edge(Graph, E2),
		      digraph:add_edge(Graph, {R,Node}, R, Node,
				       D1#edge{type=placed})
	      end, Sts),
	    {_,D} = digraph:vertex(Graph,R),
	    {W,H} = D#vertex.wh,
	    Dim = case Opt#gd_options.horizontal of
		      false -> W;
		      true -> H
		  end,
	    mk_trees(Rs, Graph, Opt, Visited1, [{R,Dim,Sts}|Acc])
    end;
mk_trees([],Graph,Opt,Visited,Acc) ->
    {Acc,Visited}.

%%%----
%%% Enters Level and Postion in level into the digraph
tree_levels_poss({{?pseudo_root,_}, Trees}, Graph) ->  
    tree_levels_poss(Trees, Graph);

tree_levels_poss(Trees,Graph) when list(Trees) -> 
    tree_levels_poss(Trees,0,Graph);

tree_levels_poss(Tree,Graph) ->
    tree_levels_poss([Tree],Graph).


tree_levels_poss(TreeList, Level, Graph) ->
    foreach(
      fun({{Name,Pos},SubTree}) ->
	      {_,D} = digraph:vertex(Graph, Name),
	      digraph:add_vertex(Graph, Name, D#vertex{level=Level,
							   level_pos=Pos}),
	      tree_levels_poss(SubTree, Level+1, Graph)
      end, TreeList).

%%%----
abs_design(Tree,Params) ->
    D = abs(design(Tree,Params), 0),
    {Min,Max} = min_max(D),
    move(D, -Min).

abs({{Name,RelPos},SubTree}, RootPos) ->
    NewPos = RelPos+RootPos,
    {{Name,NewPos}, map(fun(T) -> abs(T,NewPos) end,SubTree)}.

move({{Name,AbsPos},SubTree}, Disp) ->
    NewPos = AbsPos+Disp,
    {{Name,NewPos}, map(fun(T) -> move(T,Disp) end,SubTree)}.

poss(N) -> poss(N,[]).

poss({{_,P},S}, Acc) -> foldl(fun poss/2, [P|Acc], S).

min_max(L) ->
    Pss = poss(L),
    {min(Pss), max(Pss)}.

design(Tree,Params) -> element(1, design1(Tree,Params)).

design1({Label,Dim,Subtrees}, Params) ->
    {Trees, Extents} = unzip(map(fun(T) -> design1(T,Params) end, Subtrees)),
    Positions = fitlist(Extents,Params),
    Ptrees = map(fun move_tree/1, zip(Trees,Positions)),
    Pextents = map(fun move_extent/1, zip(Extents,Positions)),
    HalfDim = Dim div 2,
    ResultExtent = [{-HalfDim,HalfDim}|merge_list(Pextents)],
    ResultTree = {{Label,0.0},Ptrees},
    {ResultTree, ResultExtent}.

move_tree({{{Label,Pos},SubTrees}, Delta}) ->
    {{Label,Pos+Delta},SubTrees}.

move_extent({E, Delta}) ->
    map(fun({P,Q}) ->
		{P+Delta, Q+Delta}
	end, E).

merge([], Qs) -> Qs;
merge(Ps, []) -> Ps;
merge([{P,_}|Ps], [{_,Q}|Qs]) -> [{P,Q}|merge(Ps,Qs)].

merge_list(Es) -> foldr(fun merge/2, [], Es).

rmax(P, Q) when P>Q -> P;
rmax(P, Q) -> Q.

fit([{_,P}|Ps], [{Q,_}|Qs], Sep) -> rmax(fit(Ps,Qs,Sep), P-Q+Sep);
fit(_, _, Sep) -> 0.0.

fitlistl1(Acc,[],_) -> [];
fitlistl1(Acc,[E|Es],Sep) ->
    X = fit(Acc,E,Sep),
    [X | fitlistl1(merge(Acc,move_extent({E,X})),Es,Sep)].

fitlistl(Es,Sep) -> fitlistl1([],Es,Sep).

fitlistr1(Acc,[],Sep) -> [];
fitlistr1(Acc,[E|Es],Sep) ->
    X = - fit(E,Acc,Sep),
    [X | fitlistr1(merge(move_extent({E,X}),Acc),Es,Sep)].

fitlistr(Es,Sep) -> lists:reverse(fitlistr1([],lists:reverse(Es),Sep)).

fitlist(Es,{Sep,Center}) -> 
    map(fun({X,Y}) when Center==true -> (X+Y)/2;
	   ({X,_}) when Center==false -> X
	end, zip(fitlistl(Es,Sep),fitlistr(Es,Sep))).

