%%% Default values for parameters

-record(gd_options, {
	  %% default graph options (overridden by record gd_graph)
	  cyclic = true,			% true | false
	  directed = true,			% true | false

	  %% Layout style:
	  algorithm = tree,			% tree | {graph,sugiyama}
	  hierarchic = true,			% true | false
	  horizontal = true,			% true | false
	  bg_color = white,			% GS color
	  node_separation = 15,			% int >=0

	  %% ... root style
	  center_parents = true,		% true | false

	  %% ... vertex style
	  shape = rectangle,
	  graph_font = {fixed,12},		% (GS font notation)
	  max_name_string = 10,			% Number of characters
	  select_node_attributes = [{bw,3}],
	  new_node_attributes = [{fill,green}],
	  old_node_attributes = [{fill,cyan}],
	  del_node_attributes = [{fill,red}],

	  %% ... edge style
	  new_arc_attributes = [{fg,green}],
	  old_arc_attributes = [{fg,black}],
	  del_arc_attributes = [{fg,red}],
	  family_tree = true			% true | false
	 }).


%%% The input graph

-record(gd_graph,
	{%% Graph properties (defaults in record gd_options)
	  cyclic,				% true | false
	  directed,				% true | false

	  %% most important vertices:
	  start_vertices = [],			% [Id]

	  %% The graph itself:
	  vertices = [],				% [Id]    Id = term()
	  edges = []				% [{Id,Id}]
	}).

	 
%%% changes to an already displayed graph

-record(gd_graph_update,
	{new_vertices = [],			% [Id]
	 deleted_vertices = [],			% [Id]
	 new_edges = [],			% [{Id,Id}]
	 deleted_edges = []			% [{Id,Id}]
	}).

