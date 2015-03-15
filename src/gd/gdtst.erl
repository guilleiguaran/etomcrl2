-module(gdtst).
-export([start/0,
	 callback/1]).

-include("gd.hrl").
-include("gdtop.hrl").

start() ->
%%    gdtop:start({?MODULE,callback}).
    gdtop:start({?MODULE,callback}, [],
		#gdtop_options{menubar_items=
			       [{menubutton, [{label,{text,"TEST"}}]}]},
		#gd_options{graph_font={screen,16},
			    algorithm=tree} ).


callback(graph) ->
    #gd_graph{directed=false,
	      cyclic=false,
	      vertices=[n1,n2,n3,n4],
	      start_vertices=[n2],
	      edges=[{n1,n2}, {n2,n3},
		     {n1,n4}]};

callback({name_string,n1}) -> "A node\nwith a long name";
callback({name_string,n3}) -> "Another\nnode\nwith a long name";

callback({shape,n1}) -> oval;
callback({shape,n4}) -> {polygon, [{20,-10}, {30,-5}, {5,40}, {-15,45},
				   {-20,0}, {-10,-10}, {20,-10}]};

callback({old_node_attributes,n2}) -> [{fg,blue},{bw,2},{fill,white}];
callback({select_node_attributes,n3}) -> [{fg,red}];
callback({select_node_attributes,n4}) -> [{fill,yellow}];
callback({old_node_attributes,_}) -> [{fill,white}];
callback({new_node_attributes,_}) -> [{fill,white}].



