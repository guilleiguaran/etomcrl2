-record(vertex, {
	  node_obj,
	  level,				% 0,1,....
	  level_pos,				% Float >= 0
	  short_string="",
	  full_string="",
	  wh={1,1},
	  %% for sugiyama algortihm
	  bc
	 }).

-record(edge, {
	  obj,
	  type,					% original | reversed_copy 
						% | placed
	  long_names,
	  arrow_place = last,			% first | last
	  level_diff				% integer() | undefined
	 }).

-define(pseudo_root, '# $$%pseudo_root').
-define(placeholder(N), {'#4$placeholder',N}).

-define(level_separation, {30,60}).


