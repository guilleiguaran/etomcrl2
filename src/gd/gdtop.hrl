%%% Default values for parameters

-record(gdtop_options, {
	  %% Window properties
	  title = "Graph",			% string()
	  user_v_area_size = 0,			% >=0 (in GS units)
	  user_h_area_size = 0,			% >=0 (in GS units)
	  user_area = [],
	  main_width = 500,
	  main_height = 400,
	  menubar_items = [],
	  frame_items = [],

	  %% General
	  max_backlog = 5,			% 0..inf
	  poll_interval = none			% none | >0  (seconds)
	 }).
	 
