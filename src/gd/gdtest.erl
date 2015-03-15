-module(gdtest).
-export([start/0,
	 callback/2]).

-include("gdtop.hrl").
-include("gd.hrl").

-record(ud, {button,
	     entry,
	     directed=false,			% hard coded in options menu!!
	     test=empty}).


start() ->
    gdtop:start({?MODULE,callback},
		#ud{},
		#gdtop_options{title = "Test of Graph Drawing",
			       menubar_items =
			       [{menubutton,[{label,{text,"Tests"}}],
				 [{menu,[],test_menu_items()}]}]
			      },

		#gd_options{cyclic=false}).

%%%================================================================
test(Label,TestName) ->
    test(Label,TestName, []).

test(Label,TestName, L) ->
    {menuitem, [{label, {text,Label}}, {data,{test,TestName}},
		{itemtype,radio},{group,test}|L]}.

test_menu_items() ->
    [test("Empty",empty,[{select,true}]),
     test("Tree",tree),
     test("Large Tree",large_tree),
     test("Acyclic Graph",acyclic_graph),
     test("Acyclic Graph 2",acyclic_graph2),
     test("Acyclic Graph 3",acyclic_graph3),
     test("Cyclic",cyclic_graph1),
     test("Single-node Cyclic",cyclic_graph2),
     test("Single-node Cyclic 2",cyclic_graph3),
     test("Cyclic 3",cyclic_graph4),
     test("Cyclic 4",cyclic_graph5),
     test("Processes",processes),
     test("Expanding",expanding),
     test("Thomas 1",thomas1),
     test("Thomas 2",thomas2),
     test("Thomas Expanding 1",{expanding_thomas1,1}),
     test("Bjarne", bjarne),
     {menuitem, [{label,{text,"Options"}}, {itemtype,cascade}],
      [{menu,[],
	[option("Directed", directed)
	]
       }]}
    ].

option(Label, Name) -> 
    option(Label, Name, []).

option(Label, Name, L) -> 
    {menuitem, [{label, {text,Label}}, {data,{test_option,Name}},
		{itemtype,check}|L]}.


mk_graph({expanding,Vs,Es}, MyData) ->
    Last = lists:last(Vs),
    New = Last+1,
    NewVs = Vs ++ [New],
    NewEs = [{Last,New}|Es],
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = NewVs,
	       edges = NewEs},
     MyData#ud{test={expanding,NewVs,NewEs}}};

mk_graph(expanding, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [0],
	       edges = []},
     MyData#ud{test={expanding,[0],[]}}};

mk_graph({expanding_thomas1,1}, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = ["<G(X), F(X)>","<F(s(X)), F(X)>","<F(a), G(b)>"],
	       start_vertices=["<G(X), F(X)>"],
	       edges = [{"<F(s(X)), F(X)>","<F(a), G(b)>"},
			{"<F(s(X)), F(X)>","<F(s(X)), F(X)>"},
			{"<G(X), F(X)>","<F(a), G(b)>"},
			{"<G(X), F(X)>","<F(s(X)), F(X)>"},
			{"<F(a), G(b)>","<G(X), F(X)>"}]},
     MyData#ud{test={expanding_thomas1,2}}};

mk_graph({expanding_thomas1,2}, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = ["<G(X), F(X)>",
			   "<H(X,s(X)), H(0,0)>",
			   "<G(s(X)), G(X)>",
			   "<F(s(X)), F(X)>",
			   "<F(a), G(b)>",
			   "<H(X,0), F(X)>"],
	       edges = [{"<F(s(X)), F(X)>","<F(a), G(b)>"},
			{"<F(s(X)), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,0), F(X)>","<F(a), G(b)>"},
			{"<H(X,0), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,s(X)), H(0,0)>","<H(X,0), F(X)>"},
			{"<H(X,s(X)), H(0,0)>","<H(X,s(X)), H(0,0)>"},
			{"<G(s(X)), G(X)>","<G(s(X)), G(X)>"},
			{"<G(s(X)), G(X)>","<G(X), F(X)>"},
			{"<G(X), F(X)>","<F(a), G(b)>"},
			{"<G(X), F(X)>","<F(s(X)), F(X)>"},
			{"<F(a), G(b)>","<G(s(X)), G(X)>"},
			{"<F(a), G(b)>","<G(X), F(X)>"}]},
     MyData#ud{test={expanding_thomas1,3}}};

mk_graph({expanding_thomas1,3}, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = ["<G(X), F(X)>",
			   "<H(X,s(X)), H(0,0)>",
			   "<G(s(X)), G(X)>",
			   "<F(s(X)), F(X)>",
			   "<F(a), G(b)>",
			   "<H(X,0), F(X)>"],
	       edges = [{"<F(s(X)), F(X)>","<F(a), G(b)>"},
			{"<F(s(X)), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,0), F(X)>","<F(a), G(b)>"},
			{"<H(X,0), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,s(X)), H(0,0)>","<H(X,0), F(X)>"},
			{"<G(s(X)), G(X)>","<G(s(X)), G(X)>"},
			{"<G(s(X)), G(X)>","<G(X), F(X)>"},
			{"<G(X), F(X)>","<F(a), G(b)>"},
			{"<G(X), F(X)>","<F(s(X)), F(X)>"},
			{"<F(a), G(b)>","<G(X), F(X)>"}]},
     MyData#ud{test={expanding_thomas1,4}}};

mk_graph({expanding_thomas1,N}, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = [],
	       edges = []},
     MyData};

mk_graph(empty, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [], 
	       edges = []},
     MyData};

mk_graph(tree, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [n1,n2,n3,n4,n5,n6,n7,n8,n9,n10], 
	       start_vertices = [n9,n4],
	       edges = [{n1,n2}, {n2,n3}, {n1,n8}, {n4,n5},{n4,n6},{n4,n7},
			{n1,n4},
			{n9,n10}]},
     MyData};

mk_graph(cyclic_graph1, MyData) -> 
    {#gd_graph{cyclic=true,
	       start_vertices = [n2,n7,n8,n9],
	       vertices = [n1,n2,n3,n4,n5,n6,n7,n8,n9],
	       edges = [{n1,n2}, {n2,n3}, {n3,n4}, {n4,n1},{n3,n5},{n3,n6}]},
     MyData};

mk_graph(cyclic_graph2, MyData) -> 
    {#gd_graph{cyclic=true,
	       vertices = [n1],
	       edges = [{n1,n1}]},
     MyData};

mk_graph(cyclic_graph3, MyData) -> 
    {#gd_graph{cyclic=true,
	       vertices = [n1,n2],
	       edges = [{n1,n2}, {n2,n2}]},
     MyData};

mk_graph(cyclic_graph4, MyData) -> 
    {#gd_graph{cyclic=true,
	       vertices = [
			   n1,n2,n4,
			   n3,n5,n6,n7,n8,n9],
	       start_vertices = [n2,n5,n6,n8],
	       edges = [
			{n1,n2}, {n2,n3}, {n3,n4}, {n4,n1},{n3,n5},{n3,n6},
			{n6,n7},{n7,n3},{n5,n7}
			,
			{n9,n9}, {n8,n9}
		       ]},
     MyData};

mk_graph(cyclic_graph5, MyData) -> 
    {#gd_graph{cyclic=true,
	       start_vertices = [n2],
	       vertices = [n1,n2,n3,n4,n5,n6],
	       edges = [{n4,n5},
			{n4,n4},
			{n6,n5},
			{n6,n4},
			{n2,n6},
			{n2,n2},
			{n3,n3},
			{n3,n1},
			{n1,n5},
			{n1,n4},
			{n5,n3},
			{n5,n1}]},
     MyData};

mk_graph(acyclic_graph, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [n0,n1,n2,n3,n4,n5,n6,n7,n8,n9],
	       start_vertices = [n0],
	       edges = [{n0,n1},{n0,n2}, {n0,n8},
			{n1,n3}, {n1,n4}, {n1,n7}, {n1,n9},
			{n2,n3}, {n2,n5}, {n2,n8}, {n2,n9},
			{n3,n6},
			{n4,n6},
			{n5,n7}, {n5,n8},
			{n6,n9}]},
     MyData};

mk_graph(acyclic_graph2, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [n1,n2,n3,n4,n5,n6,n7,n8],
	       start_vertices = [n1],
	       edges = [{n1,n2}, {n1,n3}, {n1,n4},
			{n2,n5},
			{n3,n5}, {n3,n6},
			{n4,n7},
			{n5,n8},
			{n6,n8},
			{n7,n8}]},
     MyData};

mk_graph(acyclic_graph3, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [n1,n2,n3,n4,n5,n6],
	       start_vertices = [n1,n2,n3],
	       edges = [{n1,n4},
			{n2,n6},
			{n3,n5},
			{n4,n6},
			{n5,n6}]},
     MyData};

mk_graph(large_tree, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = lists:map(fun(I) -> list_to_atom([I]) end,
				    lists:seq($A,$Z) ++  
				    lists:seq($a,$z)) ++ [0,1,2],

	       edges = [{'A','B'}, {'A','S'}, {'A',o}, {'B','C'}, {'B','P'},
			{'S','T'}, {'S',e}, {o,p}, {'C','D'}, {'C','E'},
			{'P','Q'}, {'P','R'}, {'T','U'}, {'T','V'},
			{'T','W'}, {e,f}, {e,h}, {e,i}, {p,q}, {p,v}, {p,2},
			{'E','F'}, {'W','X'}, {'W','Z'}, {f,g}, {i,j}, {q,r},
			{q,s}, {q,t}, {q,u}, {v,w}, {v,x}, {v,0}, {v,1},
			{'F','G'}, {'F','H'}, {'F','M'}, {'F','N'},
			{'X','Y'}, {'Z',a}, {'Z',b}, {'Z',c}, {'Z',d}, {j,k},
			{j,l}, {j,m}, {j,n}, {x,y}, {x,z}, {'H','I'},
			{'H','J'}, {'H','K'}, {'H','L'}, {'N','O'}]}, MyData}; 

mk_graph(thomas1, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = ["<G(X), F(X)>",
			   "<H(X,s(X)), H(0,0)>",
			   "<G(s(X)), G(X)>",
			   "<F(s(X)), F(X)>",
			   "<F(a), G(b)>",
			   "<H(X,0), F(X)>"],
%%	       start_vertices=["<H(X,s(X)), H(0,0)>"],
	       edges = [{"<F(s(X)), F(X)>","<F(a), G(b)>"},
			{"<F(s(X)), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,0), F(X)>","<F(a), G(b)>"},
			{"<H(X,0), F(X)>","<F(s(X)), F(X)>"},
			{"<H(X,s(X)), H(0,0)>","<H(X,0), F(X)>"},
			{"<H(X,s(X)), H(0,0)>","<H(X,s(X)), H(0,0)>"},
			{"<G(s(X)), G(X)>","<G(s(X)), G(X)>"},
			{"<G(s(X)), G(X)>","<G(X), F(X)>"},
			{"<G(X), F(X)>","<F(a), G(b)>"},
			{"<G(X), F(X)>","<F(s(X)), F(X)>"},
			{"<F(a), G(b)>","<G(s(X)), G(X)>"},
			{"<F(a), G(b)>","<G(X), F(X)>"}]},
     MyData};

mk_graph(thomas2, MyData) ->
    {#gd_graph{cyclic=true,
	       vertices = ["<QUOT(s(X),s(Y)), MINUS(X,Y)>",
			   "<QUOT(s(X),s(Y)), QUOT(minus(X,Y),s(Y))>",
			   "<MINUS(s(X),s(Y)), MINUS(X,Y)>"],
%%	       start_vertices=["<QUOT(s(X),s(Y)), QUOT(minus(X,Y),s(Y))>"],
	       edges = [{"<QUOT(s(X),s(Y)), MINUS(X,Y)>",
			 "<MINUS(s(X),s(Y)), MINUS(X,Y)>"},
			{"<MINUS(s(X),s(Y)), MINUS(X,Y)>",
			 "<MINUS(s(X),s(Y)), MINUS(X,Y)>"},
			{"<QUOT(s(X),s(Y)), QUOT(minus(X,Y),s(Y))>",
			 "<QUOT(s(X),s(Y)), QUOT(minus(X,Y),s(Y))>"},
			{"<QUOT(s(X),s(Y)), QUOT(minus(X,Y),s(Y))>",
			 "<QUOT(s(X),s(Y)), MINUS(X,Y)>"}]},
     MyData};

mk_graph(bjarne, MyData) ->
    {#gd_graph{directed=MyData#ud.directed,
	       vertices = [erlang, 
			   teleorb,
			   oseDelta, linux, nt, win95, 
			   solaris, vxworks, ppc, alpha, intel, sparc, m68k],
	       start_vertices=[erlang
			      ,teleorb
			      ],
	       edges = [{erlang, oseDelta},
			{erlang, linux},
			{erlang, nt},
			{erlang, win95},
			{erlang, solaris},
			{erlang, vxworks},
			{teleorb, ppc},
			{teleorb, intel},
			{oseDelta, ppc},
			{oseDelta, m68k},
			{linux, alpha},
			{nt, alpha},
			{nt, intel},
			{win95, intel},
			{solaris, intel},
			{solaris, sparc},
			{vxworks, ppc},
			{vxworks, m68k}]},
     MyData};

mk_graph(processes, MyData) -> 
    Vs = processes(),
    Es = lists:foldl(
	   fun(Pid,Acc) ->
		   lists:foldl(
		     fun(Pid1,Acc1) ->
			     T = lists:sort([Pid,Pid1]), % prevent cycles
			     ordsets:add_element(list_to_tuple(T), Acc1)
		     end, Acc, 
		     case catch lists:keysearch(links,1,process_info(Pid)) of
			 {value,{_,Pids}} -> Pids;
			 _ -> []
		     end)
	   end, [], Vs),
    SVs = [whereis(init) | case whereis(gs_frontend) of
			       undefined -> [];
			       Pid -> [Pid]
			   end],
    {#gd_graph{directed=MyData#ud.directed,
	       start_vertices = SVs,
	       vertices = Vs,
	       edges = Es},
     MyData}.

%%%---------------- Window setup
callback({frame,Parent}, MyData) ->
    gs:label(Parent,[{label,{text,"Process:"}}]),
    {ok, #ud{entry = gs:entry(Parent,[{x,80},{width,300}]),
	     button= gs:button(Parent,[{x,400},{data,my_tst},
				       {label,{text,"test"}}])}};

%%%---------------- Action in window with the drawn graph
callback({selected_nodes,N}, MyData) ->
    gs:config(MyData#ud.button, {enable,length(N)>0}),
    {ok,MyData};

callback({event, {gs,_,click,{test,Test},_}}, MyData) ->
    {ok, MyData#ud{test=Test}};

callback({event,{gs,_,click,{test_option,Option},[_,_,_,Value]}}, MyData) ->
    {ok, case Option of
	     directed -> MyData#ud{directed=Value}
	 end};

callback({event,{gs,_,click,my_tst,_}},  MyData) ->
    {ok, MyData};

callback({click,node,Id}, MyData) ->
    {case MyData#ud.test of
	 processes ->
	     {text, io_lib:format('~p\n',[process_info(Id)])};
	 Other ->
	     {menu,[{"Label 1", l1},
		    {"Label 2", l2}]}
     end, MyData};


%%%---------------- Graph definition
callback(graph, MyData) ->
    mk_graph(MyData#ud.test, MyData);


%%%---------------- Appearence
%callback({shape,{'#4$placeholder',X}}, MyData) ->
%    {oval, MyData};

callback({shape,Id}, MyData) when pid(Id) ->
    true = lists:member(Id, [whereis(init),whereis(gs_frontend)]),
    {oval, MyData};

callback({name_string,{'#4$placeholder',X}}, MyData) ->
    {io_lib:write(X), MyData};

callback({name_string,Pid}, MyData) when pid(Pid) ->
    {case lists:keysearch(registered_name,1,process_info(Pid)) of
	 {value, {_,N}} -> io_lib:format("~w\n~w",[N,Pid]);
	 _ -> io_lib:write(Pid)
     end, MyData};

callback({old_node_attributes,{'#4$placeholder',X}}, MyData) ->
    {[{fill,white}], MyData};

callback({old_arc_attributes,{Edge,LevelDiff}}, MyData) ->
    {case LevelDiff of
	 undefined -> none;			% not level-drawing
	 1 -> none;				% parent->child, use default
	 0 -> [{width,2},{fg,blue}];		% same level arc
	 I when I<0 -> [{width,2},{fg,orange}];	% backward arc
	 I when I>1 -> [{width,2},{fg,orange}]	% forward to grand+ children
     end, MyData};

callback(P,MyData) ->
    %%    io:format('Unhandled user callback: ~w ~w\n', [P,MyData]),
    none.
