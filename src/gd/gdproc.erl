-module(gdproc).

-include("gdtop.hrl").
-include("gd.hrl").
%%% Example of usage of the Graph Drawer. This module displays process links

-export([start/0, callback/1]).

-import(lists, [foldl/3]).
-import(ordsets, [add_element/2]).

%%%================================================================
start() -> gdtop:start({?MODULE,callback}, no_state,
		      #gdtop_options{},
		      #gd_options{algorithm=tree,
				  cyclic=false,
				  horizontal=false
				 }).

%%%================================================================
%%% Calls from the Grah Drawer

callback(title) -> "Linked Processes";

callback(graph) -> 
    StartVertices = [whereis(init), whereis(gs_frontend)],
    #gd_graph{vertices=processes(),
	      start_vertices=lists:filter(fun(X) -> X=/=undefined end,
					  StartVertices),
	      edges=links()};

callback({shape,Id}) -> Id = whereis(init), oval;

callback({name_string,Pid}) when pid(Pid) ->
    case catch lists:keysearch(registered_name,1,process_info(Pid)) of
	{value, {_,N}} -> atom_to_list(N) ++ "\n" ++ pid_to_list(Pid);
	_ -> io_lib:write(Pid)
    end;

callback({click,node,Id}) ->
    {text, io_lib:format('~p\n',[process_info(Id)])}.


%%%================================================================
%%% The list of all pairs of linked processes
links() ->
    foldl(fun(Pid,Acc) ->
		  foldl(fun(Pid1,Acc1) ->
				T = lists:sort([Pid,Pid1]),
				add_element(list_to_tuple(T), Acc1)
			end, Acc, linked_to(Pid))
	  end, [], processes()).
    

%%% The list of processes that Pid are linked to
linked_to(Pid) ->
    case catch lists:keysearch(links,1,process_info(Pid)) of
	{value,{_,Pids}} -> Pids;
	_ -> []
    end.
