-module(gd_txtwin).

-export([pop_up_text_window/3,
	 txt_win/3]).

-define(DBG(F,V), io:format('~w ~w ~w: ~s\n',
			    [?MODULE,?LINE,self(),io_lib:format(F,V)])).

%%%----------------------------------------------------------------
pop_up_text_window(Parent, Title, Spec) ->
    spawn(?MODULE, txt_win, [Parent,Title,Spec]).

txt_win(Parent, Title, Spec) ->
    mk_txt_win(Parent, Title, lists:flatten(get_txt(Spec))),
    txt_win_loop(loop).

mk_txt_win(Parent, Title, String) ->
    W = gs:window(Parent, [{map,true}, {title,Title}, {configure,true},
			   {data,txt_window}]),
    MenuBar = 
	{menubar,[],
	 [{menubutton,{label,{text,"File"}},
	   [{menu,[],
	     [{menuitem,[{data,exit},{label,{text,"Exit"}}]}]
	    }]
	  }]
	},
    gs:create_tree(W,[MenuBar]),
    F = gs:frame(W, [{packer_x,[{stretch,1}]},
		     {packer_y,[{fixed,30},{stretch,1,50}]}]),
    E = gs:editor(F, [{pack_xy,{1,2}},
		      {insert,{'end',String}},
		      {wrap,none},
		      {hscroll,true},{vscroll,true}]),
    gs:config(W, {data,F}),
    gs:config(F, lower),
    gs:config(E, {enable,false}),
    {Kw,Kh} = cols_rows(String),
    Width = 30 + 7 * lists:max([lists:min([Kw,80]), 20]),
    Height = 60 + 16 * lists:max([lists:min([Kh,25]), 10]),
    gs:config(W, [{width,Width},{height,Height}]).

cols_rows(String) ->
    {_,Kw,Kh} = lists:foldl(fun($\n,{N,Nmax,H}) when N>Nmax -> {0,N,H+1};
			       ($\n,{N,Nmax,H}) -> {0,Nmax,H+1};
			       ($\t,{N,Nmax,H}) -> {8-(N rem 8),Nmax,H};
			       (_, {N,Nmax,H}) -> {N+1,Nmax,H}
			    end, {0,0,0}, String),
    {Kw,Kh}.

txt_win_loop(stop) ->
    ok;
txt_win_loop(_) ->
    txt_win_loop(
      receive
	  {gs,_,click,exit,_} -> stop;

	  %% "system"
	  {gs,_,configure,[],_} -> ok;		% occurs on PCs !
	  {gs,_,configure,F,[W,H|_]} -> gs:config(F,[{width,W},{height,H}]);
	  {gs,_,destroy,_,_} -> stop;

	  Others ->
	      ?DBG("*** Unknown event: ~p\n", [Others])
      end).

%%%----------------------------------------------------------------

get_txt({load,FileName}) ->
    case file:read_file(FileName) of
	{ok, Bin} -> 
	    binary_to_list(Bin);
	{error, Reason} ->
	    io_lib:format(
	      '*** ERROR while trying to read file "~p".\nReason=~s\n',
	      [FileName, file:format_error(Reason)])
    end;

get_txt(S) when list(S) -> 
    S.
    
