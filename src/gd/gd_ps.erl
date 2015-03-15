-module(gd_ps).


-export([ps/1, ps/2]).

-import(gd_lib, [mulD/2, subD/2, roundD/1, addD/2]).

-record(s, {scale = 1,
	    fn,
	    lw
	   }).

%% return a PostScript representation of the gs canvas Canvas.

%%ps(Canvas) -> ps(Canvas, {0,0}, {593,842}).

ps(Canvas) -> ps(gs:read(parent_window(Canvas),title), Canvas).

ps(Title, Canvas) -> ps(Title, Canvas, {40,40}, {513,762}).

ps(Title, Canvas, {Xps_min,Yps_min}, {Xps_max,Yps_max}) ->
    Objs = gs:read(Canvas,children),
    AllCoords = lists:flatten(lists:map(fun(O) ->
						gs:read(O,coords)
					end, Objs)),
    {Xmin,Xmax,Ymin,Ymax} = gd_lib:minmax(AllCoords),
    H = Ymax - Ymin,
    W = Xmax - Xmin,
    Sx = Xps_max/W,
    Sy = Yps_max/H,
    S = lists:min([Sx,Sy]),
    F = fun({X0,Y0}) ->
		   X1 = round(Xps_min + S*(X0-Xmin)),
		   Y1 = round(Yps_min + S*(Ymax-Y0)),
		   {X1, Y1}
	   end,
    {GraphPs,_} = lists:mapfoldl(fun ps_obj/2,
			     #s{fn=F,
				scale=S},
			     lists:reverse(Objs)),
    [ps_prolog(Title, {Xps_min,Yps_min,Xps_max,Yps_max}, S),
     GraphPs,
     ps_epilog()
    ].


parent_window(O) ->
    case gs:read(O,type) of
	window -> O;
	_ -> parent_window(gs:read(O,parent))
    end.

%%%----------------------------------------------------------------
ps_obj(O,D) -> 
    F = D#s.fn,
    ps_obj(gs:read(O,type), lists:map(F,gs:read(O,coords)), D, O).


ps_obj(rectangle, [{Xul,Yul}, {Xlr,Ylr}], D, O) ->
    {W,D1} = line_width(O,bw,D),
    {[W, io_lib:format("~w ~w ~w ~w r\n", [Xul,Yul, Xlr,Ylr])],
     D1};

ps_obj(line, Coords, D, O) ->
    {W,D1} = line_width(O,width,D),
    {[case gs:read(O, arrow) of
	  none -> [];
	  first -> draw_arrow(Coords);
	  last -> draw_arrow(lists:reverse(Coords));
	  both -> [draw_arrow(Coords),
		  draw_arrow(lists:reverse(Coords))]
      end,
      W,
      draw_line(Coords, gs:read(O,smooth))
     ], D1};

ps_obj(polygon, Coords, D, O) ->
    {W,D1} = line_width(O,bw,D),
    {[W, draw_line(Coords)],
     D1};

ps_obj(oval, [{Xul,Yul}, {Xlr,Ylr}], D, O) ->
    Xc = (Xul+Xlr) div 2,
    Yc = (Yul+Ylr) div 2,
    Dx = (Xlr-Xul) / (Ylr-Yul),
    R = Xc - Xul,
    {W,D1} = line_width(O,bw,D),
    {[W, io_lib:format("~w ~w ~w ~w o\n", [Xc/Dx,Yc,R/Dx,Dx])],
     D1};

ps_obj(text, [P0], D, O) ->
    Txt = gs:read(O, text),
    {X0,Y0} = P0,
    {X,Y} = {X0, Y0 - round(D#s.scale*12)},
    {io_lib:format('(~s) ~w ~w t\n', [Txt,X,Y]),
     D};

ps_obj(Type, Coords, D, O) ->
    io:format('*** gs type ~w (object ~w near ~w) not supported!\n', 
	      [Type,O,Coords]),
    {[], D}.


%%%----------------
line_width(O, A, D) -> 
    CurrentW = D#s.lw,
    case gs:read(O,A) of
	CurrentW -> {[],D};
	W -> {io_lib:format(" ~w lw ",[W]), D#s{lw=W}}
    end.


draw_line(Points) -> draw_line(Points,false).

draw_line([{X,Y}|T], Smooth) ->
    case Smooth of
	false -> [lists:map(fun({Xi,Yi}) ->
				    io_lib:format("~w ~w ", [Xi,Yi])
			    end, lists:reverse(T)),
		  case length(T) of
		      1 -> io_lib:format("~w ~w l1\n", [X,Y]);
		      L -> io_lib:format("~w ~w ~w l\n", [L,X,Y])
		  end
		 ];
	true -> 
	    [io_lib:format("~w ~w moveto  ", [X,Y]),
	     draw_smooth_line_cont(T),
	     io_lib:format(' stroke\n',[])
	    ]
    end.

draw_smooth_line_cont([{X1,Y1}, {X2,Y2}, {X3,Y3} | Points]) ->
    [io_lib:format(' ~w ~w  ~w ~w ~w ~w curveto', [X1,Y1, X2,Y2, X3,Y3]),
     draw_smooth_line_cont(Points)];
draw_smooth_line_cont([{X1,Y1}, {X2,Y2}]) ->
    io_lib:format(' ~w ~w  ~w ~w ~w ~w curveto', [X1,Y1, X2,Y2, X2,Y2]);
draw_smooth_line_cont([{X1,Y1}]) ->
    io_lib:format(' ~w ~w  ~w ~w ~w ~w curveto', [X1,Y1, X1,Y1, X1,Y1]);
draw_smooth_line_cont([]) ->
    [].

draw_arrow([{Xt,Yt},{Xf,Yf}|_]) ->
    D = gd_lib:distance({Xt,Yt},{Xf,Yf}),
    {Xf1,Yf10} =
	if D<5 -> {Xf,Yf};
	   true -> 
		F = 5/D,
		roundD(addD({Xf,Yf},   mulD(1-F, subD({Xt,Yt},{Xf,Yf}))))
	end,
    Yf1 = 
	if Yf10==Yt -> Yt+0.01;
	   true -> Yf10
	end,
    io_lib:format('~w ~w ~w ~w a\n', [Xf1,Yf1,Xt,Yt]).


    
%%%----------------------------------------------------------------
ps_prolog(Title, BoundingBox, S) ->
    [eps_header(Title, BoundingBox),
     choosefont_def(),
     arrow_proc_def(S),
     io_lib:format("/l {moveto {lineto} repeat stroke} def\n"
		   "/l1 {moveto lineto stroke} def\n"
		   "\n"
		   "/r {/y2 exch def\n"
		   "    /x2 exch def\n"
		   "    /y1 exch def\n"
		   "    /x1 exch def\n"
		   "    newpath\n"
		   "    x1 y1 moveto x2 y1 x2 y2 x1 y2 3 {lineto} repeat\n"
		   "    closepath gsave 1 setgray fill grestore} def\n"
		   "\n"
		   "/o {matrix currentmatrix 5 1 roll 1 scale\n"
		   "    0 360 arc gsave 1 setgray fill grestore\n"
		   "    setmatrix\n"
		   "} def\n"
		   "\n"
		   "/lw {~w mul setlinewidth} def\n"
		   "\n"
		   "%%EndProlog\n"
		   "\n"
		   "/Helvetica ~w choosefont\n"
		   "\n"
		   "%%Page: 1 1\n",
		   [S, round(S*12)]
		  )].

ps_epilog() ->
    "stroke\n"
	"showpage\n"
	"%%Trailer\n"
	"%%EOF\n".

eps_header(Title, {LLx,LLy,URx,URy}) ->
    {YYYY,MM,DD} = date(),
    {HH,Min,SS} = time(),
    io_lib:format("%!PS-Adobe-2.0\n"
		  "%%Title: ~s\n"
		  "%%Creator: Generic Graph Frontend 0.1\n"
		  "%%CreationDate: ~w-~2..0w-~2..0w ~2..0w:~2..0w:~2..0w\n"
		  "%%BoundingBox: ~w ~w ~w ~w\n"
		  "%%Pages: 1\n"
		  "%%DocumentFonts: Helvetica\n"
		  "%%EndComments\n",
		  [Title, YYYY,MM,DD, HH,Min,SS, LLx,LLy,URx,URy]).

choosefont_def() ->
    "/choosefont {\n"
	"    exch findfont exch scalefont setfont\n"
	"    currentfont /FontBBox get 0 get\n"
	"    currentfont /FontBBox get 1 get\n"
	"    currentfont /FontMatrix get dtransform\n"
	"    /yfllt exch def\n"
	"    /xfllt exch def\n"
	"    currentfont /FontBBox get 2 get\n"
	"    currentfont /FontBBox get 3 get\n"
	"    currentfont /FontMatrix get dtransform\n"
	"    /yfurt exch def\n"
	"    /xfurt exch def\n"
	"    /fh yfurt yfllt sub def\n"
	"    /fw xfurt xfllt sub def\n"
	"    /t {yfllt sub dup /y0 exch def\n"
	"        exch\n"
	"        xfllt add dup /x0 exch def\n"
	"        exch moveto\n"
	"        {pop 10 eq {/y0 y0 fh sub def  x0 y0 moveto} if }\n"
	"        exch kshow\n"
	"        stroke\n"
	"    } def\n"
	"\n"
	" } def\n".
    

%% Xtail Ytail  Xtip Ytip  TailThickness HeadMaxThicknes HeadLength
arrow_proc_def(S) ->
    io_lib:format("/arrowdict 14 dict def\n"
		  "arrowdict begin\n"
		  "  /mtrx matrix def\n"
		  "end\n"
		  "\n"
		  "/arrow\n"
		  " {arrowdict begin\n"
		  "    /headlength exch def\n"
		  "    /halfheadthickness exch 2 div def\n"
		  "    /halfthickness exch 2 div def\n"
		  "    /tipy exch def  /tipx exch def\n"
		  "    /taily exch def /tailx exch def\n"
		  "\n"
		  "    /dx tipx tailx sub def\n"
		  "    /dy tipy taily sub def\n"
		  "    /arrowlength dx dx mul dy dy mul add sqrt def\n"
		  "    /angle dy dx atan def\n"
		  "    /base arrowlength headlength sub def\n"
		  "\n"
		  "    /savematrix mtrx currentmatrix def\n"
		  "\n"
		  "    tailx taily translate\n"
		  "    angle rotate\n"
		  "\n"
		  "    0 halfthickness neg moveto\n"
		  "    base halfthickness neg lineto\n"
		  "    base halfheadthickness neg lineto\n"
		  "    arrowlength 0 lineto\n"
		  "    base halfheadthickness lineto\n"
		  "    base halfthickness lineto\n"
		  "    0 halfthickness lineto\n"
		  "    closepath\n"
		  "\n"
		  "    savematrix setmatrix\n"
		  "  end\n"
		  "} def\n"
		  "\n"
		  "/a {newpath ~w ~w ~w arrow fill} def\n",
		  [1, trunc(S*5), trunc(S*7)]). 
