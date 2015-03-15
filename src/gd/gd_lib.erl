-module(gd_lib).
-author('hans@erix.ericsson.se').

-export([zip/1, zip/2, unzip/1,
	 minmax/1,
	 addD/2, addD/1,
	 subD/2,
	 divD/2,
	 mulD/2,
	 truncD/1,
	 roundD/1,
	 meanD/1,
	 distance/2]).



%%%----------------
zip([A|As], [B|Bs]) -> [{A,B} | zip(As,Bs)];
zip(_,_) -> [].

zip([[]|_]) -> [];
zip(Ls) ->[list_to_tuple(lists:map(fun(L) -> hd(L) end,Ls)) | 
	   zip(lists:map(fun(L) -> tl(L) end,Ls))].

%%%----------------
unzip(L) -> unzip(L, [], []).

unzip([{A,B}|ABs], Aacc, Bacc) -> unzip(ABs,[A|Aacc],[B|Bacc]);
unzip([], Aacc, Bacc) -> {lists:reverse(Aacc), lists:reverse(Bacc)}.


%%%---- arithmetic
addD({A1,B1}, {A2,B2}) -> {A1+A2, B1+B2}.

addD(L) when list(L) -> lists:foldl(fun addD/2, hd(L), tl(L)).

subD({A1,B1}, {A2,B2}) -> {A1-A2, B1-B2}.

divD({A,B},N) when number(N) -> {A div N, B div N}.

mulD(N, {X,Y}) when number(N) -> {N*X, N*Y};
mulD({X,Y}, N) when number(N) -> {N*X, N*Y}.

truncD({A,B}) -> {trunc(A), trunc(B)}.
    
roundD({A,B}) -> {round(A), round(B)}.
    
meanD(L) when list(L),length(L)>0 -> 
    divD(lists:foldl(fun addD/2,hd(L),tl(L)),length(L)).


minmax(Points) ->
    {Xs,Ys} = unzip(Points),
    {lists:min(Xs),lists:max(Xs),lists:min(Ys),lists:max(Ys)}.

%%%---- geometry
distance({X1,Y1}, {X2,Y2}) ->
    Dx = (X1-X2),
    Dy = (Y1-Y2),
    math:sqrt(Dx*Dx + Dy*Dy).
	    
    
