% Functions for constructs that mCRL supports, but
% are not mapped nicely in Erlang.
%
% These functions are used to enrich the Erlang code
% to enable a translation into mCRL
%
% September 2003 Thomas Arts

-module(mcrl).

-export([nondeterministic/2]).

%+type nondeterministic(A->B,[A]) -> B.
%
nondeterministic(Fun,Choices) ->
   {A1,A2,A3} = now(),
   random:seed(A1,A2,A3),
   Choice = random:uniform(length(Choices)),
   Fun(lists:nth(Choice,Choices)).


