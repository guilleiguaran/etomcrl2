-module(erlang).

%%%%%% bifs

%+type gen_tag(pid()) -> {pid(),atom()}.

gen_tag(Pid) -> {Pid,tag}.

%+type gen_modtageq({pid(),tag()},{pid(),tag()}) -> bool().
%
% in mcrl there are no tags to remove, in contrast to the
% Erlang version of gen_modtageq.
%
gen_modtageq(Client1,Client2) -> 
  Client1==Client2.

gen_modtagrm(Client) ->
  Client.

%+type member(X,[X]) -> bool().

member(E,[]) -> 
  false;
member(E,[Head|Tail]) ->
  case E==Head of
       true ->
         true;
       false ->
         member(E,Tail)
  end.

