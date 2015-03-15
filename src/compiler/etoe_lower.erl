%
% replace map function on sourcecode level (abstract forms)
%
%% <p> Thomas Arts. January 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

%% PRECOND:
%% 
%% A list of Abstract forms.
%%
%% TODO: list comprehensions and records
%%
%% INVARIANTS:
%%
%% The Erlang semantics are preserved
%% 
%% POSTCOND:
%%
%% The high order functions "map" and "foreach" are replaced for a
%% first order variant as follows:
%%     
%%    map(fun(X) -> ... end,Xs) is replaced by map_...(Xs,FreeVar1,...,FreeVarN)
%% code is added for map_.../N+1

-module(etoe_lower).

-export([forms/1,file/1,file/2,freevars/1]).

-import(lists,[map/2,member/2,foldl/3,foldr/3]).

-include("etomcrl.hrl").


-define(Rest,'Rest').

%+type forms([abs_form()]) -> [abs_form()].
%
forms(AbsForms) ->
  {NewAbsForms,MapFuns} =
     foldr(fun({eof,Line},{NewForms,Maps}) ->
                {NewForms,Maps++[{eof,Line}]};
              (AbsForm,{NewForms,Maps}) ->
                replace(AbsForm,NewForms,Maps)
           end,{[],[]},AbsForms),
  NewAbsForms++MapFuns.

%+type file(filename()) -> [abs_form()] 
%
file(FileName) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms).

%+type file(filename()) -> [abs_form()] 
%
file(Source,Dest) ->
  AbsForms = tl(file(Source)),
  ok = 
    file:write_file(Dest, 
                    map(fun(A) -> erl_pp:form(A) end, AbsForms)).


replace({function,Line,Name,Arity,Clauses},Forms,Maps) ->
  {MapFreeBody,NewMaps} = mapfree(Clauses,Maps),
  {[{function,Line,Name,Arity,MapFreeBody}|Forms],NewMaps};
replace(AbsForm,Forms,Maps) ->
  {[AbsForm|Forms],Maps}.

% mapfree/2: parsing an expression, 
%   replacing map(fun(X) -> ... end,Xs) by   map_...(Xs,FreeVar1,...,FreeVarN)
%   and adding code for map_.../N+1
mapfree(Expr,Maps) ->
  case Expr of
       Exprs when list(Exprs) ->
         foldl(fun(E,{Es,Ms}) ->
                  {NE,NMs} = mapfree(E,Ms),
                  {Es++[NE],NMs}
               end,{[],Maps},Exprs);
       {clause,Line,Pats,Guards,E} ->
         {NE,NMs} = mapfree(E,Maps),
         {{clause,Line,Pats,Guards,NE},NMs};
       {tuple,Line,Es} ->
         {NEs,NMs} = mapfree(Es,Maps),
         {{tuple,Line,NEs},NMs};
       {cons,Line,Head,Tail} ->
         {NH,NM1s} = mapfree(Head,Maps),
         {NT,NM2s} = mapfree(Tail,NM1s),
         {{cons,Line,NH,NT},NM2s};
       {match,Line,E1,E2} ->
         {NE2,NMs} = mapfree(E2,Maps),
         {{match,Line,E1,NE2},NMs};
       {'case',Line,E,Clauses} ->
         {NE,NM1s} = mapfree(E,Maps),
         {NCs,NM2s} = mapfree(Clauses,NM1s),
         {{'case',Line,NE,NCs},NM2s};
       {call,Line,Fun,Args} ->
         case {Fun,length(Args)} of
              {{atom,_,map},2} ->
                hofcall(Maps,map,Line,Args);
              {{remote,_,{atom,_,lists},{atom,_,map}},2} ->
                hofcall(Maps,map,Line,Args);
              {{atom,_,foreach},2} ->
                hofcall(Maps,foreach,Line,Args);
              {{remote,_,{atom,_,lists},{atom,_,foreach}},2} ->
                hofcall(Maps,foreach,Line,Args);
              _ ->
                {NArgs,NM1s} = mapfree(Args,Maps),
                {{call,Line,Fun,NArgs},NM1s}
         end;
       {op,Line,Op,E} ->
         {NE,NMs} = mapfree(E,Maps),
         {{op,Line,Op,NE},NMs};
       {op,Line,Op,E1,E2} ->
         {NE1,NM1s} = mapfree(E1,Maps),
         {NE2,NM2s} = mapfree(E2,NM1s),
         {{op,Line,Op,NE1,NE2},NM2s};

% list comprehensions should also be considered, like records

       _ ->
         {Expr,Maps}
  end.

hofcall(Maps,Kind,Line,[Arg1,Arg2]) ->
  case hofname(Maps,atom_to_list(Kind),Arg1,Arg2) of
       error ->
         {{call,Line,{atom,Line,Kind},[Arg1,Arg2]},Maps};
       {Name,FreeVars,Clauses} ->
          %?DEBUG("~p found ~p ~p ~p~n",[Kind,Name,Arg1,Arg2]),
          HOFun = 
            case Kind of
                 map ->
                   {function,1,Name,length(FreeVars)+1,
                      [{clause,1,[{nil,1}|FreeVars],[],[{nil,1}]}|
                       map(fun({clause,_,[Pat],Guards,Exprs}) ->
                              {clause,1,[{cons,1,Pat,{var,1,rest(Pat,?Rest)}}|
                                         FreeVars],Guards,
                               maplast(Name,rest(Pat,?Rest),FreeVars,Exprs)}
                           end,Clauses)
                      ]
                   };
                 foreach ->
                   {function,1,Name,length(FreeVars)+1,
                      [{clause,1,[{nil,1}|FreeVars],[],[{nil,1}]}|
                       map(fun({clause,_,[Pat],Guards,Exprs}) ->
                              {clause,1,[{cons,1,Pat,{var,1,rest(Pat,?Rest)}}|
                                         FreeVars],Guards,
                               foreachlast(Name,rest(Pat,?Rest),FreeVars,Exprs)}
                           end,Clauses)
                      ]
                   } 
            end,
          {{call,Line,{atom,Line,Name},[Arg2|FreeVars]},
           [HOFun|Maps]}
  end.

maplast(Name,Rest,FreeVars,[E]) -> 
  [{cons,1,E,{call,1,{atom,1,Name},[{var,1,Rest}|FreeVars]}}];
maplast(Name,Rest,FreeVars,[E|Es]) -> 
  [E|maplast(Name,Rest,FreeVars,Es)].

foreachlast(Name,Rest,FreeVars,[E]) -> 
  [E,{call,1,{atom,1,Name},[{var,1,Rest}|FreeVars]}];
foreachlast(Name,Rest,FreeVars,[E|Es]) -> 
  [E|foreachlast(Name,Rest,FreeVars,Es)].


hofname(Maps,Kind,{'fun',_,{clauses,Clauses}},Arg2) ->
  Name = 
    case Clauses of
          [{clause,_,Pats,Guards,[{call,_,Fun,Args}]}] ->
            case Fun of
                 {atom,_,Atom} ->
                   list_to_atom(Kind++"_"++atom_to_list(Atom));
                 {remote,_,{atom,_,Mod},{atom,_,Atom}} ->
                   list_to_atom(Kind++"_"++atom_to_list(Mod)++"_"++
                                        atom_to_list(Atom))
            end;
          _ ->
            list_to_atom(Kind++"_"++integer_to_list(length(Maps)))
     end,
   {Name,freevars(Clauses),Clauses};
hofname(Maps,Kind,Arg1,Arg2) ->
  io:format("Error line ~p: function in ~p not 'fun' type~n",
            [element(2,Arg1),Kind]),
  error.

% freevars(Clauses) should return all free variables in the clauses Clauses
freevars(Clauses) ->
  map(fun(V) -> {var,1,V} end,clauses_transform(Clauses)).

rest({var,_,V},Rest) ->
  list_to_atom(atom_to_list(V)++"s");
rest(_,Rest) -> Rest.


% modified erl_id_trans.erl

clauses_transform(Clauses) ->
  {Bound,Free} = icr_clauses(Clauses,{[],[]}),
  sets:to_list(sets:from_list(Free)).    % uniq list of vars

icr_clauses(Clauses,{Bound,Free}) ->      % used strong scope rules !
  foldl(fun({clause,_,P0,G0,B0},{Bs,Fs}) -> 
           {B,NewBound} = patterns(P0,{Bs,[]}),
           {_,NewFree} = exprs(B0,guard(G0,{B++NewBound,Fs})),
           {Bs,NewFree}
        end,{Bound,Free},Clauses).

patterns(Pats,{Bound,Free}) ->
  foldl(fun(Pat,{B,F}) ->
           pattern(Pat,{B,F})
        end,{Bound,Free},Pats).

pattern(Pat,Vars) ->
  case Pat of
       {var,Line,'_'} ->
         Vars;
       {var,Line,V} -> 
         {Bound,Free} = Vars,
         case member(V,Bound) of
              true ->
                {Bound,Free};
              false ->
                {Bound,[V|Free]}
         end;
       {match,Line,P0,R0} ->
         {Bound,Free} = Vars,
         {B1s,F1s} = pattern(P0,{Bound,[]}),
         pattern(R0,{B1s++F1s,Free});
       {integer,Line,I} -> 
         Vars;
       {float,Line,F} ->
         Vars;
       {atom,Line,A} ->
         Vars;
       {string,Line,S} ->
         Vars;
       {nil,Line} ->
         Vars;
       {cons,Line,H0,T0} ->
         patterns([H0,T0],Vars);
       {tuple,Line,Ps0} ->
         patterns(Ps0,Vars);
       {record,Line,Name,Pfs0} ->
         foldl(fun({record_field,Lf,{atom,La,F},P0},Vs) ->
                  pattern(P0,Vs)
               end,Vars,Pfs0);
%% record_field occurs in query expressions
       {record_field,Line,Rec0,Field0} ->
         expr(Field0,expr(Rec0,Vars));
       {bin,Line,Fs} ->
         pattern_grp(Fs,Vars);
       {op,Line,'++',P1,P2} ->
         patterns([P1,P2],Vars);
       {op,Line,Op,A} ->
         pattern(A,Vars);
       {op,Line,Op,L,R} ->
         patterns([L,R],Vars)
  end.

pattern_grp(Bins,Vars) ->
  foldl(fun({bin_element,L1,E1,S1,T1},Vs) ->
           case S1 of
                default -> Vs;
                _ -> expr(S1,Vs)
           end
        end,Vars,Bins).

guard([G0|Gs],Vars) when list(G0) ->
    guard(Gs,exprs(G0,Vars));
guard(G,Vars) ->
    exprs(G,Vars).

exprs(Exprs,Vars) ->
  foldl(fun(E,Vs) ->
           expr(E,Vs)
        end,Vars,Exprs).

expr(Expr,Vars) ->
  case Expr of
       {var,Line,'_'} ->
         Vars;
       {var,Line,V} -> 
         {Bound,Free} = Vars,
         case member(V,Bound) of
              true ->
                {Bound,Free};
              false ->
                {Bound,[V|Free]}
         end;
       {match,Line,P0,R0} ->
         {Bound,Free} = Vars,
         {B1s,F1s} = pattern(P0,{Bound,[]}),
         expr(R0,{B1s++F1s,Free});
       {integer,Line,I} -> 
         Vars;
       {float,Line,F} ->
         Vars;
       {atom,Line,A} ->
         Vars;
       {string,Line,S} ->
         Vars;
       {nil,Line} ->
         Vars;
       {cons,Line,H0,T0} ->
         exprs([H0,T0],Vars);
       {tuple,Line,Ps0} ->
         exprs(Ps0,Vars);
       {bin,Line,Fs} ->
         pattern_grp(Fs,Vars);
       {op,Line,Op,E1,E2} ->
         exprs([E1,E2],Vars);
       {op,Line,Op,E} ->
         expr(E,Vars);
       {lc,Line,E0,Qs0} ->
         expr(E0,lc_quals(Qs0,Vars));
       {record_index,Line,Name,Field0} ->
         expr(Field0,Vars);
       {record,Line,Name,Inits0} ->
         foldl(fun({record_field,Lf,{atom,La,F},Val0},Vs) ->
                  expr(Val0,Vs)
               end,Vars,Inits0);
       {record_field,Line,Rec0,Name,Field0} ->
         exprs([Rec0,Field0],Vars);
       {record,Line,Rec0,Name,Upds0} ->
         foldl(fun({record_field,Lf,{atom,La,F},Val0},Vs) ->
                  expr(Val0,Vs)
               end,expr(Rec0,Vars),Upds0);
       {record_field,Line,Rec0,Field0} ->
         exprs([Rec0,Field0],Vars);
       {block,Line,Es0} ->
         exprs(Es0,Vars);
       {'if',Line,Cs0} ->
         icr_clauses(Cs0,Vars);
       {'case',Line,E0,Cs0} ->
         icr_clauses(Cs0,expr(E0,Vars));
       {'receive',Line,Cs0} ->
         icr_clauses(Cs0,Vars);
       {'receive',Line,Cs0,To0,ToEs0} ->
         icr_clauses(Cs0,exprs([To0|ToEs0],Vars));

       {'fun',Line,Body} ->
         case Body of
	      {clauses,Cs0} ->
	          icr_clauses(Cs0,Vars);
	      {function,F,A} ->
	          Vars;
	      {function,M,F,A} ->	%This is an error in lint!
	          Vars
          end;

       {call,Line,{var,L0,V0},As0} -> 
         exprs([{var,L0,V0}|As0],Vars);
       {call,Line,F0,As0} ->
         exprs(As0,Vars);
       {'catch',Line,E0} ->
         expr(E0,Vars);
       {'query', Line, E0} ->
    %% lc expression
         expr(E0,Vars)      %% ??
  end. 


lc_quals([{generate,Line,P0,E0}|Qs],Vars) ->
    {Bound,Free} = expr(E0,Vars),
    {_,F} = pattern(P0,{Bound,[]}),
    lc_quals(Qs,{Bound++F,Free});
lc_quals([E0|Qs],Vars) ->
    lc_quals(Qs,expr(E0,Vars));
lc_quals([],Vars) -> 
    Vars.

