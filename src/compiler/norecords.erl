%
% remove records from AbsForms (source-to-source transformation)
%
% % <p>Thomas Arts. May 2001</p> 
%%
%% <p>Revised and commented by Juanjo Sanchez Penas and Clara Benac Earle.
%% October 2003</p>

-module(norecords).

-export([forms/1,file/1,file/2]).

-import(lists,[map/2,foldl/3,foldr/3]).
-include("etomcrl.hrl").

%+type forms([abs_form()]) -> [abs_form()].
%%
%% 

forms(AbsForms) ->
    {Records,{New,Extract,Update},OtherForms} =
	foldr(fun({function,Line,Name,Arity,Clauses},{Recs,RForms,Forms}) ->
		      {Recs,RForms,[{function,Line,Name,Arity,clauses(Clauses)}|Forms]};
		 ({attribute,Line,record,{Name,Fields}},{Recs,{Ns,Es,Us},Forms}) ->

		      FieldNames = % atom list of field names extacted from the abstract form
			  map(fun({record_field,_,{atom,_,FN}}) -> % Undefined field (no initial value)
				      FN;
				 ({record_field,_,{atom,_,FN},_}) -> % Initialized field
				      FN
			      end,Fields),

		      ?DEBUG("after ~p found record ~p~n",[Recs,Name]),

		      case lists:keysearch(Name,1,Recs) of
			  {value,{_,Fs}} -> % The record has already been processed
			      case Fs==FieldNames of
				  true -> % The same record again
				      {Recs,{Ns,Es,Us},Forms};
				  false -> % Another record with the same name

				      %% TODO:
				      %% As it is implemented now, we
				      %% cannot handle records defined
				      %% in different modules with the
				      %% same name. This could be
				      %% solved by putting the Erlang
				      %% module name in front of the
				      %% record name, in the noimports
				      %% module of the compiler

				      ?ERROR(Line,"multiple definitions of record ~p~n",
					  [Name]),
				      {Recs,{Ns,Es,Us},Forms}
			      end;
			  false -> % New record definition (we need to translate it)
			      {NCs,ECs,UCs} = 
				  {mk_new(Name,Fields),
				   mk_extract(Name,Fields),
				   mk_update(Name,Fields)},
			      
			      {[{Name,FieldNames}|Recs],
			       {NCs++Ns,ECs++Es,UCs++Us}, 
			       %% NCs = New clauses for the records
			       %% ECs = Extract clauses for the records
			       %% UCs = Update clauses for the records
			       Forms}
		      end;
		 (Form,{Recs,RForms,Forms}) ->
		      {Recs,RForms,[Form|Forms]}
	      end,
	      {[],{[],[],[]},[]},
	      AbsForms),
    case Records of
	[] -> % We don+t have records in our code
	    OtherForms;
	_ ->
	    mk_record(New,Extract,Update) % Creates the functions with the obtained clauses
		++
		[mk_updates()|OtherForms] % Adds to the AbsForms ...
    end.

%% Note that we are introducing new functions to the code (Abstract
%% forms). Since this module is now called after the call to
%% 'noimports', it would not work for the muCRL tools in the case there
%% were a module called 'record' that had a function called 'new',
%% 'extract' or 'update'.
%%
%% If we change the order of the modules, and for instance have this
%% module in the 'etoe' part (whith the modules still separated), then
%% it would be wrong if the user writes his/hers own functions called
%% 'record_new', 'record_extract' or 'record_update' with the same
%% arity than the ones we define here.

mk_record(New,Extract,Update) ->
  [{function,0,record_new,1,New}, 
   {function,0,record_extract,3,Extract},
   {function,0,record_update,4,Update}].

%% mk_new(atom(), [absform()]) -> [absform()]
%%
%% -record(RecordName, [Field1, Field2=E, ...])
%%
%% is translated into:
%%
%% RecordName() -> {mcrlrecord, RecordName, [undefined1, E]}

mk_new(Name,Fields) ->
  [{clause,0,[{atom,0,Name}],[],
          [{tuple,0,[{atom,0,mcrlrecord},
                     {atom,0,Name}|
		     map(fun({record_field,_,_}) ->
				 {atom,0,undefined};
			    ({record_field,_,_,E}) ->
				 expr(E)
			 end,Fields)]}]}].

%% mk_extract(atom(), [absform()]) -> [absform()]
%%
%% -record(RecordName, [Field1, Field2=E, ...])
%%
%% is translated into:
%%
%% Rec = {mcrlrecord, RecordName, F0,...,Fi} where I = length(Fields)-1 
%%
%% returns:
%%
%% ({mcrlrecord, RecordName, F0,...,Fi},RecordName, FieldName1) -> F0
%% ({mcrlrecord, RecordName, F0,...,Fi},RecordName, FieldName2) -> F1
%% ...
%% ({mcrlrecord, RecordName, F0,...,Fi},RecordName, FieldNamei) -> Fi
%%
%% e.g.:
%% -record(state, [field1ofstate, field2ofstate]).
%%
%% produces:
%%
%% ({mcrlrecord, state, F0, F1]}),state, field1ofstate) -> F0

mk_extract(Name,Fields) ->
    RecName = {atom,0,Name},
    Rec = {tuple,0,[{atom,0,mcrlrecord},RecName|
		    map(fun(N) -> 
				fieldvar(N)
			end,
			lists:seq(0,length(Fields)-1)
		       )]},
    foldl(fun(Field,Cs) ->
		  Cs++[mk_extract_clause(Rec,RecName,Field,length(Cs))]
	  end,[],Fields).

mk_extract_clause(Rec,RecName,{record_field,_,Field},Nr) ->
  {clause,0,[Rec,RecName,Field],[],[fieldvar(Nr)]};
mk_extract_clause(Rec,RecName,{record_field,_,Field,_},Nr) ->
  {clause,0,[Rec,RecName,Field],[],[fieldvar(Nr)]}.

%% mk_update(atom(), [absform()]) -> [absform()]
%%
%% -record(RecordName, [Field1, Field2=E, ...])
%%
%% is translated into:
%%
%% Rec = {mcrlrecord, RecordName, F0,...,Fi} where I = length(Fields)-1 
%%
%% returns:
%%
%% ({mcrlrecord, RecordName, F0,...,Fi, NewF, RecordName, FieldName1) -> {mcrlrecord, RecordName, NewF, F1,... Fi}
%% ({mcrlrecord, RecordName, F0,...,Fi, NewF, RecordName, FieldName2) -> {mcrlrecord, RecordName, F0, NewF,... Fi}
%% ...
%% ({mcrlrecord, RecordName, F0,...,Fi, NewF, RecordName, FieldNamei) -> {mcrlrecord, RecordName, F0, F1,... NewF}
%%
%% e.g.:
%% -record(state, [field1ofstate, field2ofstate]).
%%
%% produces:
%%
%% ({mcrlrecord, state, F0, F1}, NewF, state, field1ofstate) -> {mcrlrecord, state, NewF, F1}
%% ({mcrlrecord, state, F0, F1}, NewF, state, field2ofstate) -> {mcrlrecord, state, F0, NewF}


mk_update(Name,Fields) ->
    RecName = {atom,0,Name},
    Rec = {tuple,0,[{atom,0,mcrlrecord},RecName|
		    map(fun(N) -> 
				fieldvar(N)
			end,
			lists:seq(0,length(Fields)-1)
		       )]},
    foldl(fun(Field,Cs) ->
		  Cs++[mk_update_clause(Rec,RecName,Field,{var,0,'NewF'},length(Cs))]
	  end,[],Fields).

mk_update_clause(Rec,RecName,{record_field,_,Field},NewF,Nr) ->
  {clause,0,[Rec,RecName,Field,NewF],[],[changefield(Rec,Nr,NewF)]};
mk_update_clause(Rec,RecName,{record_field,_,Field,_},NewF,Nr) ->
  {clause,0,[Rec,RecName,Field,NewF],[],[changefield(Rec,Nr,NewF)]}.

changefield({tuple,0,Fs},Nr,NewF) ->
  {tuple,0,changefield2(Fs,Nr+2,NewF)}.  % first two are no real fields

changefield2([F|Fs],0,NewF) ->
  [NewF|Fs];
changefield2([F|Fs],N,NewF) ->
  [F|changefield2(Fs,N-1,NewF)].


%% Creates this new function:
%%
%% record_updates(Record, Name, []) ->
%%     Record;
%% record_updates(Record, Name, [{Field, NewF}, Fields]) ->
%%    record_updates( 
%%      (record_update(Record, Name, Field, NewF),
%%       Name,
%%       Fields).

mk_updates() ->
  Rec = {var,0,'Record'},
  RecName = {var,0,'Name'},
  Field = {var,0,'Field'},
  Fields = {var,0,'Fields'},
  NewF = {var,0,'NewF'},
  {function,0,record_updates,3,
    [{clause,0,[Rec,RecName,{nil,0}],[],[Rec]},
     {clause,0,[Rec,RecName,{cons,0,{tuple,0,[Field,NewF]},Fields}],[],
      [{call,0,{atom,0,record_updates},
       [{call,0,{atom,0,record_update},[Rec,RecName,Field,NewF]},
                                                      RecName,Fields]}]}
    ]
  }.


%% Given a name N, creates the variable FN
%% e.g: if N=1, returns {var, 0, 'F1'}

fieldvar(N) ->
  {var,0,list_to_atom("F"++integer_to_list(N))}.

list_to_abslist([]) ->
  {nil,0};
list_to_abslist([H|T]) ->
  {cons,0,H,list_to_abslist(T)}.


%+type file(filename()) -> [abs_form()] 
%
file(FileName) ->
  {ok,AbsForms} = epp:parse_file(FileName,["."],[]),
  forms(AbsForms).

%+type file(filename(),filename()) -> ok.
%
file(Source,Dest) ->
  AbsForms = tl(file(Source)),
  ok = 
    file:write_file(Dest, 
                    map(fun(A) -> erl_pp:form(A) end, AbsForms)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% The following code is a modification of the erl_id_trans (an Erlang
%% module that performs an identity parse transformation of Erlang
%% code

%% This is a map of the function 'clause' over the clause list

clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|clauses(Cs)];
clauses([]) -> [].

clause({clause,Line,H0,G0,B0}) ->
    H1 = head(H0), % Patterns of the function
    G1 = guard(G0),
    B1 = exprs(B0), % Body of the function
    {clause,Line,H1,G1,B1}.

head(Ps) -> patterns(Ps).

%%  These patterns are processed "sequentially" for purposes of variable
%%  definition etc.

patterns([P0|Ps]) ->
    P1 = pattern(P0),
    [P1|patterns(Ps)];
patterns([]) -> [].

string_to_conses([], Line, Tail) ->
    Tail;
string_to_conses([E|Rest], Line, Tail) ->
    {cons, Line, {integer, Line, E}, string_to_conses(Rest, Line, Tail)}.

pattern({var,Line,V}) -> {var,Line,V};
pattern({match,Line,L0,R0}) ->
    L1 = pattern(L0),
    R1 = pattern(R0),
    {match,Line,L1,R1};
pattern({integer,Line,I}) -> {integer,Line,I};
pattern({float,Line,F}) -> {float,Line,F};
pattern({atom,Line,A}) -> {atom,Line,A};
pattern({string,Line,S}) -> {string,Line,S};
pattern({nil,Line}) -> {nil,Line};
pattern({cons,Line,H0,T0}) ->
    H1 = pattern(H0),
    T1 = pattern(T0),
    {cons,Line,H1,T1};
pattern({tuple,Line,Ps0}) ->
    Ps1 = pattern_list(Ps0),
    {tuple,Line,Ps1};

%%pattern({struct,Line,Tag,Ps0}) 
%%    Ps1 = pattern_list(Ps0),
%%    {struct,Line,Tag,Ps1};

%%  It seems that we are not translating the records when they
%%  are in the pattern of a function declaration. TODO

pattern({record,Line,Name,Pfs0}) ->
    Pfs1 = pattern_fields(Pfs0),
    {record,Line,Name,Pfs1};
%% record_field occurs in query expressions
pattern({record_field,Line,Rec0,Field0}) ->
    Rec1 = expr(Rec0),
    Field1 = expr(Field0),
    {record_field,Line,Rec1,Field1};


pattern({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
pattern({op,Line,'++',{nil,_},R}) ->
    pattern(R);
pattern({op,Line,'++',{cons,Li,{integer,L2,I},T},R}) ->
    pattern({cons,Li,{integer,L2,I},{op,Li,'++',T,R}});
pattern({op,Line,'++',{string,Li,L},R}) ->
    pattern(string_to_conses(L, Li, R));
pattern({op,Line,Op,A}) ->
    {op,Line,Op,A};
pattern({op,Line,Op,L,R}) ->
    {op,Line,Op,L,R}.

pattern_grp([{bin_element,L1,E1,S1,T1} | Fs]) ->
    S2 = case S1 of
	     default ->
		 default;
	     _ ->
		 expr(S1)
	 end,
    T2 = case T1 of
	     default ->
		 default;
	     _ ->
		 bit_types(T1)
	 end,
    [{bin_element,L1,expr(E1),S2,T2} | pattern_grp(Fs)];
pattern_grp([]) ->
    [].

bit_types([]) ->
    [];
bit_types([Atom | Rest]) when atom(Atom) ->
    [Atom | bit_types(Rest)];
bit_types([{Atom, Integer} | Rest]) when atom(Atom), integer(Integer) ->
    [{Atom, Integer} | bit_types(Rest)].

%% -type pattern_list([Pattern]) -> [Pattern].
%%  These patterns are processed "in parallel" for purposes of variable
%%  definition etc.

pattern_list([P0|Ps]) ->
    P1 = pattern(P0),
    [P1|pattern_list(Ps)];
pattern_list([]) -> [].

%% -type pattern_fields([Field]) -> [Field].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

pattern_fields([{record_field,Lf,{atom,La,F},P0}|Pfs]) ->
    P1 = pattern(P0),
    [{record_field,Lf,{atom,La,F},P1}|pattern_fields(Pfs)];
pattern_fields([]) -> [].

guard([G0|Gs]) when list(G0) ->
    [guard0(G0) | guard(Gs)];
guard(L) ->
    guard0(L).

guard0([G0|Gs]) ->
    G1 = guard_test(G0),
    [G1|guard0(Gs)];
guard0([]) -> [].

%%  All function calls here must be type tests and only comparison
%%  operators are allowed here! Note record/2 tests are special and
%%  will be expanded later.

guard_test({atom,Line,true}) -> {atom,Line,true};
guard_test({call,Line,{atom,La,F},As0}) ->
    case erl_internal:type_test(F, length(As0)) of
	true -> As1 = gexpr_list(As0),
		{call,Line,{atom,La,F},As1}
    end;
guard_test({op,Line,Op,L0,R0}) ->
    case erl_internal:comp_op(Op, 2) of
	true ->
	    L1 = gexpr(L0),
	    R1 = gexpr(R0),			%They see the same variables
	    {op,Line,Op,L1,R1}
    end.

%% -type gexpr(GuardExpr) -> GuardExpr.

gexpr({var,Line,V}) -> {var,Line,V};
gexpr({integer,Line,I}) -> {integer,Line,I};
gexpr({float,Line,F}) -> {float,Line,F};
gexpr({atom,Line,A}) -> {atom,Line,A};
gexpr({string,Line,S}) -> {string,Line,S};
gexpr({nil,Line}) -> {nil,Line};
gexpr({cons,Line,H0,T0}) ->
    H1 = gexpr(H0),
    T1 = gexpr(T0),				%They see the same variables
    {cons,Line,H1,T1};
gexpr({tuple,Line,Es0}) ->
    Es1 = gexpr_list(Es0),
    {tuple,Line,Es1};
gexpr({record_index,Line,Name,Field0}) ->
    Field1 = gexpr(Field0),
    {record_index,Line,Name,Field1};
gexpr({record_field,Line,Rec0,Name,Field0}) ->
    Rec1 = gexpr(Rec0),
    Field1 = gexpr(Field0),
    {record_field,Line,Rec1,Name,Field1};
gexpr({call,Line,{atom,La,F},As0}) ->
    case erl_internal:guard_bif(F, length(As0)) of
	true -> As1 = gexpr_list(As0),
		{call,Line,{atom,La,F},As1}
    end;
gexpr({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
gexpr({op,Line,Op,A0}) ->
    case erl_internal:arith_op(Op, 1) of
	true -> A1 = gexpr(A0),
		{op,Line,Op,A1}
    end;
gexpr({op,Line,Op,L0,R0}) ->
    case erl_internal:arith_op(Op, 2) of
	true ->
	    L1 = gexpr(L0),
	    R1 = gexpr(R0),			%They see the same variables
	    {op,Line,Op,L1,R1}
    end.

%% -type gexpr_list([GuardExpr]) -> [GuardExpr].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

gexpr_list([E0|Es]) ->
    E1 = gexpr(E0),
    [E1|gexpr_list(Es)];
gexpr_list([]) -> [].

%% -type exprs([Expression]) -> [Expression].
%%  These expressions are processed "sequentially" for purposes of variable
%%  definition etc.

% ADDITION to erl_id_trans
exprs([{call,_,{remote,_,{atom,_,io},{atom,_,format}},_}|Es]) ->
   exprs(Es);
exprs([E0|Es]) ->
    E1 = expr(E0),
    [E1|exprs(Es)];
exprs([]) -> [].

%% -type expr(Expression) -> Expression.

expr({var,Line,V}) -> {var,Line,V};
expr({integer,Line,I}) -> {integer,Line,I};
expr({float,Line,F}) -> {float,Line,F};
expr({atom,Line,A}) -> {atom,Line,A};
expr({string,Line,S}) -> {string,Line,S};
expr({nil,Line}) -> {nil,Line};
expr({cons,Line,H0,T0}) ->
    H1 = expr(H0),
    T1 = expr(T0),				%They see the same variables
    {cons,Line,H1,T1};
expr({lc,Line,E0,Qs0}) ->
    Qs1 = lc_quals(Qs0),
    E1 = expr(E0),
    {lc,Line,E1,Qs1};
expr({tuple,Line,Es0}) ->
    Es1 = expr_list(Es0),
    {tuple,Line,Es1};
%%expr({struct,Line,Tag,Es0}) ->
%%    Es1 = pattern_list(Es0),
%%    {struct,Line,Tag,Es1};

%%%%%%%%%%% begin of record processing

%% #recordName.fieldName (returns the index of the field)
%%  
%% No change is made in the abstract form

expr({record_index,Line,Name,Field0}) ->
    Field1 = expr(Field0),
    {record_index,Line,Name,Field1};

%% #recordName{field1=Value, ..., fieldN=ValueN}.
%% is translated into:
%% record_updates(record_new(recordName), recordName, [{field1, value1}...]) 

expr({record,Line,Name,Inits0}) ->   % new record is created
    ?DEBUG("recordname ~p~n",[Name]),
    Inits1 = record_inits(Inits0),
    {call,Line,{atom,Line,record_updates},
       [{call,Line,{atom,Line,record_new},[{atom,0,Name}]},
        {atom,0,Name},list_to_abslist(Inits1)]};

%% Record#recordName.field1
%% is translated into:
%% record_extract(Record, recordName, field1)
  
expr({record_field,Line,Rec0,Name,Field0}) -> % extract value from record
    Rec1 = expr(Rec0),  % Rec0 is the expression to the left of # 
    Field1 = expr(Field0),
    {call,Line,{atom,0,record_extract},[Rec1,{atom,0,Name},Field1]};

%% Record#recordName(field1=value1, ..., fieldN=valueN)
%% is translated into:
%% record_updates(Record, recordName, [{field1, valueN}]...) 

expr({record,Line,Rec0,Name,Upds0}) ->  % record is updated
    Rec1 = expr(Rec0), % Rec0 is the expression to the left of # 
    Upds1 = record_updates(Upds0),
    {call,Line,{atom,Line,record_updates},
       [Rec1,{atom,0,Name},list_to_abslist(Upds1)]};

%% This abstract form corresponds to incorrect Erlang code, but can
%% still be parsed to an abstract form:
%%             Record.field (without specifying the record name)

expr({record_field,Line,Rec0,Field0}) ->
    Rec1 = expr(Rec0),
    Field1 = expr(Field0),
    {record_field,Line,Rec1,Field1};

%%%%%%%%%%% end of record processing

expr({block,Line,Es0}) ->
    %% Unfold block into a sequence.
    Es1 = exprs(Es0),
    {block,Line,Es1};
expr({'if',Line,Cs0}) ->
    Cs1 = icr_clauses(Cs0),
    {'if',Line,Cs1};
expr({'case',Line,E0,Cs0}) ->
    E1 = expr(E0),
    Cs1 = icr_clauses(Cs0),
    {'case',Line,E1,Cs1};
expr({'receive',Line,Cs0}) ->
    Cs1 = icr_clauses(Cs0),
    {'receive',Line,Cs1};
expr({'receive',Line,Cs0,To0,ToEs0}) ->
    To1 = expr(To0),
    ToEs1 = exprs(ToEs0),
    Cs1 = icr_clauses(Cs0),
    {'receive',Line,Cs1,To1,ToEs1};
expr({'fun',Line,Body}) ->
    case Body of
	{clauses,Cs0} ->
	    Cs1 = fun_clauses(Cs0),
	    {'fun',Line,{clauses,Cs1}};
	{function,F,A} ->
	    {'fun',Line,{function,F,A}};
	{function,M,F,A} ->			%This is an error in lint!
	    {'fun',Line,{function,M,F,A}}
    end;
expr({call,Line,F0,As0}) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    F1 = expr(F0),
    As1 = expr_list(As0),
    {call,Line,F1,As1};
expr({'catch',Line,E0}) ->
    %% No new variables added.
    E1 = expr(E0),
    {'catch',Line,E1};
expr({'query', Line, E0}) ->
    %% lc expression
    E = expr(E0),
    {'query', Line, E};
expr({match,Line,P0,E0}) ->
    E1 = expr(E0),
    P1 = pattern(P0),
    {match,Line,P1,E1};
expr({bin,Line,Fs}) ->
    Fs2 = pattern_grp(Fs),
    {bin,Line,Fs2};
expr({op,Line,Op,A0}) ->
    A1 = expr(A0),
    {op,Line,Op,A1};
expr({op,Line,Op,L0,R0}) ->
    L1 = expr(L0),
    R1 = expr(R0),				%They see the same variables
    {op,Line,Op,L1,R1};
%% The following are not allowed to occur anywhere!
expr({remote,Line,M0,F0}) ->
    M1 = expr(M0),
    F1 = expr(F0),
    {remote,Line,M1,F1}.

%% -type expr_list([Expression]) -> [Expression].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

expr_list([E0|Es]) ->
    E1 = expr(E0),
    [E1|expr_list(Es)];
expr_list([]) -> [].

%% -type record_inits([RecordInit]) -> [RecordInit].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is]) ->
    Val1 = expr(Val0),
    [{tuple,0,[{atom,La,F},Val1]}|record_inits(Is)];
record_inits([]) -> [].

%% -type record_updates([RecordUpd]) -> [RecordUpd].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us]) ->
    Val1 = expr(Val0),
    [{tuple,0,[{atom,La,F},Val1]}|record_updates(Us)];
record_updates([]) -> [].

%% -type icr_clauses([Clause]) -> [Clause].

icr_clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|icr_clauses(Cs)];
icr_clauses([]) -> [].

%% -type lc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_quals([{generate,Line,P0,E0}|Qs]) ->
    E1 = expr(E0),
    P1 = pattern(P0),
    [{generate,Line,P1,E1}|lc_quals(Qs)];
lc_quals([E0|Qs]) ->
    E1 = expr(E0),
    [E1|lc_quals(Qs)];
lc_quals([]) -> [].

%% -type fun_clauses([Clause]) -> [Clause].

fun_clauses([C0|Cs]) ->
    C1 = clause(C0),
    [C1|fun_clauses(Cs)];
fun_clauses([]) -> [].
