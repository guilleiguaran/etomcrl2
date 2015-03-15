
-define(DEBUG(F,A),io:format("debug (~p): "++F,[?MODULE|A])).
%-define(DEBUG(F,A),ok).
-define(ERROR(Line,F,A),io:format("error line ~p: "++F,[Line|A])).
-define(ERRORSTRING(String),io:format(String)).
-define(WARNING(Line,F,A),io:format("warning line ~p: "++F,[Line|A])).

-define(TempDir,begin
                  case os:getenv("MCRLTEMP") of
                       false -> "/tmp";
                       _ -> filename:absname(os:getenv("MCRLTEMP"))
                  end
                end).
-define(MCRLDir,begin
                  case os:getenv("MCRLDIR") of
                       false -> ".";
                       _ -> filename:absname(os:getenv("MCRLDIR"))
                  end
                end).
-define(MCRLExt,".mCRL").
-define(PMCRLFile,"tomcrl").

-define(MCRLSelf,'MCRLSelf').

-define(Term,"Term").
-define(Natural,"Natural").
-define(MaxInt,5).

-define(MCRL_RESERVED_VARS,['F','T',?MCRLSelf,'MCRLBool',
                            'MCRLTerm1','MCRLTerm2']).
-define(MCRL_TERM_CONSTRUCTORS,
          [{pid,[{"N",?Natural}]},
           {int,[{"N",?Natural}]},
           {nil,[]},
           {cons,[{"H1",?Term},{"T1",?Term}]},
           {tuplenil,[{"H1",?Term}]},
           {tuple,[{"H1",?Term},{"T1",?Term}]}
          ]).

-define(BIN_OPERATORS,[{'==',"equal"},
                       {'++',"list_append"},{'--',"list_subtract"},
                       {'+',"mcrl_plus"},{'-',"mcrl_minus"},{'*',"mcrl_times"},
                       {'div',"mcrl_div"},{'rem',"mcrl_rem"},
                       {'=<',"mcrl_leq"},{'>=',"mcrl_geq"},
                       {'<',"mcrl_less"},{'>',"mcrl_greater"},
                       {'and',"and"},{'or',"or"}]).


-define(GEN_SERVER_CALL,{remote,_,{atom,_,gen_server},{atom,_,call}}).
-define(SERVERLOOP,serverloop). % in etopmcrl
-define(MCRLSERVER,mcrlserver). % in etopmcrl

-define(conftau,conftau).
-define(emptybuffer,emptybuffer).

-define(See_as_Bifs,[{lists,member,2}]).

-define(SIDEEFFECTS,[{{gen_server,call,2},{gscall,3},buffercall,3},
                     {{gen_server,cast,2},{gscast,2},buffercast,2},
                     {{gshcall,3},{handle_call,3},call,3},
                     {{gshcast,2},{handle_cast,2},cast,2},
                     {{gen_server,reply,2},{gen_server,replied,3},reply,3}]).

