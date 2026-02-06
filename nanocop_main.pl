%% File: nanocop_main.pl  -  Version: 2.0  -  Date: 20 January 2020
%%
%% Purpose: Call the nanoCoP core prover for a given formula
%%
%% Author:   Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage:   nanocop_main(X,S,R). % proves formula in file X with
%%                               %  settings S and returns result R
%%
%% Copyright:  (c) 2016-2020 by Jens Otten
%% License:   GNU General Public License

: - assert(prolog(swi)).  % Prolog dialect (eclipse/swi)
:- dynamic(axiom_path/1).

% execute predicates specific to Prolog dialect

: - \+ prolog(eclipse) -> true ;
   nodbgcomp,  % switch off debugging mode
   set_flag(print_depth,10000),  % set print depth
   set_flag(variable_names,off),  % print internal variable names
   ( getenv('TPTP',Path) -> Path1=Path ; Path1='' ),
   retract_all(axiom_path(_)), assert(axiom_path(Path1)),
   [nanocop20].  % load nanoCoP core prover

:- prolog(eclipse) -> true ;
   set_prolog_flag(print_write_options,[quoted(false)]),
   ( getenv('TPTP',Path) -> Path1=Path ; Path1='' ),
   retractall(axiom_path(_)), assert(axiom_path(Path1)),
   [nanocop20_swi].  % load nanoCoP core prover

% CRITICAL FIX: Load in correct order
:- [nanocop_tptp2].  % load TPTP support FIRST (declares operators)
:- [nanocop_proof].  % load proof presentation SECOND (uses operators)

%%% call the nanoCoP core prover

nanocop_main(File,Settings,Result) :-
    axiom_path(AxPath), ( AxPath='' -> AxDir='' ;
    name(AxPath,AxL), append(AxL,[47],DirL), name(AxDir,DirL) ),
    ( leancop_tptp2(File,AxDir,[_],F,Conj) ->
      Problem=F ; [File], f(Problem), Conj=non_empty ),
    ( Conj\=[] -> Problem1=Problem ; Problem1=(~Problem) ),
    ( member(noeq,Settings) -> Problem1=Problem2 ;
        leancop_equal(Problem1,Problem2) ),
    ( prove2(Problem2,Settings,Proof) ->
      ( Conj\=[] -> Result='Theorem' ; Result='Unsatisfiable' ) ;
      ( Conj\=[] -> Result='Non-Theorem' ; Result='Satisfiable' )
    ),
    bmatrix(Problem2,Settings,Matrix),
    output_result(File,Matrix,Proof,Result,Conj).

% print status and connection proof

output_result(File,Matrix,Proof,Result,Conj) :-
    ( Conj\=[] -> Art=' is a ' ; Art=' is ' ), nl,
    print(File), print(Art), print(Result), nl,
    var(Proof) -> true ; print('Start of proof'),
      ( Result='Theorem' -> Out=' for ' ; Out=' for negated ' ),
      print(Out), print(File), nl, nanocop_proof(Matrix,Proof),
      print('End of proof'), print(Out), print(File), nl.
