%% File: nanocop20_swi.pl  -  Version: 2.0  -  Date: 1 May 2021
%%
%% Purpose: nanocop: A Non-clausal Connection Prover
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage:   prove(F,P).  % where F is a first-order formula, e.g.
%%                       %  F=((p,all X:(p=>q(X)))=>all Y:q(Y))
%%                       %  and P is the returned connection proof
%%
%% Copyright: (c) 2016-2021 by Jens Otten
%% License:   GNU General Public License

:- set_prolog_flag(occurs_check,true).  % global occurs check on

:- dynamic(pathlim/0), dynamic(lit/4).

% definitions of logical connectives and quantifiers

:- op(1130,xfy,<=>). :- op(1110,xfy,=>). :- op(500, fy,'~').
:- op( 500, fy,all). :- op( 500, fy,ex). :- op(500,xfy,:).
% : - op(200,xfy,^).    % ← AJOUTER CETTE LIGNE pour indexation (I^K)^V

:- [i_operators].

% -----------------------------------------------------------------
% prove(F,Proof) - prove formula F



prove(F,Proof) :- prove2(F,[cut,comp(7)],Proof).

/*
prove2(F,Set,Proof) :-
    bmatrix(F,Set,Mat), retractall(lit(_,_,_,_)),
    assert_matrix(Mat), prove(Mat,1,Set,Proof).
*/
% --- Semantic Interpreter (English & Skolem Cleanup) ---
g4mic_interpret_path([], []).
g4mic_interpret_path([Lit|Rest], [Interpretation|Interps]) :-
    ( Lit = -Atom ->
        clean_skolem(Atom, CleanAtom),
        Interpretation = (CleanAtom = 'True')
    ;   clean_skolem(Lit, CleanLit),
        Interpretation = (CleanLit = 'False')
    ),
    g4mic_interpret_path(Rest, Interps).

% Helper to make Skolem terms (ID^[Args]) readable as skID(Args)
clean_skolem(Term, CleanTerm) :-
    ( var(Term) -> CleanTerm = 'X'
    ; compound(Term) ->
        Term =.. [F|Args],
        ( F = (^), Args = [ID|SubArgs] ->
            atomic_list_concat([sk, ID], SkName),
            maplist(clean_skolem, SubArgs, CleanArgs),
            CleanTerm =.. [SkName|CleanArgs]
        ; maplist(clean_skolem, Args, CleanArgs),
          CleanTerm =.. [F|CleanArgs]
        )
    ; CleanTerm = Term ).

% --- Main Engine Hook ---
prove2(F, Set, Proof) :-
    bmatrix(F, Set, Mat),
    nb_setval(g4mic_matrix, Mat),
    retractall(lit(_,_,_,_)),
    assert_matrix(Mat),
    prove(Mat, 1, Set, Proof).

%% is_nested_axiom_structure(+Term)
%% Détecte les structures avec axiomes imbriqués (UNA, etc.)
is_nested_axiom_structure([H|_]) :-
    is_list(H), !.
is_nested_axiom_structure([H|_]) :-
    compound(H),
    H = (_^_: _), !.


% start rule  (nanocop code again !!!!!!!!)
prove(Mat,PathLim,Set,[(I^0)^V:Proof]) :-
    ( member(scut,Set) -> ( append([(I^0)^V:Cla1|_],[!|_],Mat) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) -> true ;
        ( append(MatC,[!|_],Mat) -> member((I^0)^V:Cla1,MatC) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) ),
    prove(Cla1,Mat,[],[I^0],PathLim,[],Set,Proof).

prove(Mat,PathLim,Set,Proof) :-
    retract(pathlim) ->
    ( member(comp(PathLim),Set) -> prove(Mat,1,[],Proof) ;
      PathLim1 is PathLim+1, prove(Mat,PathLim1,Set,Proof) ) ;
    member(comp(_),Set) -> prove(Mat,1,[],Proof).

% axiom
prove([],_,_,_,_,_,_,[]).

% decomposition rule
prove([J:Mat1|Cla],MI,Path,PI,PathLim,Lem,Set,Proof) :-
    !, member(I^V:Cla1,Mat1),
    prove(Cla1,MI,Path,[I,J|PI],PathLim,Lem,Set,Proof1),
    prove(Cla,MI,Path,PI,PathLim,Lem,Set,Proof2),
    Proof=[J:I^V:Proof1|Proof2].

% reduction and extension rules
prove([Lit|Cla],MI,Path,PI,PathLim,Lem,Set,Proof) :-
    Proof=[Lit,I^V:[NegLit|Proof1]|Proof2],
    \+ (member(LitC,[Lit|Cla]), member(LitP,Path), LitC==LitP),
    (-NegLit=Lit;-Lit=NegLit) ->
       ( member(LitL,Lem), Lit==LitL, _ClaB1=[], Proof1=[],I=l,V=[]
         ;
         member(NegL,Path), unify_with_occurs_check(NegL,NegLit),
         _ClaB1=[], Proof1=[],I=r,V=[]
         ;
         lit(NegLit,ClaB,Cla1,Grnd1),
         ( Grnd1=g -> true ; length(Path,K), K<PathLim -> true ;
           \+ pathlim -> assert(pathlim), fail ),
         prove_ec(ClaB,Cla1,MI,PI,I^V:ClaB1,MI1),
         prove(ClaB1,MI1,[Lit|Path],[I|PI],PathLim,Lem,Set,Proof1)
       ),
       ( member(cut,Set) -> ! ; true ),
       prove(Cla,MI,Path,PI,PathLim,[Lit|Lem],Set,Proof2).

% extension clause (e-clause)
prove_ec((I^K)^V:ClaB,IV:Cla,MI,PI,ClaB1,MI1) :-
    append(MIA,[(I^K1)^V1:Cla1|MIB],MI), length(PI,K),
    ( ClaB=[J^K:[ClaB2]|_], member(J^K1,PI),
      unify_with_occurs_check(V,V1), Cla=[_:[Cla2|_]|_],
      append(ClaD,[J^K1:MI2|ClaE],Cla1),
      prove_ec(ClaB2,Cla2,MI2,PI,ClaB1,MI3),
      append(ClaD,[J^K1:MI3|ClaE],Cla3),
      append(MIA,[(I^K1)^V1:Cla3|MIB],MI1)
      ;
      (\+member(I^K1,PI);V\==V1) ->
      ClaB1=(I^K)^V:ClaB, append(MIA,[IV:Cla|MIB],MI1) ).

% -----------------------------------------------------------------
% positiveC(Clause,ClausePos) - generate positive start clause

positiveC([],[]).
positiveC([M|C],[M3|C2]) :-
    ( M=I:M1 -> positiveM(M1,M2),M2\=[],M3=I:M2 ; -_\=M,M3=M ),
    positiveC(C,C2).

positiveM([],[]).
positiveM([I:C|M],M1) :-
    ( positiveC(C,C1) -> M1=[I:C1|M2] ; M1=M2 ), positiveM(M,M2).

% -----------------------------------------------------------------
% bmatrix(Formula,Set,Matrix) - generate indexed matrix

bmatrix(F,Set,M) :-
    univar(F,[],F1),
    ( member(conj,Set), F1=(A=>C) ->
        bmatrix(A,1,MA,[],[],_,1,J,_),
        bmatrix(C,0,MC,[],[],_,J,_,_), ( member(reo(I),Set) ->
        reorderC([MA],[_:MA1],I), reorderC([MC],[_:MC1],I) ;
        _:MA1=MA, _:MC1=MC ), append(MC1,[!|MA1],M)
      ; bmatrix(F1,0,M1,[],[],_,1,_,_), ( member(reo(I),Set) ->
        reorderC([M1],[_:M],I) ; _:M=M1 ) ).

%% Ajout
bmatrix(![X]:F1, Pol, M, FreeV, FV, Paths, I, I1, K) :- !,
    bmatrix(all X:F1, Pol, M, FreeV, FV, Paths, I, I1, K).

bmatrix(?[X]:F1, Pol, M, FreeV, FV, Paths, I, I1, K) :- !,
    bmatrix(ex X:F1, Pol, M, FreeV, FV, Paths, I, I1, K).
%%% fin de l'ajout

bmatrix((F1<=>F2),Pol,M,FreeV,FV,Paths,I,I1,K) :- !,
    bmatrix(((F1=>F2),(F2=>F1)),Pol,M,FreeV,FV,Paths,I,I1,K).

bmatrix((~F),Pol,M,FreeV,FV,Paths,I,I1,K) :- !,
    Pol1 is (1-Pol), bmatrix(F,Pol1,M,FreeV,FV,Paths,I,I1,K).

bmatrix(F,Pol,M,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(uni,C,Pol), !,
    bmatrix(F1,Pol,M,FreeV,[X|FV],Paths,I,I1,K).

bmatrix(F,Pol,M,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(exist,C,Pol), !,
    append(FreeV,FV,FreeV1), I2 is I+1,
    copy_term((X,F1,FreeV1),((I^FreeV1),F2,FreeV1)),
    bmatrix(F2,Pol,M,FreeV,FV,Paths,I2,I1,K).

bmatrix(F,Pol,J^K:M3,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(alpha,C,Pol,Pol1,Pol2), !,
    bmatrix(F1,Pol1,J^K:M1,FreeV,FV,Paths1,I,I2,K),
    bmatrix(F2,Pol2,_:M2,FreeV,FV,Paths2,I2,I1,K),
    Paths is Paths1*Paths2,
    (Paths1>Paths2 -> append(M2,M1,M3) ; append(M1,M2,M3)).

bmatrix(F,Pol,I^K:[(I2^K)^FV1:C3],FreeV,FV,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(beta,C,Pol,Pol1,Pol2), !,
    ( FV=[] -> FV1=FV, F3=F1, F4=F2 ;
      copy_term((FV,F1,F2,FreeV),(FV1,F3,F4,FreeV)) ),
    append(FreeV,FV1,FreeV1),  I2 is I+1, I3 is I+2,
    bmatrix(F3,Pol1,M1,FreeV1,[],Paths1,I3,I4,K),
    bmatrix(F4,Pol2,M2,FreeV1,[],Paths2,I4,I1,K),
    Paths is Paths1+Paths2,
    ( (M1=_:[_^[]:C1];[M1]=C1), (M2=_:[_^[]:C2];[M2]=C2) ->
      (Paths1>Paths2 -> append(C2,C1,C3) ; append(C1,C2,C3)) ).

bmatrix(A,0,I^K:[(I2^K)^FV1:[A1]],FreeV,FV,1,I,I1,K)  :-
    copy_term((FV,A,FreeV),(FV1,A1,FreeV)), I2 is I+1, I1 is I+2.

bmatrix(A,1,I^K:[(I2^K)^FV1:[-A1]],FreeV,FV,1,I,I1,K) :-
    copy_term((FV,A,FreeV),(FV1,A1,FreeV)), I2 is I+1, I1 is I+2.

bma(alpha,',',1,1,1). bma(alpha,(;),0,0,0). bma(alpha,(=>),0,1,0).
bma(beta,',',0,0,0).  bma(beta,(;),1,1,1).  bma(beta,(=>),1,0,1).
bma(exist,all,0). bma(exist,ex,1). bma(uni,all,1). bma(uni,ex,0).

% -----------------------------------------------------------------
% assert_matrix(Matrix) - write matrix into Prolog's database

assert_matrix(M) :-
    member(IV:C,M), assert_clauses(C,IV:ClaB,ClaB,IV:ClaC,ClaC).
assert_matrix(_).

assert_clauses(C,ClaB,ClaB1,ClaC,ClaC1) :- !,
    append(ClaD,[M|ClaE],C),
    ( M=J:Mat -> append(MatA,[IV:Cla|MatB],Mat),
                 append([J:[IV:ClaB2]|ClaD],ClaE,ClaB1),
                 append([IV:ClaC2|MatA],MatB,Mat1),
                 append([J:Mat1|ClaD],ClaE,ClaC1),
                 assert_clauses(Cla,ClaB,ClaB2,ClaC,ClaC2)
               ; append(ClaD,ClaE,ClaB1), ClaC1=C,
                 (ground(C) -> Grnd=g ; Grnd=n),
                 assert(lit(M,ClaB,ClaC,Grnd)), fail ).

% -----------------------------------------------------------------
%  reorderC([Matrix],[MatrixReo],I) - reorder clauses

reorderC([],[],_).
reorderC([M|C],[M1|C1],I) :-
    ( M=J:M2 -> reorderM(M2,M3,I), length(M2,L), K is I mod (L*L),
      mreord(M3,M4,K), M1=J:M4 ; M1=M ), reorderC(C,C1,I).

reorderM([],[],_).
reorderM([J:C|M],[J:D|M1],I) :- reorderC(C,D,I), reorderM(M,M1,I).

mreord(M,M,0) :- !.
mreord(M,M1,I) :-
    mreord1(M,I,X,Y), append(Y,X,M2), I1 is I-1, mreord(M2,M1,I1).

mreord1([],_,[],[]).
mreord1([C|M],A,M1,M2) :-
    B is 67*A, I is B rem 101, I1 is I mod 2,
    ( I1=1 -> M1=[C|X], M2=Y ; M1=X, M2=[C|Y] ), mreord1(M,I,X,Y).

% ----------------------------
% create unique variable names

univar(X,_,X)  :- (atomic(X);var(X);X==[[]]), !.
univar(F,Q,F1) :-
    F=..[A,B|T], ( (A=ex;A=all),B=X:C -> delete2(Q,X,Q1),
    copy_term((X,C,Q1),(Y,D,Q1)), univar(D,[Y|Q],E), F1=..[A,Y:E] ;
    univar(B,Q,B1), univar(T,Q,T1), F1=..[A,B1|T1] ).

% delete variable from list
delete2([],_,[]).
delete2([X|T],Y,T1) :- X==Y, !, delete2(T,Y,T1).
delete2([X|T],Y,[X|T1]) :- delete2(T,Y,T1).


% =========================================================================
% PRETTY-PRINTER FOR COUNTER-MODELS (minimaliste)
% =========================================================================

%% pretty_print_countermodel(+Model)
pretty_print_countermodel([]) :-
    write('     ∅'), nl, nl, !.

pretty_print_countermodel(Model) :-
    is_list(Model),
    Model \= [],
    ! ,
    write('     '),
    format_model_compact(Model),
    nl, nl.

pretty_print_countermodel(Model) :-
    format('     ~w~n~n', [Model]).

%% format_model_compact(+List)
%% Affiche le modèle sur une ligne :  a = ⊤, b = ⊥, ...
format_model_compact([Interp]) :-
    ! ,
    format_compact_assignment(Interp).

format_model_compact([Interp|Rest]) :-
    format_compact_assignment(Interp),
    write(', '),
    format_model_compact(Rest).

%% format_compact_assignment(+Assignment)
%% Formate une assignation :  a = ⊤ ou p(x) = ⊥
format_compact_assignment((Atom = Value)) :-
    Atom = (A = B),  % Cas égalité
    !,
    format_value(Value, DisplayValue),
    format('(~w = ~w) = ~w', [A, B, DisplayValue]).

format_compact_assignment((Pred = Value)) :-
    format_value(Value, DisplayValue),
    format('~w = ~w', [Pred, DisplayValue]).

format_compact_assignment(Other) :-
    format('~w', [Other]).

%% format_value(+Value, -DisplayValue)
%% Convertit True/False en ⊤/⊥
format_value(true, '⊤') :- !.
format_value('True', '⊤') :- !.
format_value(false, '⊥') :- !.
format_value('False', '⊥') :- !.
format_value(V, V).
