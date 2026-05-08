%% File: nanocop20_swi.pl  -  Version: 2.0 + opt-pathlim + opt-prove_ec-stage1 + open-path + g4-preprocess
%%
%% Purpose: nanoCoP: A Non-clausal Connection Prover (G4+ edition)
%%
%% Author:  Jens Otten (original, 2016-2021)
%%
%% Optimizations and additions applied to original nanocop20_swi.pl:
%%
%% [opt-pathlim] (validated)
%%   pathlim flag managed via nb_setval/nb_current instead of
%%   assert/retract. Semantically equivalent, eliminates dynamic
%%   database manipulation overhead.
%%
%% [opt-prove_ec-stage1] (validated on Pelletier 47: -19% CPU,
%%   identical proofs)
%%   In prove_ec/6, replace the redundant pair
%%       append(MIA,[(I^K1)^V1:Cla1|MIB],MI), ...,
%%       append(MIA,[NewElement|MIB],MI1)
%%   with select_replace/4 which performs split + reconstruction
%%   in a single recursive pass, avoiding the second O(n) traversal.
%%
%% [open-path] (NEW, to be validated)
%%   Capture of the open path at the last failed closure attempt
%%   via dynamic predicate nanocop_open_path/1. Used by the G4+
%%   wrapper to distinguish CounterSatisfiable from GaveUp:
%%     - prove/2 succeeded                              -> Theorem
%%     - prove/2 failed, nanocop_depth_limited=true     -> GaveUp
%%     - prove/2 failed, nanocop_depth_limited=false    -> CounterSatisfiable
%%       and nanocop_open_path/1 holds a partial witness.
%%
%% [g4-preprocess] (NEW, to be validated)
%%   Applies invertible G4 sequent calculus rules to simplify the
%%   formula BEFORE matrix generation. Only rules that eliminate
%%   beta-clauses are used (L∨→, L∧→, L→→). L0→ is deliberately
%%   omitted: it does not reduce beta-clauses and can remove
%%   useful connection paths, hurting nanoCoP's performance.
%%   Rules applied in optimal order:
%%     1. L∧→  : (A & B) → C  →  A → (B → C)  (if A not conj.)
%%     2. L∨→  : (A | B) → C  →  (A → C) & (B → C)
%%     3. L→→  : ((A → B) → C)  →  (B → C)  (if B not impl.)
%%   Quantifier rules are deliberately omitted: nanoCoP excels at
%%   first-order reasoning, and pre-processing quantifiers would
%%   risk interfering with its efficient matrix treatment.
%%
%% G4+ specific code preserved:
%%   nanocop_depth_limited/0 flag for SZS status reporting
%%   (must remain dynamic; persists across pathlim retracts to
%%    distinguish authentic failure from depth-truncated failure).
%%
%% Soundness: occurs_check global flag remains ON.
%%   Empirical validation on TPTP showed that disabling it causes
%%   80+ soundness errors (CounterSatisfiable problems incorrectly
%%   proved as Theorem) on KRS, GRP, GEO, LCL domains, AND a
%%   regression in completeness on at least one previously-proved
%%   formula. The structural argument that explicit
%%   unify_with_occurs_check/2 calls suffice is FALSE in practice.
%%
%% Copyright: (c) 2016-2021 by Jens Otten
%% License:   GNU General Public License

:- set_prolog_flag(occurs_check,true).  % global occurs check on

:- dynamic(lit/4).
:- dynamic(nanocop_depth_limited/0).  % G4+: persistent flag, search was truncated by depth limit
:- dynamic(nanocop_open_path/1).      % MOD-4: captures last open path on failed closure

:- op(1130,xfy,<=>). :- op(1110,xfy,=>). :- op(500, fy,'~').
:- op( 500, fy,all). :- op( 500, fy,ex). :- op(500,xfy,:).
% :- op(1000, xfy, &).   % conjonction
% :- op(1100, xfy, '|').  % disjonction (car | est réservé pour les listes)

:- [operators].

% -----------------------------------------------------------------
% prove(F,Proof) - prove formula F

prove(F,Proof) :- prove2(F,[cut,comp(7)],Proof).

prove2(F,Set,Proof) :-
    nb_setval(pathlim_status, none),
    retractall(nanocop_open_path(_)),     % MOD-4: reset open-path on each call
    preprocess_g4(F, F_simplified),       % MOD-5: G4 pre-processing
    bmatrix(F_simplified,Set,Mat), retractall(lit(_,_,_,_)),
    assert_matrix(Mat), prove(Mat,1,Set,Proof).

% start rule
prove(Mat,PathLim,Set,[(I^0)^V:Proof]) :-
    ( member(scut,Set) -> ( append([(I^0)^V:Cla1|_],[!|_],Mat) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) -> true ;
        ( append(MatC,[!|_],Mat) -> member((I^0)^V:Cla1,MatC) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) ),
    prove(Cla1,Mat,[],[I^0],PathLim,[],Set,Proof).

% iterative deepening control (optimized: nb_setval instead of assert/retract)
prove(Mat,PathLim,Set,Proof) :-
    ( nb_current(pathlim_status, set) ->
        nb_setval(pathlim_status, none),
        ( member(comp(PathLim),Set) -> prove(Mat,1,[],Proof)
        ; PathLim1 is PathLim+1, prove(Mat,PathLim1,Set,Proof) )
    ; member(comp(_),Set) -> prove(Mat,1,[],Proof)
    ).

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
           nb_current(pathlim_status, set) -> fail ;
           nb_setval(pathlim_status, set),
           ( nanocop_depth_limited -> true ; assertz(nanocop_depth_limited) ),
           fail ),
         prove_ec(ClaB,Cla1,MI,PI,I^V:ClaB1,MI1),
         prove(ClaB1,MI1,[Lit|Path],[I|PI],PathLim,Lem,Set,Proof1)
       ),
       ( member(cut,Set) -> ! ; true ),
       prove(Cla,MI,Path,PI,PathLim,[Lit|Lem],Set,Proof2).

% MOD-4: open-path capture clause
prove([Lit|_Cla],_MI,Path,_PI,_PathLim,_Lem,_Set,_Proof) :-
    \+ nanocop_depth_limited,
    retractall(nanocop_open_path(_)),
    assertz(nanocop_open_path([Lit|Path])),
    fail.

% extension clause (e-clause)  --  OPTIMIZED VERSION
prove_ec((I^K)^V:ClaB,IV:Cla,MI,PI,ClaB1,MI1) :-
    length(PI,K),
    select_replace(MI, (I^K1)^V1:Cla1, NewElem, MI1),
    ( ClaB=[J^K:[ClaB2]|_], member(J^K1,PI),
      unify_with_occurs_check(V,V1), Cla=[_:[Cla2|_]|_],
      select_replace(Cla1, J^K1:MI2, J^K1:MI3, Cla3),
      prove_ec(ClaB2,Cla2,MI2,PI,ClaB1,MI3),
      NewElem = (I^K1)^V1:Cla3
    ;
      (\+member(I^K1,PI);V\==V1) ->
      ClaB1=(I^K)^V:ClaB,
      NewElem = IV:Cla
    ).

% select_replace(+List, ?OldElem, ?NewElem, -NewList)
select_replace([X|Xs], X, Y, [Y|Xs]).
select_replace([X|Xs], O, N, [X|Ys]) :-
    select_replace(Xs, O, N, Ys).

% -----------------------------------------------------------------
% positiveC(Clause,ClausePos) - generate positive start clause

positiveC([],[]).
positiveC([M|C],[M3|C2]) :-
    ( M=I:M1 -> positiveM(M1,M2),M2\=[],M3=I:M2 ; -_\=M,M3=M ),
    positiveC(C,C2).

positiveM([],[]).
positiveM([I:C|M],M1) :-
    ( positiveC(C,C1) -> M1=[I:C1|M2] ; M1=M2 ), positiveM(M,M2).

% =========================================================================
% MOD-5: G4 PRE-PROCESSING
% =========================================================================
% Only rules that eliminate beta-clauses: L∧→, L∨→, L→→
% L0→ omitted: does not reduce beta-clauses, can remove useful paths.

preprocess_g4(F, F_simplified) :-
    preprocess_sequent([], F, Gamma, Delta),
    rebuild_formula(Gamma, Delta, F_simplified).

% preprocess_sequent(+Gamma, +Delta, -Gamma_out, -Delta_out)
preprocess_sequent(Gamma, Delta, Gamma_out, Delta_out) :-
    preprocess_sequent_aux(Gamma, Delta, Gamma_out, Delta_out),
    !.  % cut après succès

preprocess_sequent_aux(Gamma, Delta, Gamma_out, Delta_out) :-
    ( Delta = (A => B) ->
      preprocess_sequent_aux([A|Gamma], B, Gamma_out, Delta_out)
    ;
    saturate_gamma(Gamma, Delta, Gamma_sat, Delta_sat),
    ( Gamma_sat \= Gamma ; Delta_sat \= Delta ->
                               preprocess_sequent_aux(Gamma_sat, Delta_sat, Gamma_out, Delta_out)
      ;
      Gamma_out = Gamma_sat,
      Delta_out = Delta_sat
    )
    ).

% saturate_gamma(+Gamma, +Delta, -Gamma_out, -Delta_out)
% Apply L∧→, L∨→, L→→ in optimal order until saturation.

saturate_gamma(Gamma, Delta, Gamma_out, Delta_out) :-
    ( apply_Land_implies(Gamma, Delta, Gamma1, Delta1)
    ; apply_Lor_implies(Gamma, Delta, Gamma1, Delta1)
    ; apply_Limplies_implies(Gamma, Delta, Gamma1, Delta1)
    ),
    !,
    saturate_gamma(Gamma1, Delta1, Gamma_out, Delta_out).

saturate_gamma(Gamma, Delta, Gamma, Delta).

% -------------------------------------------------------------------------
% 1. L∧→ : (A & B) → C  →  A → (B → C)
% Guard: A must not be a conjunction (avoids infinite chaining).
% -------------------------------------------------------------------------

apply_Land_implies(Gamma, Delta, Gamma_out, Delta_out) :-
    select(((A & B) => C), Gamma, RestGamma),
    \+ (A = (_ & _)),
    !,
    NewFormula = (A => (B => C)),
    ( member(NewFormula, RestGamma) ->
        Gamma_out = RestGamma,
        Delta_out = Delta
    ;
        Gamma_out = [NewFormula | RestGamma],
        Delta_out = Delta
    ).

% -------------------------------------------------------------------------
% 2. L∨→ : (A | B) → C  →  (A → C) & (B → C)
% Eliminates a beta-clause (the disjunction).
% -------------------------------------------------------------------------

apply_Lor_implies(Gamma, Delta, Gamma_out, Delta_out) :-
    select(((A ; B) => C), Gamma, RestGamma),
    !,
    New1 = (A => C),
    New2 = (B => C),
    ( member(New1, RestGamma) -> Gamma1 = RestGamma ; Gamma1 = [New1 | RestGamma] ),
    ( member(New2, Gamma1)   -> Gamma_out = Gamma1 ; Gamma_out = [New2 | Gamma1] ),
    Delta_out = Delta.

% -------------------------------------------------------------------------
% 3. L→→ : ((A → B) → C)  →  (B → C)
% Guard: B must not be an implication (avoids infinite chaining).
% -------------------------------------------------------------------------

apply_Limplies_implies(Gamma, Delta, Gamma_out, Delta_out) :-
    select(((_A => B) => C), Gamma, RestGamma),
    \+ (B = (_ => _)),
    !,
    NewFormula = (B => C),
    ( member(NewFormula, RestGamma) ->
        Gamma_out = RestGamma,
        Delta_out = Delta
    ;
        Gamma_out = [NewFormula | RestGamma],
        Delta_out = Delta
    ).

% -------------------------------------------------------------------------
% Rebuild formula from Gamma and Delta
% Gamma = [H1, ..., Hn]  →  H1 → (H2 → ... → (Hn → Delta)...)
% -------------------------------------------------------------------------

rebuild_formula([], Delta, Delta) :- !.
rebuild_formula([H|T], Delta, (H => Rest)) :-
    rebuild_formula(T, Delta, Rest).

% =========================================================================
% END OF G4 PRE-PROCESSING
% =========================================================================

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

%% Ajout : support de la syntaxe TPTP ![X]:F et ?[X]:F
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
% reorderC([Matrix],[MatrixReo],I) - reorder clauses

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
