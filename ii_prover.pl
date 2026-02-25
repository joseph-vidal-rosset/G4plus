% =========================================================================
% G4+ FOL Prover -- Core Engine
% =========================================================================
%
% Sequent calculus theorem prover for first-order logic based on
% Roy Dyckhoff's G4 calculus with extensions for classical logic.
%
% Key features:
% - Contraction-free G4 rules (efficient proof search)
% - Progressive logic detection: minimal -> intuitionistic -> classical
% - Eigenvariable management for quantifier rules
% - Optimized rule ordering for performance
%
% Rule ordering rationale:
% - Rforall first: eigenvariable introduced before any left rules fire
% - L& before L0->: decompose conjunctions before modus ponens
% - L0-> with guard: avoid re-deriving already present formulas
% - L\/-> before branching rules: deterministic simplification first
% - IP just before R->: classical law applied before implication decomposition
% - Lforall after right rules: universal instantiation guided by Skolem terms
% =========================================================================

% =========================================================================
% EIGENVARIABLE REGISTRY (backtrackable global state)
% =========================================================================

init_eigenvars :- b_setval(g4_eigenvars, []).

member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem, !.

% =========================================================================
% RULE 0: AXIOM
% =========================================================================

g4mic_ax(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A \= (_ & _),
    A \= (_ | _),
    A \= (_ => _),
    A \= (! _),
    A \= (? _),
    Delta = [B],
    unify_with_occurs_check(A, B).

% =========================================================================
% g4mic_proves/7
% g4mic_proves(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut,
%              LogicLevel, Proof)
% =========================================================================

% --- Rule 0: Axiom (tested first, non-tabled) ----------------------------
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% --- Rule 1: L-bot -----------------------------------------------------
g4mic_proves(Gamma>Delta, _, _, SI, SI, LL, lbot(Gamma>Delta, #)) :-
    member(LL, [intuitionistic, classical]),
    member(#, Gamma), !.

% --- Rule 2: R-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rcond(Gamma>Delta, P)) :-
    Delta = [A => B], !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).
% =====================================================================
% PROPOSITIONAL RULES (deterministic, no branching)
%======================================================================
% LEFT RULES
%======================================================================
% --- Rule 3: L& -----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, land(Gamma>Delta, P)) :-
    select((A & B), Gamma, G1), !,
    g4mic_proves([A, B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 4: TNE (triple negation elimination) ----------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],
    member(LongNeg, Gamma),
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2, !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).

% --- Rule 5: L0-> (modus ponens on context) -------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, l0cond(Gamma>Delta, P)) :-
    select((A => B), Gamma, G1),
    member(A, G1),
    !,
    g4mic_proves([B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 6: L&-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, landto(Gamma>Delta, P)) :-
    select(((A & B) => C), Gamma, G1), !,
    g4mic_proves([(A => (B => C)) | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 7: L\/-> (optimized) --------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lorto(Gamma>Delta, P)) :-
    select(((A | B) => C), Gamma, G1), !,
    ( member(A, G1), member(B, G1) ->
        g4mic_proves([B=>C, A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(A, G1) ->
        g4mic_proves([A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(B, G1) ->
        g4mic_proves([B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ;
        g4mic_proves([A=>C, B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ).

% =========================================================================
% Intuitionistic rule Lbot and classical rule IP
% =========================================================================

% --- Rule 8: IP (indirect proof -- classical only) ------------------------
% Placed just before R->: classical law applied before decomposition
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Th > 0,
    g4mic_proves([(A => #) | Gamma]>[#], FV, Th, SI, SO, classical, P).

% =========================================================================
% BRANCHING RULES
% =========================================================================
%% Left rules first
%==========================================================================

% --- Rule 9: L->-> --------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A => B) => C), Gamma, G1),
    \+ (B = #, member(A, G1)),
    !,
    g4mic_proves([A, (B => C) | G1]>[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves([C | G1]>Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 10: L\/ (left disjunction) ---------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lor(Gamma>Delta, P1, P2)) :-
    select((A | B), Gamma, G1), !,
    g4mic_proves([A | G1]>Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves([B | G1]>Delta, FV, Th, J1, SO, LL, P2).

%=========================================================================
% RIGHT RULES
%========================================================================

% --- Rule 11: R\/ ----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ror(Gamma>Delta, P)) :-
    Delta = [(A | B)], !,
    (   g4mic_proves(Gamma>[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(Gamma>[B], FV, Th, SI, SO, LL, P)
    ).

% --- Rule 12: R& ----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(Gamma>[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(Gamma>[B], FV, Th, J1, SO, LL, P2).

% =========================================================================
% QUANTIFIER  RULES
% =========================================================================
% --- Rule 13: Rforall -----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(Gamma > [A1 | D1], FV, Th, J1, SO, LL, P).

% --- Rule 14: Lexists ----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves([A1 | G1] > Delta, FV, Th, J1, SO, LL, P).

% --- Rule 15: Lforall (universal instantiation, Otten's limitation) -----------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    length(FV, Len), Len =< Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves([A1 | Gamma] > Delta, [Y | FV], Th, SI, SO, LL, P), !.

% --- Rule 16: Rexists ----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FV, Len), Len < Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves(Gamma > [A1 | D1], [Y | FV], Th, SI, SO, LL, P), !.

% =========================================================================
% QUANTIFIER CONVERSION RULES
% =========================================================================

% --- Rule 17: CQ_c (classical quantifier shift) ---------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    ( member((?[ZT-YT]:AT) => B, G1),
      \+ \+ ((A => B) = AT) ->
        g4mic_proves([?[ZT-YT]:AT | G1]>Delta, FV, Th, SI, SO, classical, P)
    ;
        g4mic_proves([?[Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, classical, P)
    ).

% --- Rule 18: CQ_m (quantifier conversion, all logics) -------------------
% (?[X]:A => B) -> ![X]:(A => B)
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, cq_m(Gamma>Delta, P)) :-
    select((?[Z-X]:A) => B, Gamma, G1),
    g4mic_proves([![Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, LL, P).

% =========================================================================
% HELPER PREDICATES
% =========================================================================

% is_nested_negation(Formula, Target, Depth)
% Checks if Formula = not^Depth(Target)
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

% =========================================================================
% END of Prover
% =========================================================================
