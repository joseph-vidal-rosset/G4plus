% =========================================================================
% G4+ FOL Prover — Core Engine
% =========================================================================
%
% Sequent calculus theorem prover for first-order logic based on
% Roy Dyckhoff's G4 calculus with extensions for classical logic.
%
% Key features:
% - Contraction-free G4 rules (efficient proof search)
% - Progressive logic detection: minimal → intuitionistic → classical
% - Eigenvariable management for quantifier rules
% - Optimized rule ordering for performance
%
% Rule ordering strategy:
%   0.  Axiom, L-bot           (immediate closure)
%   1-5. Deterministic prop.   (no branching, single recursive call)
%   6.   L->->                 (2 branches, but with cut)
%   7.   IP                    (classical only, must precede R->)
%   8.   R->                   (deterministic, right implication)
%   9.   Lv                    (2 branches, delayed after L->->)
%   10-11. Rv, R&              (right rules, branching)
%   12-15. Quantifier rules    (L-exists before L-forall for Skolem guidance)
%   16-17. CQ rules            (quantifier conversions, last resort)
%
% =========================================================================

% =========================================================================
% EIGENVARIABLE REGISTRY (backtrackable global state)
% =========================================================================

init_eigenvars :- b_setval(g4_eigenvars, []).

member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem, !.

% =========================================================================
% RULE 0: AXIOM (separate predicate, not tabled)
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

% --- Rule 0: Axiom (tested first) ----------------------------------------
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% --- Rule 0.1: L-bot -----------------------------------------------------
g4mic_proves(Gamma>Delta, _, _, SI, SI, LL, lbot(Gamma>Delta, #)) :-
    member(LL, [intuitionistic, classical]),
    member(#, Gamma), !.

% =========================================================================
% PROPOSITIONAL RULES (deterministic, no branching)
% =========================================================================

% --- Rule 1: L& -----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, land(Gamma>Delta, P)) :-
    select((A & B), Gamma, G1), !,
    g4mic_proves([A, B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 2: L0-> (modus ponens on context) -------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, l0cond(Gamma>Delta, P)) :-
    select((A => B), Gamma, G1),
    member(A, G1), !,
    g4mic_proves([B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 3: TNE (triple negation elimination) ----------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],
    member(LongNeg, Gamma),
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2, !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).

% --- Rule 4: L&-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, landto(Gamma>Delta, P)) :-
    select(((A & B) => C), Gamma, G1), !,
    g4mic_proves([(A => (B => C)) | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 5: Lv-> (optimized) --------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lorto(Gamma>Delta, P)) :-
    select(((A | B) => C), Gamma, G1), !,
    ( member(A, G1), member(B, G1) ->
        g4mic_proves([A=>C, B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(A, G1) ->
        g4mic_proves([A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(B, G1) ->
        g4mic_proves([B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ;
        g4mic_proves([A=>C, B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ).

% =========================================================================
% IMPLICATION RULES (with branching)
% =========================================================================

% --- Rule 6: L->-> --------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A => B) => C), Gamma, G1), !,
    g4mic_proves([A, (B => C) | G1]>[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves([C | G1]>Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 7: IP (indirect proof — classical only) -------------------------
% Must precede R-> : IP needs the goal intact before decomposition
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Th > 0,
    g4mic_proves([(A => #) | Gamma]>[#], FV, Th, SI, SO, classical, P).

% --- Rule 8: R-> -----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rcond(Gamma>Delta, P)) :-
    Delta = [A => B], !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).

% --- Rule 9: Lv (left disjunction — delayed after L->->) ------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lor(Gamma>Delta, P1, P2)) :-
    select((A | B), Gamma, G1), !,
    g4mic_proves([A | G1]>Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves([B | G1]>Delta, FV, Th, J1, SO, LL, P2).

% =========================================================================
% RIGHT RULES
% =========================================================================

% --- Rule 10: Rv (right disjunction) --------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ror(Gamma>Delta, P)) :-
    Delta = [(A | B)], !,
    (   g4mic_proves(Gamma>[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(Gamma>[B], FV, Th, SI, SO, LL, P)
    ).

% --- Rule 11: R& (right conjunction) --------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(Gamma>[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(Gamma>[B], FV, Th, J1, SO, LL, P2).

% =========================================================================
% QUANTIFIER RULES
% L-exists before L-forall: Skolem terms guide universal instantiation
% =========================================================================

% --- Rule 12: L-exists (eigenvariable introduction) -----------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves([A1 | G1] > Delta, FV, Th, J1, SO, LL, P).

% --- Rule 13: R-forall (eigenvariable introduction) -----------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(Gamma > [A1 | D1], FV, Th, J1, SO, LL, P).

% --- Rule 14: L-forall (universal instantiation, Otten's limitation) ------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    length(FV, Len), Len =< Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves([A1 | Gamma] > Delta, [Y | FV], Th, SI, SO, LL, P), !.

% --- Rule 15: R-exists (existential instantiation) ------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FV, Len), Len < Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves(Gamma > [A1 | D1], [Y | FV], Th, SI, SO, LL, P), !.

% =========================================================================
% QUANTIFIER CONVERSION RULES
% =========================================================================

% --- Rule 16: CQ_c (classical quantifier shift) ---------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    ( member((?[ZT-YT]:AT) => B, G1),
      \+ \+ ((A => B) = AT) ->
        g4mic_proves([?[ZT-YT]:AT | G1]>Delta, FV, Th, SI, SO, classical, P)
    ;
        g4mic_proves([?[Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, classical, P)
    ).

% --- Rule 17: CQ_m (quantifier conversion, all logics) -------------------
% (?[X]:A => B) → ![X]:(A => B)
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
