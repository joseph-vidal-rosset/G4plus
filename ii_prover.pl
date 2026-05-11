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
% - Deterministic rules before any branching (weakest logic first):
%     Axiom, L-bot, R->, L&, R&, Rforall, Lexists, L0->, L&->, L\/->
% - Branching rules after all deterministic reductions:
%     L\/, R\/, IP (classical only), L->->
% - Threshold-based quantifier rules last:
%     CQ_m (before Lforall: builds the universal form that Lforall instantiates),
%     Lforall, Rexists, CQ_c (classical only)
% - TNE removed: dead code (R-> fires first on Delta=[A=>B] with cut)
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
%
% Rule ordering rationale:
% -------------------------
% Invertible deterministic rules first (no branching, no loss of information):
%   1. Axiom, L-bot                     -- base cases
%   2. Lexists, Rforall                 -- eigenvariable introduction (enriches context)
%   3. R->, L&                          -- structural decomposition
%   4. L0->, L&->                       -- conditional decomposition (benefit from eigenvars)
%   5. R&, L\/->                        -- deterministic with cut
% Then branching rules (non-deterministic, expensive):
%   6. L\/, R\/                         -- disjunction (two branches / choice)
%   7. IP                               -- classical indirect proof
%   8. L->->                            -- implication-to-implication (two branches)
% Then threshold-based quantifier rules (non-deterministic, instantiation):
%   9. CQ_m, Lforall, Rexists, CQ_c
% =========================================================================

% --- Rule 0: Axiom  ----------------------------
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% --- Rule 1: L-bot -----------------------------------------------------
g4mic_proves(Gamma>Delta, _, _, SI, SI, LL, lbot(Gamma>Delta, #)) :-
    member(LL, [intuitionistic, classical]),
    member(#, Gamma), !.

% --- Rule 4: R-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rcond(Gamma>Delta, P)) :-
    Delta = [A => B], !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).

% --- Rule 5: L& -----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, land(Gamma>Delta, P)) :-
    select((A & B), Gamma, G1), !,
    g4mic_proves([A, B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 6: L0-> (modus ponens on context) -------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, l0cond(Gamma>Delta, P)) :-
    select((A => B), Gamma, G1),
    member(A, G1),
    !,
    g4mic_proves([B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 7: L&-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, landto(Gamma>Delta, P)) :-
    select(((A & B) => C), Gamma, G1), !,
    g4mic_proves([(A => (B => C)) | G1]>Delta, FV, Th, SI, SO, LL, P).


% --- Rule 2: Lexists (deterministic: existential in antecedent -> introduce eigenvar) --
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves([A1 | G1] > Delta, FV, Th, J1, SO, LL, P).


% --- Rule 8: R& (deterministic: Delta is a conjunction -> decompose immediately) --
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(Gamma>[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(Gamma>[B], FV, Th, J1, SO, LL, P2).

% --- Rule 10: L\/ (left disjunction) --------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lor(Gamma>Delta, P1, P2)) :-
    select((A | B), Gamma, G1), !,
    g4mic_proves([A | G1]>Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves([B | G1]>Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 11: R\/ ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ror(Gamma>Delta, P)) :-
    Delta = [(A | B)],
    (   g4mic_proves(Gamma>[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(Gamma>[B], FV, Th, SI, SO, LL, P)
    ).


% --- Rule 9: L\/-> (optimized) --------------------------------------------
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

% --- Rule 12: IP (indirect proof -- classical only, must be before L->->)  --
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Th > 0,
    g4mic_proves([(A => #) | Gamma]>[#], FV, Th, SI, SO, classical, P).

% --- Rule 13: L->-> --------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A => B) => C), Gamma, G1),
    \+ (B = #, member(A, G1)),
    !,
    g4mic_proves([A, (B => C) | G1]>[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves([C | G1]>Delta, FV, Th, J1, SO, LL, P2).


% --- Rule 3: Rforall (deterministic: universal in succedent -> introduce eigenvar) --
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(Gamma > [A1 | D1], FV, Th, J1, SO, LL, P).

% =========================================================================
% THRESHOLD-BASED QUANTIFIER RULES
% =========================================================================

% --- Rule 14: CQ_m (quantifier conversion, all logics -- must precede Lforall) --
% (?[X]:A => B)  ->  ![X]:(A => B)
% Placed before Lforall so that the universal form is available for instantiation.
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, cq_m(Gamma>Delta, P)) :-
    select((?[Z-X]:A) => B, Gamma, G1),
    g4mic_proves([![Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, LL, P).

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
% CLASSICAL QUANTIFIER CONVERSION RULE (classical)
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

% =========================================================================
% HELPER PREDICATES
% =========================================================================

% =========================================================================
% END of Prover
% =========================================================================
