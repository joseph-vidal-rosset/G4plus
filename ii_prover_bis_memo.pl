% =========================================================================
% G4 FOL Prover with equality
% TPTP-version
% =========================================================================
% This is the core G4 sequent calculus theorem prover for first-order logic.
%
% Key features:
% - Implements Roy Dyckhoff's G4 sequent calculus rules
% - Handles propositional and first-order logic
% - Supports equality reasoning (reflexivity, symmetry, transitivity)
% - Progressive logic level detection (minimal → intuitionistic → classical)
% - Eigenvariable management for quantifier rules
% - FAILURE MEMOIZATION for lall/rex to avoid redundant exploration
%
% The G4 calculus is a refinement of Gentzen's LJ/LK systems optimized for
% automated theorem proving. It features:
% - Contraction-free rules (more efficient search)
% - Optimized left-implication rule (reduces backtracking)
% - Natural correspondence with natural deduction
%
% Proof strategy:
% 1. Start with minimal logic (constructive, no excluded middle)
% 2. Escalate to intuitionistic if minimal fails
% 3. Fall back to classical logic if needed
%
% This progressive approach maximizes constructive content while ensuring
% completeness for classical logic.
% =========================================================================

% =========================================================================
% FAILURE MEMOIZATION CACHE
% =========================================================================
% We cache sequents that have FAILED, so we don't retry them.
% The cache key is a normalized form: sequent + threshold + logic level.
% We only cache failures for sequents produced by lall and rex,
% which are the main sources of combinatorial explosion.
%
% IMPORTANT: The cache must be cleared before each new proof attempt
% (each new threshold iteration), since a sequent that fails at
% threshold N might succeed at threshold N+1.
% =========================================================================

:- dynamic g4_fail_cache/1.

% Initialize/clear the failure cache
init_fail_cache :- retractall(g4_fail_cache(_)).

% Check if a sequent has already failed
% We normalize by sorting Gamma to make cache hits order-independent
check_fail_cache(Gamma > Delta, Threshold, LogicLevel) :-
    msort(Gamma, SortedGamma),
    g4_fail_cache(memo(SortedGamma, Delta, Threshold, LogicLevel)).

% Record a failed sequent
record_failure(Gamma > Delta, Threshold, LogicLevel) :-
    msort(Gamma, SortedGamma),
    \+ g4_fail_cache(memo(SortedGamma, Delta, Threshold, LogicLevel)),
    assertz(g4_fail_cache(memo(SortedGamma, Delta, Threshold, LogicLevel))).

% =========================================================================
% EIGENVARIABLE REGISTRY (using b_setval for BACKTRACKABLE global state)
% =========================================================================
% Initialize eigenvariable registry (call before each proof attempt)
% Using b_setval for BACKTRACKABLE global variable
init_eigenvars :- b_setval(g4_eigenvars, []).

% member_check(Term, List): check if Term is structurally equivalent (=@=) to any member
member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem,
    !.

%==========================================================================
% AXIOM - SEPARATE PREDICATE (NOT TABLED)
%==========================================================================
% Must be tested BEFORE any tabled rules to avoid caching non-axiomatic proofs
g4mic_ax(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    Delta = [B],
    unify_with_occurs_check(A, B).

% TABLING: Memoization to avoid redundant computations
% :- table g4mic_proves/7.

% g4mic_proves/7 -
% g4mic_proves(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
% LogicLevel: minimal | intuitionistic | classical
%==========================================================================
% Entry point: test axiom FIRST (non-tabled), then other rules (tabled)
%==========================================================================
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% 0.1 L-bot
g4mic_proves(Gamma>Delta, _, _, SkolemIn, SkolemIn, LogicLevel, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, land(Gamma>Delta,P)) :-
    select((A&B),Gamma,G1), !,
    g4mic_proves([A,B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L0->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, l0cond(Gamma>Delta,P)) :-
    select((A=>B),Gamma,G1),
    member(A,G1), !,
    g4mic_proves([B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L&->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, landto(Gamma>Delta,P)) :-
    select(((A&B)=>C),Gamma,G1), !,
    g4mic_proves([(A=>(B => C))|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],  % Goal: not-A
    % Search in Gamma for a formula with more negations
    member(LongNeg, Gamma),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    g4mic_proves([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law).
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), Gamma),  % not-A not already in context
    Threshold > 0,
    g4mic_proves([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, P).
% 4. Lv-> (OPTIMIZED)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lorto(Gamma>Delta,P)) :-
    select(((A|B)=>C),Gamma,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        g4mic_proves([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        g4mic_proves([A=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        g4mic_proves([B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        g4mic_proves([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 8. R->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rcond(Gamma>Delta,P)) :-
    Delta = [A=>B], !,
    g4mic_proves([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 6. L->->b
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ltoto(Gamma>Delta,P1,P2)) :-
    select(((A=>B)=>C),Gamma,G1), !,
    g4mic_proves([A,(B=>C)|G1]>[B], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves([C|G1]> Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
% 5. Lv (MOVED AFTER L->->b as per optimization)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lor(Gamma>Delta, P1,P2)) :-
    select((A|B),Gamma,G1), !,
    g4mic_proves([A|G1]>Delta, FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves([B|G1]>Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).

% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    copy_term((X:(A|B),FreeVars), (f_sk(SkolemIn,FreeVars):(A1|B1),FreeVars)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable (backtrackable)
    b_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    g4mic_proves([A1|G1]>Delta, FreeVars, Threshold, J1, J2, LogicLevel, P1),
    g4mic_proves([B1|G1]>Delta, FreeVars, Threshold, J2, SkolemOut, LogicLevel, P2).
% 10. R?
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   g4mic_proves(Gamma>[A], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;   g4mic_proves(Gamma>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rand(Gamma>Delta,P1,P2)) :-
    Delta = [(A&B)], !,
    g4mic_proves(Gamma>[A], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves(Gamma>[B], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
% 13. R-forall - with BACKTRACKABLE global eigenvariable registry
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    % Using b_getval for backtrackable global variable
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable (backtrackable)
    b_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    g4mic_proves(Gamma > [A1|D1], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% =========================================================================
% 14. L-forall - WITH OTTEN's LIMITATION + FAILURE MEMOIZATION
% =========================================================================
% This is the main source of combinatorial explosion (e.g., Pelletier 27).
% We check the failure cache BEFORE attempting the proof, and record
% failures AFTER they occur.
% =========================================================================
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    % OTTEN's CHECK: prevent infinite instantiation when threshold is reached
    length(FreeVars, Len), Len =< Threshold,
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    NewGamma = [A1|Gamma],
    NewFreeVars = [Y|FreeVars],
    % CHECK FAILURE CACHE: skip if this sequent already failed at this threshold
    \+ check_fail_cache(NewGamma > Delta, Threshold, LogicLevel),
    % Attempt proof with failure recording
    (   g4mic_proves(NewGamma > Delta, NewFreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ->  true   % Success: done
    ;   % Failure: record in cache and fail
        record_failure(NewGamma > Delta, Threshold, LogicLevel),
        fail
    ), !.

 % 12. L-exists - with BACKTRACKABLE global eigenvariable registry
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    % Using b_getval for backtrackable global variable - NO ?
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable (backtrackable)
    b_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    g4mic_proves([A1|G1] > Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% =========================================================================
% 15. R-exists - WITH FAILURE MEMOIZATION
% =========================================================================
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FreeVars, Len), Len < Threshold,
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    NewDelta = [A1|D1],
    NewFreeVars = [Y|FreeVars],
    % CHECK FAILURE CACHE
    \+ check_fail_cache(Gamma > NewDelta, Threshold, LogicLevel),
    (   g4mic_proves(Gamma > NewDelta, NewFreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ->  true
    ;   record_failure(Gamma > NewDelta, Threshold, LogicLevel),
        fail
    ), !.
% 16. CQ_c - Classical rule
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, cq_c(Gamma>Delta,P)) :-
    select((![Z-X]:A) => B, Gamma, G1),

    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATargbet
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        g4mic_proves([?[ZTarget-YTarget]:ATarget|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ;
        % Otherwise: normal case with X
        g4mic_proves([?[Z-X]:(A => B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ).
% 17. CQ_m - Quantifier conversion (VALID IN ALL LOGICS)
% Critical rule: (?[X]:A => B) → ![X]:(A => B)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, cq_m(Gamma>Delta,P)) :-
    select((?[Z-X]:A)=>B, Gamma, G1),
    g4mic_proves([![Z-X]:(A=>B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% =========================================================================
% =========================================================================
% NOTE: Equality is handled exclusively by nanoCoP
% =========================================================================
% Helper: verify if Formula = not^n(Target) and return n
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

% =========================================================================
% END of Prover
% =========================================================================
