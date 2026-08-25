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
% This file is the modular packaging of the engine that also lives in
% g4mic_nanocop.pl. The two are kept byte-identical from the
% EIGENVARIABLE REGISTRY banner to the END of Prover banner: any change
% to a rule, to the Gamma compartments, or to the flat-Gamma invariant
% must be applied to both. See CLAUDE.md, "Architecture of proof search
% -- the flat-Gamma invariant", for why Fl is threaded alongside the
% eight buckets and what breaks if it is dropped.
%
% TNE removed: dead code (R-> fires first on Delta=[A=>B] with cut).
% =========================================================================

% =========================================================================
% EIGENVARIABLE REGISTRY (backtrackable global state)
% =========================================================================

init_eigenvars :- b_setval(g4_eigenvars, []).

member_check(Term, [Elem|Rest]) :-
    (   Term =@= Elem
    ->  true
    ;   member_check(Term, Rest)
    ).

% =========================================================================
% RULE 0: AXIOM
% =========================================================================

g4mic_ax(At,_Cj,_Dj,_I0,_IA,_IO,_IT,_Qt,Fl,Delta, _, _, SkolemIn, SkolemIn, _,
         ax(Fl>Delta, ax)) :-
    Delta = [B],
    (   nonvar(B)
    ->  atomic_formula(B),
        member(A, At),
        unify_with_occurs_check(A, B)
    ;   member(A, At),
        atomic_formula(A),
        unify_with_occurs_check(A, B)
    ).

% atomic_formula(+F): F has no logical connective as principal symbol.
% The five shapes are listed as clause heads of connective_shape/1 rather
% than as name/arity pairs looked up by functor/3: SWI indexes a
% single-argument predicate on the principal functor of its argument, so
% \+ connective_shape(F) is one jump-table lookup where functor/3 plus a
% two-argument table lookup was a functor decomposition, an atom index
% and an arity test. Measured -14.5% on the test alone.
% The compound/1 guard is what makes an unbound F atomic, as before:
% without it, connective_shape(F) would unify F with _ & _ and succeed.
atomic_formula(F) :-
    (   compound(F)
    ->  \+ connective_shape(F)
    ;   true
    ).

connective_shape(_ & _).
connective_shape(_ | _).
connective_shape(_ => _).
connective_shape(!_).
connective_shape(?_).

% =========================================================================
% GAMMA COMPARTMENTS
% =========================================================================
% Gamma is held in two forms at once, both threaded through
% g4mic_proves/16 and g4mic_ax/16:
%
%   - eight separate arguments -- Atoms,Conj,Disj,ImplAtom,LandTo,LorTo,
%     LtoTo,Quant -- one list per principal-connective bucket. Each
%     propositional left rule consults only its own bucket instead of
%     scanning all of Gamma;
%   - Fl, the same members as one flat list in INSERTION ORDER (most
%     recent first), which every proof node records as its Gamma>Delta
%     sequent.
%
% Fl is not redundant, and it is not a convenience: everything
% downstream of search -- the bussproofs renderer, the ND-tree
% translator, fitch_g4_proof/8 -- re-derives which formula each rule
% acted on by searching Gamma, and that re-derivation depends on Gamma's
% order. Bucket order is not insertion order and cannot be made to
% reproduce it. Flattening the buckets instead of threading Fl silently
% loses 19 natural-deduction trees across 8 tests; no static bucket
% order fixes it. Every rule must keep Fl in step with the buckets: a
% rule that removes from a bucket removes from Fl (selectchk/3), and a
% rule that inserts conses onto Fl in the same order the original
% flat-list code used. See CLAUDE.md, "Architecture of proof search --
% the flat-Gamma invariant".
%
% The eight buckets are passed as bare list arguments rather than
% wrapped in a single compound term: an earlier version wrapped them in
% a g/8 term, but rebuilding that wrapper on every insert/select cost
% ~2x a plain list cons (measured), which ate the gain from doing fewer,
% smaller scans. With bare arguments, a rule that touches one bucket
% pays only for that bucket's cons cell; the other seven flow through
% as untouched variable references, at no cost.
%
% Bucket membership is exhaustive and mutually exclusive over the six
% shapes a Gamma member can have after negation normalisation (~A is
% rewritten to A => # before the prover runs -- see subst_neg/2):
%   Atoms    -- atomic formulas (no connective_shape/1 match), incl. #
%   Conj     -- A & B
%   Disj     -- A | B
%   ImplAtom -- A => B, A atomic                  (textbook G4 L0-> case)
%   LandTo   -- (A & B) => C
%   LorTo    -- (A | B) => C
%   LtoTo    -- (A => B) => C
%   Quant    -- ![Z-X]:A, ?[Z-X]:A, and the two quantified-antecedent
%               implication forms (![Z-X]:A)=>B, (?[Z-X]:A)=>B
%
% Rules that select from a single bucket (L&, L\/, L\/->, L->->, Lexists,
% Lforall, CQ_m, CQ_c) agree with flat-Gamma order for free: filtering a
% LIFO sequence preserves relative order, so the head of Conj *is* the
% first conjunction of Gamma.
%
% L0-> is the exception, and the reason gamma_remove/17 exists. It fires
% on ANY implication in Gamma whose antecedent is already present
% elsewhere, regardless of the antecedent's shape -- intentional,
% existing behaviour, not the textbook atomic-only case -- so its
% candidates range over five buckets at once, and no concatenation of
% those five reproduces the global order. It therefore enumerates over
% Fl and deletes the chosen implication from the buckets afterwards.
% =========================================================================

% gamma_insert(+F, +At,+Cj,+Dj,+I0,+IA,+IO,+IT,+Qt, -AtO,-CjO,-DjO,-I0O,-IAO,-IOO,-ITO,-QtO):
% the single classification point. Reuses atomic_formula/1 (same
% functor test as the Axiom rule), so "atomic" means the same thing
% everywhere.
%
% Clause order is chosen for first-argument indexing, not for reading:
% the three shapes with a concrete principal functor come first, so SWI
% can jump straight to the matching clause. Putting the atomic clause
% first -- its head argument is a plain variable -- defeats the index
% altogether and makes every insertion run atomic_formula/1 before
% anything else. The five shapes are mutually exclusive, so the order
% carries no meaning beyond that. Measured -21.5% on the predicate.
gamma_insert((A & B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,[(A&B)|Cj],Dj,I0,IA,IO,IT,Qt) :- !.
gamma_insert((A | B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,[(A|B)|Dj],I0,IA,IO,IT,Qt) :- !.
gamma_insert((A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO) :- !,
    gamma_insert_impl(A, (A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO).
gamma_insert(F, At,Cj,Dj,I0,IA,IO,IT,Qt, [F|At],Cj,Dj,I0,IA,IO,IT,Qt) :-
    atomic_formula(F), !.
gamma_insert(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,[F|Qt]).
    % F = ![Z-X]:A or ?[Z-X]:A -- the only shapes left once atomic/&/|/=>
    % have been ruled out (closed six-shape assumption above).

gamma_insert_impl((_ & _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,[F|IA],IO,IT,Qt) :- !.
gamma_insert_impl((_ | _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,[F|IO],IT,Qt) :- !.
gamma_insert_impl((_ => _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,[F|IT],Qt) :- !.
gamma_insert_impl(A, F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,[F|I0],IA,IO,IT,Qt) :-
    atomic_formula(A), !.
gamma_insert_impl(_, F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,[F|Qt]).
    % A = ![Z-X]:_ or ?[Z-X]:_ -- quantified-antecedent implication
    % (CQ_c / CQ_m trigger).

% gamma_insert_list(+Formulas, +At,...,+Qt, -AtO,...,-QtO): fold
% gamma_insert/17 over a list, for the sites that used to do [A, B | G1].
% Inserts RIGHT-TO-LEFT: the tail is inserted first, so the head of
% Formulas ends up at the head of its bucket. This matches the flat-list
% convention [A, B | G1], where A precedes B. Folding left-to-right would
% reverse them inside the bucket, and the rules that select from a bucket
% would then pick a different principal formula than the flat Gamma order
% dictates.
gamma_insert_list([], At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,Qt).
gamma_insert_list([F|Fs], At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO) :-
    gamma_insert_list(Fs, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    gamma_insert(F, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO).

gamma_from_list(List, At,Cj,Dj,I0,IA,IO,IT,Qt) :-
    gamma_insert_list(List, [],[],[],[],[],[],[],[], At,Cj,Dj,I0,IA,IO,IT,Qt).

% gamma_remove(+F, +At..+Qt, -AtO..-QtO): delete one occurrence of F from
% the bucket its principal connective assigns it to -- the mirror of
% gamma_insert/17, and ordered for the same indexing reason. Used by
% L0->, which enumerates candidates over the insertion-ordered flat
% Gamma (see Rule 6) and must then delete the chosen implication from
% the buckets.
gamma_remove((A & B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj1,Dj,I0,IA,IO,IT,Qt) :- !,
    selectchk((A&B), Cj, Cj1).
gamma_remove((A | B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj1,I0,IA,IO,IT,Qt) :- !,
    selectchk((A|B), Dj, Dj1).
gamma_remove((A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I01,IA1,IO1,IT1,Qt1) :- !,
    gamma_remove_impl(A, (A => B), I0,IA,IO,IT,Qt, I01,IA1,IO1,IT1,Qt1).
gamma_remove(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj,Dj,I0,IA,IO,IT,Qt) :-
    atomic_formula(F), !, selectchk(F, At, At1).
gamma_remove(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,Qt1) :-
    selectchk(F, Qt, Qt1).

gamma_remove_impl((_ & _), F, I0,IA,IO,IT,Qt, I0,IA1,IO,IT,Qt) :- !,
    selectchk(F, IA, IA1).
gamma_remove_impl((_ | _), F, I0,IA,IO,IT,Qt, I0,IA,IO1,IT,Qt) :- !,
    selectchk(F, IO, IO1).
gamma_remove_impl((_ => _), F, I0,IA,IO,IT,Qt, I0,IA,IO,IT1,Qt) :- !,
    selectchk(F, IT, IT1).
gamma_remove_impl(A, F, I0,IA,IO,IT,Qt, I01,IA,IO,IT,Qt) :-
    atomic_formula(A), !, selectchk(F, I0, I01).
gamma_remove_impl(_, F, I0,IA,IO,IT,Qt, I0,IA,IO,IT,Qt1) :-
    selectchk(F, Qt, Qt1).

% normalize_proof_gammas(+ProofIn, -ProofOut): proof nodes are built
% directly as the familiar Gamma>Delta sequent term -- each rule
% receives Fl, the flat Gamma in insertion order, and records it -- so
% nothing has to be translated afterwards and this is the identity. It
% is kept because output_proof_results/3 and the biconditional branch of
% g4mic_decides/1 call it, and because it is the hook a future change
% that stops threading Fl would need (see CLAUDE.md, "Open item").
normalize_proof_gammas(Proof, Proof).

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
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL, Proof), !.


% --- Rule 4: R-> ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             rcond(Fl>Delta, P)) :-
    Delta = [A => B], !,
    gamma_insert(A, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[A|Fl],[B], FV, Th, SI, SO, LL, P).


% --- Rule 5: L& -----------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             land(Fl>Delta, P)) :-
    select((A & B), Cj, Cj0), !,
    selectchk((A & B), Fl, Fl0),
    gamma_insert_list([A, B], At,Cj0,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[A,B|Fl0],Delta, FV, Th, SI, SO, LL, P).


% --- Rule 6: L0-> (modus ponens on context) -------------------------------
% Fires on ANY implication in Gamma whose antecedent is already present
% elsewhere, regardless of the antecedent's shape -- see the design note
% above the GAMMA COMPARTMENTS section for why gamma_all_implications_select/11
% must range over every antecedent-shape bucket rather than just ImplAtom.
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             l0cond(Fl>Delta, P)) :-
    select((A => B), Fl, Fl0),
    memberchk(A, Fl0),
    ( LL == minimal, B == # -> true ; ! ),
    gamma_remove((A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, Atg,Cjg,Djg,I0g,IAg,IOg,ITg,Qtg),
    gamma_insert(B, Atg,Cjg,Djg,I0g,IAg,IOg,ITg,Qtg, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[B|Fl0],Delta, FV, Th, SI, SO, LL, P).


% --- Rule 7: L&-> ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             landto(Fl>Delta, P)) :-
    select(((A & B) => C), IA, IA0), !,
    selectchk(((A & B) => C), Fl, Fl0),
    gamma_insert((A => (B => C)), At,Cj,Dj,I0,IA0,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[(A => (B => C))|Fl0],Delta, FV, Th, SI, SO, LL, P).


% --- Rule 2: Lexists (deterministic: existential in antecedent -> introduce eigenvar) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             lex(Fl>Delta, P)) :-
    select((?[_Z-X]:A), Qt, Qt0), !,
    selectchk((?[_Z-X]:A), Fl, Fl0),
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    gamma_insert(A1, At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[A1|Fl0],Delta, FV, Th, J1, SO, LL, P).

% --- Rule 3: Rforall (deterministic: universal in succedent -> introduce eigenvar) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             rall(Fl>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[A1 | D1], FV, Th, J1, SO, LL, P).


% --- Rule 8: R& (deterministic: Delta is a conjunction -> decompose immediately) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             rand(Fl>Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[B], FV, Th, J1, SO, LL, P2).

% --- Rule 10: L\/ (left disjunction) --------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             lor(Fl>Delta, P1, P2)) :-
    select((A | B), Dj, Dj0), !,
    selectchk((A | B), Fl, Fl0),
    gamma_insert(A, At,Cj,Dj0,I0,IA,IO,IT,Qt, AtA,CjA,DjA,I0A,IAA,IOA,ITA,QtA),
    gamma_insert(B, At,Cj,Dj0,I0,IA,IO,IT,Qt, AtB,CjB,DjB,I0B,IAB,IOB,ITB,QtB),
    g4mic_proves(AtA,CjA,DjA,I0A,IAA,IOA,ITA,QtA,[A|Fl0],Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves(AtB,CjB,DjB,I0B,IAB,IOB,ITB,QtB,[B|Fl0],Delta, FV, Th, J1, SO, LL, P2).


% --- Rule 9: L\/-> (optimized) --------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             lorto(Fl>Delta, P)) :-
    select(((A | B) => C), IO, IO0), !,
    selectchk(((A | B) => C), Fl, Fl0),
    ( memberchk(A, Fl0), memberchk(B, Fl0) ->
      gamma_insert_list([(B=>C), (A=>C)], At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
      Fl1 = [(B=>C), (A=>C)|Fl0]
    ; memberchk(A, Fl0) ->
      gamma_insert((A=>C), At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
      Fl1 = [(A=>C)|Fl0]
    ; memberchk(B, Fl0) ->
      gamma_insert((B=>C), At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
      Fl1 = [(B=>C)|Fl0]
    ;
      gamma_insert_list([(A=>C), (B=>C)], At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
      Fl1 = [(A=>C), (B=>C)|Fl0]
    ),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Fl1,Delta, FV, Th, SI, SO, LL, P).

% --- Rule 11: R\/ ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             ror(Fl>Delta, P)) :-
    Delta = [(A | B)],
    (   g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[B], FV, Th, SI, SO, LL, P)
    ).
% --- Rule 1: L-bot -----------------------------------------------------
g4mic_proves(_At,_Cj,_Dj,_I0,_IA,_IO,_IT,_Qt,Fl,Delta, _, _, SI, SI, LL,
             lbot(Fl>Delta, #)) :-
    memberchk(LL, [intuitionistic, classical]),
    memberchk(#, Fl), !.

% --- Rule 12: IP (indirect proof -- classical only, must be before L->->)  --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, classical,
             ip(Fl>Delta, P)) :-
    Delta = [A],
    A \= #,
    Th > 0,
    \+ memberchk((A => #), Fl),
    gamma_insert((A => #), At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[(A => #)|Fl],[#], FV, Th, SI, SO, classical, P).

% --- Rule 13: L->-> --------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             ltoto(Fl>Delta, P1, P2)) :-
    select(((A => B) => C), IT, IT0),
    selectchk(((A => B) => C), Fl, Fl0),
    \+ (B = #, memberchk(A, Fl0)),
    !,
    gamma_insert_list([A, (B => C)], At,Cj,Dj,I0,IA,IO,IT0,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    gamma_insert(C, At,Cj,Dj,I0,IA,IO,IT0,Qt, At2,Cj2,Dj2,I02,IA2,IO2,IT2,Qt2),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[A,(B => C)|Fl0],[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves(At2,Cj2,Dj2,I02,IA2,IO2,IT2,Qt2,[C|Fl0],Delta, FV, Th, J1, SO, LL, P2).
% =========================================================================
% THRESHOLD-BASED QUANTIFIER RULES
% =========================================================================

% --- Rule 14: CQ_m (quantifier conversion, all logics -- must precede Lforall) --
% (?[X]:A => B)  ->  ![X]:(A => B)
% Placed before Lforall so that the universal form is available for instantiation.
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             cq_m(Fl>Delta, P)) :-
    select((?[Z-X]:A) => B, Qt, Qt0),
    selectchk((?[Z-X]:A) => B, Fl, Fl0),
    gamma_insert(![Z-X]:(A => B), At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[![Z-X]:(A => B)|Fl0],Delta, FV, Th, SI, SO, LL, P).

% --- Rule 15: Lforall (universal instantiation, Otten's limitation) -----------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             lall(Fl>Delta, P)) :-
    length(FV, Len), Len =< Th,
    member((![_Z-X]:A), Qt),
    copy_term((X:A, FV), (Y:A1, FV)),
    gamma_insert(A1, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[A1|Fl],Delta, [Y | FV], Th, SI, SO, LL, P), !.

% --- Rule 16: Rexists ----------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, LL,
             rex(Fl>Delta, P)) :-
    length(FV, Len), Len < Th,
    select((?[_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,[A1 | D1], [Y | FV], Th, SI, SO, LL, P), !.

% =========================================================================
% CLASSICAL QUANTIFIER CONVERSION RULE (classical)
% =========================================================================

% --- Rule 17: CQ_c (classical quantifier shift) ---------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Fl,Delta, FV, Th, SI, SO, classical,
             cq_c(Fl>Delta, P)) :-
    select((![Z-X]:A) => B, Qt, Qt0),
    selectchk((![Z-X]:A) => B, Fl, Fl0),
    ( member((?[ZT-YT]:AT) => B, Qt0),
      \+ \+ ((A => B) = AT) ->
        gamma_insert(?[ZT-YT]:AT, At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
        Fl1 = [?[ZT-YT]:AT|Fl0]
    ;
        gamma_insert(?[Z-X]:(A => B), At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
        Fl1 = [?[Z-X]:(A => B)|Fl0]
    ),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Fl1,Delta, FV, Th, SI, SO, classical, P).

% =========================================================================
% HELPER PREDICATES
% =========================================================================
%
% =========================================================================
% END of Prover
% =========================================================================
