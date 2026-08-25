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
% Single indexed lookup on the principal functor instead of five \=/2 tests.
atomic_formula(F) :-
    (   compound(F)
    ->  functor(F, Name, Arity),
        \+ connective(Name, Arity)
    ;   true
    ).

connective(&,   2).
connective('|', 2).
connective(=>,  2).
connective(!,   1).
connective(?,   1).

% =========================================================================
% GAMMA COMPARTMENTS
% =========================================================================
% Gamma is held as eight separate arguments -- Atoms,Conj,Disj,ImplAtom,
% LandTo,LorTo,LtoTo,Quant -- threaded directly through g4mic_proves/g4mic_ax,
% one list per principal-connective bucket, instead of a flat list. Each
% propositional left rule consults only its own bucket instead of
% scanning all of Gamma. See CLAUDE.md, "Current work: compartmentalising
% Gamma".
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
%   Atoms    -- atomic formulas (functor not in connective/2), incl. #
%   Conj     -- A & B
%   Disj     -- A | B
%   ImplAtom -- A => B, A atomic                  (textbook G4 L0-> case)
%   LandTo   -- (A & B) => C
%   LorTo    -- (A | B) => C
%   LtoTo    -- (A => B) => C
%   Quant    -- ![Z-X]:A, ?[Z-X]:A, and the two quantified-antecedent
%               implication forms (![Z-X]:A)=>B, (?[Z-X]:A)=>B
%
% L0-> (see g4mic_proves/7 below) fires on ANY implication in Gamma
% whose antecedent is already present elsewhere, regardless of the
% antecedent's shape -- this is intentional, existing behaviour, not the
% textbook atomic-only case, and compartmentalisation preserves it:
% gamma_all_implications_select/11 scans ImplAtom, LandTo, LorTo, LtoTo
% and the implication-shaped members of Quant, in that fixed order,
% before L&->/L\/->/L->-> fall back to their own bucket. That fixed
% order does not reproduce the original flat-list select/3 enumeration
% order -- an accepted, documented divergence (CLAUDE.md's "known
% pitfall"): it can change which valid proof is found first (and hence
% premise order in rendered output), never provability or logic-level
% classification.
%
% Proof-tree nodes carry the same eight buckets plus Delta as their
% first nine arguments (e.g. ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, ax)),
% rather than the original single Gamma>Delta sequent term.
% normalize_proof_gammas/2 is the one place that translates this wide,
% search-internal shape back into the familiar Gamma>Delta flat-list
% sequent that the raw-term dump, bussproofs/ND-tree/Fitch renderers
% and fitch_g4_proof/8 already expect -- so none of that rendering code
% needs to change. It runs once per completed proof (proportional to
% proof size, not search-tree size); see output_proof_results/3 and the
% biconditional branch of g4mic_decides/1, the only two call sites that
% actually render a proof.
% =========================================================================

% gamma_insert(+F, +At,+Cj,+Dj,+I0,+IA,+IO,+IT,+Qt, -AtO,-CjO,-DjO,-I0O,-IAO,-IOO,-ITO,-QtO):
% the single classification point. Reuses atomic_formula/1 (same
% functor/connective test as the Axiom rule), so "atomic" means the
% same thing everywhere.
gamma_insert(F, At,Cj,Dj,I0,IA,IO,IT,Qt, [F|At],Cj,Dj,I0,IA,IO,IT,Qt) :-
    atomic_formula(F), !.
gamma_insert((A & B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,[(A&B)|Cj],Dj,I0,IA,IO,IT,Qt) :- !.
gamma_insert((A | B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,[(A|B)|Dj],I0,IA,IO,IT,Qt) :- !.
gamma_insert((A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO) :- !,
    gamma_insert_impl(A, (A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO).
gamma_insert(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,[F|Qt]).
    % F = ![Z-X]:A or ?[Z-X]:A -- the only shapes left once atomic/&/|/=>
    % have been ruled out (closed six-shape assumption above).

gamma_insert_impl(A, F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,[F|I0],IA,IO,IT,Qt) :-
    atomic_formula(A), !.
gamma_insert_impl((_ & _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,[F|IA],IO,IT,Qt) :- !.
gamma_insert_impl((_ | _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,[F|IO],IT,Qt) :- !.
gamma_insert_impl((_ => _), F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,[F|IT],Qt) :- !.
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

% gamma_to_list(+At,...,+Qt, -FlatList): flatten all eight buckets into
% one list, in a fixed canonical order. Used only where a genuine flat
% list is required (proof rendering) -- never on the search path. Does
% not reproduce the original insertion order; see the design note above.
% gamma_remove(+F, +At..+Qt, -AtO..-QtO): delete one occurrence of F from
% the bucket its principal connective assigns it to. Dispatches exactly
% like gamma_shape_member/9, so a formula is always removed from the
% bucket gamma_insert/17 put it in. Used by L0->, which enumerates
% candidates over the insertion-ordered flat Gamma (see Rule 6) and must
% then delete the chosen implication from the buckets.
gamma_remove(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj,Dj,I0,IA,IO,IT,Qt) :-
    atomic_formula(F), !, selectchk(F, At, At1).
gamma_remove((A & B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj1,Dj,I0,IA,IO,IT,Qt) :- !,
    selectchk((A&B), Cj, Cj1).
gamma_remove((A | B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj1,I0,IA,IO,IT,Qt) :- !,
    selectchk((A|B), Dj, Dj1).
gamma_remove((A => B), At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I01,IA1,IO1,IT1,Qt1) :- !,
    gamma_remove_impl(A, (A => B), I0,IA,IO,IT,Qt, I01,IA1,IO1,IT1,Qt1).
gamma_remove(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,Qt1) :-
    selectchk(F, Qt, Qt1).

gamma_remove_impl(A, F, I0,IA,IO,IT,Qt, I01,IA,IO,IT,Qt) :-
    atomic_formula(A), !, selectchk(F, I0, I01).
gamma_remove_impl((_ & _), F, I0,IA,IO,IT,Qt, I0,IA1,IO,IT,Qt) :- !,
    selectchk(F, IA, IA1).
gamma_remove_impl((_ | _), F, I0,IA,IO,IT,Qt, I0,IA,IO1,IT,Qt) :- !,
    selectchk(F, IO, IO1).
gamma_remove_impl((_ => _), F, I0,IA,IO,IT,Qt, I0,IA,IO,IT1,Qt) :- !,
    selectchk(F, IT, IT1).
gamma_remove_impl(_, F, I0,IA,IO,IT,Qt, I0,IA,IO,IT,Qt1) :-
    selectchk(F, Qt, Qt1).

% gamma_all_implications_select(-A, -B, +I0,+IA,+IO,+IT,+Qt, -I0O,-IAO,-IOO,-ITO,-QtO):
% the candidate generator for L0->. See the design note above for why
% this must range over every antecedent shape. Plain disjunction (not
% if-then-else) so backtracking into a later candidate of an earlier
% bucket -- or into a later bucket entirely -- both work, exactly as
% select/3 backtracking did on the flat list.
gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0o,IA,IO,IT,Qt) :-
    select((A=>B), I0, I0o).
gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0,IAo,IO,IT,Qt) :-
    select((A=>B), IA, IAo).
gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0,IA,IOo,IT,Qt) :-
    select((A=>B), IO, IOo).
gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0,IA,IO,ITo,Qt) :-
    select((A=>B), IT, ITo).
gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0,IA,IO,IT,Qto) :-
    select((A=>B), Qt, Qto).

% gamma_shape_member(+F, +At,+Cj,+Dj,+I0,+IA,+IO,+IT,+Qt): is F present
% in Gamma, without removing it? Dispatches on F's own principal
% connective to the matching bucket -- this is the L0-> "is A already
% present" presence test.
gamma_shape_member(F, At,_,_,_,_,_,_,_) :-
    atomic_formula(F), !, member(F, At).
gamma_shape_member((A & B), _,Cj,_,_,_,_,_,_) :- !, member((A&B), Cj).
gamma_shape_member((A | B), _,_,Dj,_,_,_,_,_) :- !, member((A|B), Dj).
gamma_shape_member((A => B), _,_,_,I0,IA,IO,IT,Qt) :- !,
    gamma_shape_member_impl(A, (A => B), I0,IA,IO,IT,Qt).
gamma_shape_member(F, _,_,_,_,_,_,_,Qt) :-
    member(F, Qt).

gamma_shape_member_impl(A, F, I0,_,_,_,_) :-
    atomic_formula(A), !, member(F, I0).
gamma_shape_member_impl((_ & _), F, _,IA,_,_,_) :- !, member(F, IA).
gamma_shape_member_impl((_ | _), F, _,_,IO,_,_) :- !, member(F, IO).
gamma_shape_member_impl((_ => _), F, _,_,_,IT,_) :- !, member(F, IT).
gamma_shape_member_impl(_, F, _,_,_,_,Qt) :-
    member(F, Qt).
    % A = ![Z-X]:_ or ?[Z-X]:_ -- look up in Quant, same bucket it was
    % inserted into.

% normalize_proof_gammas(+ProofIn, -ProofOut): every proof-tree node
% embeds the nine search-internal arguments (the eight buckets plus
% Delta) that were active when its rule fired -- e.g.
% ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, ax). The raw-term dump, the
% bussproofs/ND-tree/Fitch renderers and fitch_g4_proof/8 all expect the
% original single Gamma>Delta flat-list sequent instead. This walks a
% completed proof term once (proportional to proof size, not
% search-tree size) and rebuilds that flat-list sequent at every node,
% so nothing downstream of provable_at_level/3 ever sees the eight
% buckets separately.
% Proof nodes are built directly as the familiar Gamma>Delta sequent
% term: each rule receives Fl, the flat Gamma in insertion order, and
% records it. Nothing has to be translated afterwards, so this is now
% the identity -- kept only so existing call sites need no change.
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
/*
% --- Rule 9: L\/-> (optimized) --------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lorto(Gamma>Delta, P)) :-
    select(((A | B) => C), Gamma, G1), !,
    ( memberchk(A, G1), memberchk(B, G1) ->
      g4mic_proves([B=>C, A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; memberchk(A, G1) ->
      g4mic_proves([A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; memberchk(B, G1) ->
      g4mic_proves([B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ;
    g4mic_proves([A=>C, B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ).
*/
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

/*
% --- Rule 3: Rforall (deterministic: universal in succedent -> introduce eigenvar) --
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(Gamma > [A1 | D1], FV, Th, J1, SO, LL, P).
*/
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
