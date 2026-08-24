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
% GAMMA COMPARTMENTS
% =========================================================================
% Ported from g4mic_nanocop_optimised.pl (branch compartmentalise-gamma):
% Gamma is held as eight separate arguments -- Atoms,Conj,Disj,ImplAtom,
% LandTo,LorTo,LtoTo,Quant -- threaded directly through g4mic_proves/g4mic_ax,
% one list per principal-connective bucket, instead of a flat list. Each
% propositional left rule consults only its own bucket instead of
% scanning all of Gamma. See CLAUDE.md, "Optimisations already applied",
% item 6, for the full rationale, the g/8-wrapper approach tried and
% rejected, and validation results.
%
% Bucket membership is exhaustive and mutually exclusive over the six
% shapes a Gamma member can have after negation normalisation:
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
% L0-> fires on ANY implication in Gamma whose antecedent is already
% present elsewhere, regardless of the antecedent's shape (this file's
% original, pre-compartmentalisation L0-> already had this behaviour --
% see the "member(A, G1)" test with no shape restriction two versions
% back in git history). gamma_all_implications_select/11 preserves it,
% scanning ImplAtom, LandTo, LorTo, LtoTo and the implication-shaped
% members of Quant, in that fixed order, before L&->/L\/->/L->-> fall
% back to their own bucket. Enumeration order across buckets does not
% reproduce the original flat-list select/3 order -- an accepted,
% documented divergence: it can change which valid proof is found first
% (and hence premise order in rendered output), never provability or
% logic-level classification.
%
% Proof-tree nodes carry the same eight buckets plus Delta as their
% first nine arguments (e.g. ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, ax)),
% rather than the original single Gamma>Delta sequent term.
% normalize_proof_gammas/2 (called from o_driver.pl) is the one place
% that translates this wide, search-internal shape back into the
% familiar Gamma>Delta flat-list sequent that render_sequent/3
% (v_sc_printer.pl) and fitch_g4_proof/8 (vii_flag_style.pl) already
% expect -- so neither of those needs to change.
%
% Scope note: this file had none of the five propositional
% micro-optimisations already applied to g4mic_nanocop_optimised.pl
% (atomicity-guard hoist, guard hoists, the atomic_formula/connective
% table, memberchk swaps, redundant-re-search removal) -- only the
% compartmentalisation (item 6) is ported here, at the user's request.
% Rule bodies below preserve this file's original member/select choices
% and conditional ordering wherever compartmentalisation doesn't force
% a change; atomic_formula/connective is introduced only because
% Gamma's Atoms bucket needs a "which formulas are atomic" test to be
% defined *somewhere*, and this is the shape that test naturally takes.
% =========================================================================

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

% gamma_insert(+F, +At,+Cj,+Dj,+I0,+IA,+IO,+IT,+Qt, -AtO,-CjO,-DjO,-I0O,-IAO,-IOO,-ITO,-QtO):
% the single classification point.
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
gamma_insert_list([], At,Cj,Dj,I0,IA,IO,IT,Qt, At,Cj,Dj,I0,IA,IO,IT,Qt).
gamma_insert_list([F|Fs], At,Cj,Dj,I0,IA,IO,IT,Qt, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO) :-
    gamma_insert(F, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    gamma_insert_list(Fs, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1, AtO,CjO,DjO,I0O,IAO,IOO,ITO,QtO).

gamma_from_list(List, At,Cj,Dj,I0,IA,IO,IT,Qt) :-
    gamma_insert_list(List, [],[],[],[],[],[],[],[], At,Cj,Dj,I0,IA,IO,IT,Qt).

% gamma_to_list(+At,...,+Qt, -FlatList): flatten all eight buckets into
% one list, in a fixed canonical order. Used only where a genuine flat
% list is required (proof rendering) -- never on the search path.
gamma_to_list(At,Cj,Dj,I0,IA,IO,IT,Qt, FlatList) :-
    append(At, Cj, L1), append(L1, Dj, L2), append(L2, I0, L3),
    append(L3, IA, L4), append(L4, IO, L5), append(L5, IT, L6),
    append(L6, Qt, FlatList).

% gamma_all_implications_select(-A, -B, +I0,+IA,+IO,+IT,+Qt, -I0O,-IAO,-IOO,-ITO,-QtO):
% the candidate generator for L0->. Plain disjunction (not if-then-else)
% so backtracking into a later candidate of an earlier bucket -- or
% into a later bucket entirely -- both work, exactly as select/3
% backtracking did on the flat list.
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
% connective to the matching bucket.
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
% ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, ax). render_sequent/3 and
% fitch_g4_proof/8 expect the original single Gamma>Delta flat-list
% sequent instead. This walks a completed proof term once (proportional
% to proof size, not search-tree size) and rebuilds that flat-list
% sequent at every node. Called from o_driver.pl, the one place a
% completed proof term is handed to the renderers.
normalize_proof_gammas(Proof, Proof) :-
    atomic(Proof), !.
normalize_proof_gammas(Proof, ProofOut) :-
    Proof =.. [Tag, At,Cj,Dj,I0,IA,IO,IT,Qt,Delta | Rest], !,
    gamma_to_list(At,Cj,Dj,I0,IA,IO,IT,Qt, FlatGamma),
    maplist(normalize_proof_arg, Rest, RestOut),
    ProofOut =.. [Tag, (FlatGamma > Delta) | RestOut].

normalize_proof_arg(Arg, ArgOut) :-
    ( compound(Arg) -> normalize_proof_gammas(Arg, ArgOut) ; ArgOut = Arg ).

% =========================================================================
% RULE 0: AXIOM
% =========================================================================

g4mic_ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, _, _, SkolemIn, SkolemIn, _,
         ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, ax)) :-
    member(A, At),
    Delta = [B],
    unify_with_occurs_check(A, B).

% =========================================================================
% g4mic_proves/15
% g4mic_proves(Atoms,Conj,Disj,ImplAtom,LandTo,LorTo,LtoTo,Quant, Delta,
%              FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
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
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL, Proof), !.

% --- Rule 1: L-bot -----------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, _, _, SI, SI, LL,
             lbot(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, #)) :-
    member(LL, [intuitionistic, classical]),
    member(#, At), !.

% --- Rule 4: R-> ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             rcond(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    Delta = [A => B], !,
    gamma_insert(A, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[B], FV, Th, SI, SO, LL, P).

% --- Rule 5: L& -----------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             land(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((A & B), Cj, Cj0), !,
    gamma_insert_list([A, B], At,Cj0,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, LL, P).

% --- Rule 6: L0-> (modus ponens on context) -------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             l0cond(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    gamma_all_implications_select(A, B, I0,IA,IO,IT,Qt, I0g,IAg,IOg,ITg,Qtg),
    gamma_shape_member(A, At,Cj,Dj,I0g,IAg,IOg,ITg,Qtg),
    ( LL == minimal, B == # -> true ; ! ),
    gamma_insert(B, At,Cj,Dj,I0g,IAg,IOg,ITg,Qtg, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, LL, P).

% --- Rule 7: L&-> ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             landto(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select(((A & B) => C), IA, IA0), !,
    gamma_insert((A => (B => C)), At,Cj,Dj,I0,IA0,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, LL, P).


% --- Rule 2: Lexists (deterministic: existential in antecedent -> introduce eigenvar) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             lex(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((?[_Z-X]:A), Qt, Qt0), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    gamma_insert(A1, At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, J1, SO, LL, P).


% --- Rule 8: R& (deterministic: Delta is a conjunction -> decompose immediately) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             rand(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[B], FV, Th, J1, SO, LL, P2).

% --- Rule 10: L\/ (left disjunction) --------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             lor(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P1, P2)) :-
    select((A | B), Dj, Dj0), !,
    gamma_insert(A, At,Cj,Dj0,I0,IA,IO,IT,Qt, AtA,CjA,DjA,I0A,IAA,IOA,ITA,QtA),
    gamma_insert(B, At,Cj,Dj0,I0,IA,IO,IT,Qt, AtB,CjB,DjB,I0B,IAB,IOB,ITB,QtB),
    g4mic_proves(AtA,CjA,DjA,I0A,IAA,IOA,ITA,QtA,Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves(AtB,CjB,DjB,I0B,IAB,IOB,ITB,QtB,Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 11: R\/ ---------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             ror(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    Delta = [(A | B)],
    (   g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[B], FV, Th, SI, SO, LL, P)
    ).


% --- Rule 9: L\/-> (optimized) --------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             lorto(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select(((A | B) => C), IO, IO0), !,
    ( gamma_shape_member(A, At,Cj,Dj,I0,IA,IO0,IT,Qt), gamma_shape_member(B, At,Cj,Dj,I0,IA,IO0,IT,Qt) ->
      gamma_insert_list([(B=>C), (A=>C)], At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ; gamma_shape_member(A, At,Cj,Dj,I0,IA,IO0,IT,Qt) ->
      gamma_insert((A=>C), At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ; gamma_shape_member(B, At,Cj,Dj,I0,IA,IO0,IT,Qt) ->
      gamma_insert((B=>C), At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ;
      gamma_insert_list([(A=>C), (B=>C)], At,Cj,Dj,I0,IA,IO0,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, LL, P).

% --- Rule 12: IP (indirect proof -- classical only, must be before L->->)  --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, classical,
             ip(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ gamma_shape_member((A => #), At,Cj,Dj,I0,IA,IO,IT,Qt),
    Th > 0,
    gamma_insert((A => #), At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[#], FV, Th, SI, SO, classical, P).

% --- Rule 13: L->-> --------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             ltoto(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P1, P2)) :-
    select(((A => B) => C), IT, IT0),
    \+ (B = #, gamma_shape_member(A, At,Cj,Dj,I0,IA,IO,IT0,Qt)),
    !,
    gamma_insert_list([A, (B => C)], At,Cj,Dj,I0,IA,IO,IT0,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    gamma_insert(C, At,Cj,Dj,I0,IA,IO,IT0,Qt, At2,Cj2,Dj2,I02,IA2,IO2,IT2,Qt2),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves(At2,Cj2,Dj2,I02,IA2,IO2,IT2,Qt2,Delta, FV, Th, J1, SO, LL, P2).


% --- Rule 3: Rforall (deterministic: universal in succedent -> introduce eigenvar) --
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             rall(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[A1 | D1], FV, Th, J1, SO, LL, P).

% =========================================================================
% THRESHOLD-BASED QUANTIFIER RULES
% =========================================================================

% --- Rule 14: CQ_m (quantifier conversion, all logics -- must precede Lforall) --
% (?[X]:A => B)  ->  ![X]:(A => B)
% Placed before Lforall so that the universal form is available for instantiation.
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             cq_m(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((?[Z-X]:A) => B, Qt, Qt0),
    gamma_insert(![Z-X]:(A => B), At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, LL, P).

% --- Rule 15: Lforall (universal instantiation, Otten's limitation) -----------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             lall(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    member((![_Z-X]:A), Qt),
    length(FV, Len), Len =< Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    gamma_insert(A1, At,Cj,Dj,I0,IA,IO,IT,Qt, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, [Y | FV], Th, SI, SO, LL, P), !.

% --- Rule 16: Rexists ----------------------------------------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, LL,
             rex(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FV, Len), Len < Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,[A1 | D1], [Y | FV], Th, SI, SO, LL, P), !.

% =========================================================================
% CLASSICAL QUANTIFIER CONVERSION RULE (classical)
% =========================================================================

% --- Rule 17: CQ_c (classical quantifier shift) ---------------------------
g4mic_proves(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, FV, Th, SI, SO, classical,
             cq_c(At,Cj,Dj,I0,IA,IO,IT,Qt,Delta, P)) :-
    select((![Z-X]:A) => B, Qt, Qt0),
    ( member((?[ZT-YT]:AT) => B, Qt0),
      \+ \+ ((A => B) = AT) ->
        gamma_insert(?[ZT-YT]:AT, At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ;
        gamma_insert(?[Z-X]:(A => B), At,Cj,Dj,I0,IA,IO,IT,Qt0, At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1)
    ),
    g4mic_proves(At1,Cj1,Dj1,I01,IA1,IO1,IT1,Qt1,Delta, FV, Th, SI, SO, classical, P).

% =========================================================================
% HELPER PREDICATES
% =========================================================================

% =========================================================================
% END of Prover
% =========================================================================
