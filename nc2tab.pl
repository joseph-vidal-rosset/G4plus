%% File: nc2tab.pl (v4 : free-variable tableau)
%%
%% Strategy: priority-queue expansion (alpha > delta > gamma > beta),
%% closure by unification of free variables with branch literals,
%% local unification per branch via copy_term at beta entry.
%%
%% Modes:
%%   beth(F)      -- concise: literals and closures from nanoCoP proof
%%   beth_tree(F) -- free-variable tableau


:- use_module(library(lists)).
:- use_module(library(pairs)).

:-style_check(-singleton).


:-[i_operators].
:-[nanocop20_swi_for_g4plus].
:-[nanocop_proof].
:-[nanocop_tptp2].

:- dynamic fv_count/1, delta_count/1, line_ctr/1, gamma_source/2.

%% ============================================================
%% ENTRY POINTS
%% ============================================================

beth(F)       :- time(run(F, concise)).
%beth_tree(F)  :- time(run(F, tree)).
prove(F):-  time(run(F, tree)).

run(F, Mode) :-
    reset_state,
    % Detect equality in the TPTP formula BEFORE translation
    ( nanocop_contains_equality(F) ->
        tptp_to_internal(F, I),
        leancop_equal(I, I2)        % add the equality axioms
    ;
        tptp_to_internal(F, I),
        I2 = I                      % no equality: keep I unchanged
    ),
    ( prove2(I2, [cut, comp(7)], Proof) ->
        resolve_free_vars(Proof),
        collect_skolem_indices(Proof, Idx),
        build_skolem_map(Idx, 1, SkMap),
        format("~n===  Proof search for : ~w ===~n~n", [F]),
        ( Mode == tree ->
            show_matrix(I2),         % uses the enriched formula
            show_connections(Proof, SkMap),
            format("~n=== Tableau ===~n~n"),
            run_tree(F, SkMap),      % run_tree uses the original TPTP formula
            nl
        ;
            format("(1)  ~w    [negated goal]~n", [~F]),
            walk_concise(Proof, SkMap, 2, [], _)
        ),
        !
    ;
        format("  nanoCoP failed.~n"),
        !,
        fail
    ).

%% ============================================================
%% MATRIX PREAMBLE
%%
%% We display the matrix EXACTLY as nanoCoP produces it, via
%% portray_clause/1. This shows the nested non-clausal structure
%% with prefixes (I^K)^V, sub-matrices, and shared free variables,
%% making the correspondence between tableau and nanoCoP's proof
%% immediate and transparent.
%% ============================================================

show_matrix(InternalF) :-
    bmatrix(InternalF, [cut, comp(7)], Mat),
    format("=== Non clausal Matrix (nanocop Prolog term) ===~n"),
    write('   '), portray_clause(Mat).

%% ============================================================
%% CONNECTIONS
%%
%% Extract and display the pairs of complementary literals whose
%% unification closes each path of the proof. The Proof term from
%% nanoCoP has structure [..., Lit, Kind:[NegLit|Sub], ...]
%% where Kind indicates whether this is an extension (integer clause
%% prefix), a reduction (atom 'r') or a lemma (atom 'l').
%%
%% For each such occurrence, we record the pair (Lit, NegLit, Kind).
%% ============================================================

show_connections(Proof, SkMap) :-
    format("~n=== Connections that close the proof ===~n"),
    walk_conns(Proof, [], ConnsRev),
    reverse(ConnsRev, Conns0),
    dedup_conns(Conns0, Conns),
    ( Conns == [] ->
        write('   (none found)'), nl
    ;
        print_conns(Conns, SkMap, 1)
    ).

%% Remove duplicates (=@= -equal) while preserving order of first occurrence.
dedup_conns([], []).
dedup_conns([C|Cs], [C|Rest]) :-
    \+ has_equal(Cs, C),
    !,
    filter_not_equal(Cs, C, Cs1),
    dedup_conns(Cs1, Rest).
dedup_conns([_|Cs], Rest) :-
    dedup_conns(Cs, Rest).

has_equal([X|_], Y) :- X =@= Y, !.
has_equal([_|Xs], Y) :- has_equal(Xs, Y).

filter_not_equal([], _, []).
filter_not_equal([X|Xs], Y, Rest) :-
    X =@= Y, !,
    filter_not_equal(Xs, Y, Rest).
filter_not_equal([X|Xs], Y, [X|Rest]) :-
    filter_not_equal(Xs, Y, Rest).

%% walk_conns(+Term, +Acc, -AccOut)
%% Deterministic walk over the Proof term, accumulating connections found
%% (as conn(Lit, NegLit, Kind) terms, in REVERSE order of occurrence).
walk_conns(T, A, A) :- var(T), !.
walk_conns(T, A, A) :- atomic(T), !.
walk_conns(T, A0, A) :-
    is_list(T), !,
    walk_conns_list(T, A0, A).
walk_conns(_:Sub, A0, A) :- !,
    walk_conns(Sub, A0, A).
walk_conns(T, A0, A) :-
    compound(T), !,
    T =.. [_|Args],
    walk_conns_args(Args, A0, A).

walk_conns_args([], A, A).
walk_conns_args([X|Xs], A0, A) :-
    walk_conns(X, A0, A1),
    walk_conns_args(Xs, A1, A).

%% walk_conns_list: scan list for [Lit, Cont | ...] patterns where Cont
%% starts with the complementary literal.
walk_conns_list([], A, A).
walk_conns_list([Lit, Cont | Rest], A0, A) :-
    is_lit_term(Lit),
    extract_cont(Cont, NegLit, Kind),
    complementary_lits(Lit, NegLit),
    !,
    A1 = [conn(Lit, NegLit, Kind) | A0],
    walk_conns(Cont, A1, A2),
    walk_conns_list(Rest, A2, A).
walk_conns_list([X|Xs], A0, A) :-
    walk_conns(X, A0, A1),
    walk_conns_list(Xs, A1, A).

%% extract_cont(+Cont, -NegLit, -Kind)
%% Recognises the three shapes:
%%   Int^_:[NegLit|_]    → extension
%%   r^_:[NegLit]        → reduction
%%   l^_:[]              → lemma (Proof1=[])
%% We also accept (I^K)^V:[NegLit|_] which is how extension clauses
%% appear when the proof stores the full prefix.
extract_cont(Cont, NegLit, extension) :-
    nonvar(Cont), Cont = (Prefix:Sub),
    prefix_kind(Prefix, extension),
    nonvar(Sub), Sub = [NegLit|_].
extract_cont(Cont, NegLit, reduction) :-
    nonvar(Cont), Cont = (Prefix:Sub),
    prefix_kind(Prefix, reduction),
    nonvar(Sub), Sub = [NegLit|_].

prefix_kind((_^_)^_, extension).
prefix_kind(I^_, extension)   :- integer(I).
prefix_kind(r^_,  reduction).

is_lit_term(L) :-
    ( L = -A -> atomic_or_compound_lit(A)
    ; L \= _:_, L \= ',', L \= ';',
      atomic_or_compound_lit(L)
    ).
atomic_or_compound_lit(A) :- atom(A), !.
atomic_or_compound_lit(A) :- compound(A), functor(A, F, _),
    \+ memberchk(F, [:, ^, -]).

complementary_lits(~A, B)  :- !, A == B.
complementary_lits(A, ~B)  :- \+ functor_is_neg(A), !, A == B.
complementary_lits(-A, B)  :- \+ functor_is_neg(B), !, A == B.
complementary_lits(A, -B)  :- \+ functor_is_neg(A), A == B.

functor_is_neg(T) :- nonvar(T), functor(T, F, 1), (F = (~) ; F = (-)).

%% Pretty-print one connection per line.
%% We display literals with their RAW nanoCoP notation (integer^[deps]),
%% exactly as they appear in the matrix. This guarantees perfect
%% correspondence between the matrix and the connections — no renaming
%% that might drift from the tableau's own Skolem names.
print_conns([], _, _).
print_conns([conn(L,NL,Kind)|Cs], SkMap, N) :-
    neg_form(L, RL),
    neg_form(NL, RNL),
    format("   ~w.  ~w  <->  ~w    [~w]~n", [N, RL, RNL, Kind]),
    N1 is N+1,
    print_conns(Cs, SkMap, N1).

%% Convert nanoCoP's internal -A notation to the displayed ~A.
neg_form(-A, ~A) :- !.
neg_form(L, L).

reset_state :-
    retractall(lit(_,_,_,_)),
    retractall(pathlim),
    retractall(nanocop_depth_limited),
    retractall(fv_count(_)), assertz(fv_count(0)),
    retractall(delta_count(_)), assertz(delta_count(0)),
    retractall(line_ctr(_)), assertz(line_ctr(1)),
    retractall(gamma_source(_,_)).

nanocop_contains_equality((_ = _)) :- !.
nanocop_contains_equality(~A) :- !, nanocop_contains_equality(A).
nanocop_contains_equality(A & B) :- !, (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).
nanocop_contains_equality(A | B) :- !, (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).
nanocop_contains_equality(A => B) :- !, (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).
nanocop_contains_equality(A <=> B) :- !, (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).
nanocop_contains_equality(![_]:A) :- !, nanocop_contains_equality(A).
nanocop_contains_equality(?[_]:A) :- !, nanocop_contains_equality(A).
nanocop_contains_equality(all _:A) :- !, nanocop_contains_equality(A).
nanocop_contains_equality(ex _:A)  :- !, nanocop_contains_equality(A).
nanocop_contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg), !.

%% ============================================================
%% FREE-VARIABLE TREE MODE
%%
%% Central data : a "task" on the queue is either
%%    step(Lab, SignedFormula)   -- an intermediate formula to emit & decompose
%%    or a signed literal (a leaf)
%%
%% The queue is processed in priority order. alpha decomposition yields
%% two consecutive tasks; beta yields a branching task. gamma creates a
%% free variable (attribute-tagged for display). delta creates a concrete
%% Skolem.
%%
%% A branch maintains a list BranchLits [Lit-Line | ...] used for closure
%% attempts on each new literal.
%% ============================================================

%% ============================================================
%% BETH TABLEAU -- TWO-LEVEL ENGINE
%%
%% Level 1: the Beth tableau rules proper (alpha, beta, gamma with
%%          duplication, delta, double negation, closure by reduction).
%%          A "matrix extension" is never one of the rules.
%%
%% Level 2: the nanoCoP matrix, read through Proof, acts as a database
%%          that STEERS the engine:
%%            - how many times to instantiate a gamma formula,
%%            - which witnesses to unify the free variables with,
%%            - which branches close against which lines.
%%          The matrix never replaces an inference rule; it only guides
%%          where the rules are applied.
%% ============================================================

run_tree(F, SkMap) :-
    %% Pre-pass: read Proof into a "proof map" (how many instances of
    %% each gamma, the witnesses used to close, and so on). The map is
    %% rudimentary for now.
    retractall(gamma_budget(_, _)),
    retractall(witness(_, _)),
    build_gamma_budget,
    %% Build the tableau with Beth rules only.
    next_line(1, _),
    build_root(F, SkMap, Tree),
    %% Render.
    pretty_tree(Tree).

%% build_gamma_budget: scan the lit/4 facts to work out how many fresh
%% copies of each "source clause" -- identified by the gamma formula it
%% came from -- Proof actually used.
%% Minimal implementation: leave a generous budget by default.
build_gamma_budget.

%% Default budget for any gamma formula: at most 3 instances.
%% Adjust to taste when using this for teaching.
default_gamma_budget(3).

%% ============================================================
%% TREE CONSTRUCTION
%%
%% A node is:
%%   node(Kind, Form, Line, Children)
%%     Kind in {root, alpha, beta_left, beta_right, dneg, gamma, delta, lit}
%%   closure(Line, Form, WithLine, WithForm, EqLine)
%%     -- only reduction closes a branch.
%%
%% A branch field Bs = [Lit-Line | ...] holds the literals already
%% emitted on the current branch, each with its line.
%% ============================================================

build_root(F, SkMap, node(root, ~F, 1, 0, [Child])) :-
    Queue0 = [qitem(~F, 1, done)],
    Bs0 = [~F-1],
    build_process(Queue0, Bs0, SkMap, Child).

%% build_process(+Queue, +Bs, +SkMap, -Tree)
%% Work through the queue in priority order (alpha < delta < gamma <
%% beta), add literals to Bs, and try to close by reduction after each
%% addition.

build_process([], _Bs, _SkMap, node(open, 'branch remains open', 0, [])).

build_process(Queue, Bs, SkMap, Tree) :-
    pick(Queue, qitem(F, OriginLine, State), Rest),
    build_step(F, OriginLine, State, Rest, Bs, SkMap, Tree).

%% Priority: alpha=1, double negation=2, delta=2, gamma=3, beta=4, literal=5.
pick(Queue, Best, Rest) :-
    rank_queue(Queue, Ranked),
    keysort(Ranked, Sorted),
    Sorted = [_-Best | RKV],
    pairs_values_(RKV, Rest).

pairs_values_([], []).
pairs_values_([_-V|T], [V|TT]) :- pairs_values_(T, TT).

rank_queue([], []).
rank_queue([qitem(F,P,S)|Fs], [R-qitem(F,P,S) | Rest]) :-
    priority(F, R),
    rank_queue(Fs, Rest).


priority(F, 1) :- is_alpha(F), !.
priority(F, 2) :- F = ~(~_), !.
priority(F, 2) :- is_delta(F), !.
priority(F, 3) :- is_gamma(F), !.
priority(F, 4) :- is_lit(F), !.      % <-- literals before beta
priority(F, 5) :- is_beta(F), !.     % <-- β en dernier
priority(_, 6).


%% ============================================================
%% build_step(+F, +Origin, +State, +Queue, +Bs, +SkMap, -Tree)
%%
%% Origin: the source line to cite when rendering, as [Origin].
%% State : 'fresh' (allocate a new line for F) or 'done' (F already sits
%%         on its line, do not reallocate -- the case of the initial
%%         goal).
%% General rule:
%%   1. Allocate line N = Origin (if done) or next_line (if fresh).
%%   2. Add F-N to Bs.
%%   3. Try to close by reduction.
%%   4. If the formula decomposes, queue its parts (fresh) with
%%      Origin=N.
%% ============================================================

%% The line to use for F, according to State.
resolve_line(done, Origin, Origin) :- !.
resolve_line(fresh, _, N) :- next_line(N, _).

%% --- LITERAL
build_step(F, Origin, State, Queue, Bs, SkMap, Tree) :-
    is_lit(F), !,
    resolve_line(State, Origin, N),
    ( try_reduction(F, Bs, red(WithForm, WithLine, EqLine)) ->
        Tree = node(lit, F, N, Origin, [closure(N, F, WithLine, WithForm, EqLine)])
    ;
        ( State == done -> BsNew = Bs ; BsNew = [F-N | Bs] ),
        build_process(Queue, BsNew, SkMap, Sub),
        Tree = node(lit, F, N, Origin, [Sub])
    ).

%% --- DOUBLE NEGATION: ~(~A) ==> A.
build_step(F, Origin, State, Queue, Bs, SkMap, node(dneg, F, N, Origin, [Sub])) :-
    F = ~(~A), !,
    resolve_line(State, Origin, N),
    Queue1 = [qitem(A, N, fresh) | Queue],
    BsNew = ( State == done -> Bs ; [F-N | Bs] ),
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    build_process(Queue1, Bs1, SkMap, Sub),
    ignore(BsNew = _).

%% --- ALPHA: emit F on its line (if fresh), then queue A and B.
%%     B is inserted before A so that A is processed first, which is the
%%     natural display order.
build_step(F, Origin, State, Queue, Bs, SkMap, node(alpha, F, N, Origin, [Sub])) :-
    is_alpha(F), !,
    resolve_line(State, Origin, N),
    alpha_parts(F, A, B),
    Queue1 = [qitem(B, N, fresh), qitem(A, N, fresh) | Queue],
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    build_process(Queue1, Bs1, SkMap, Sub).

%% --- DELTA: skolemise.
build_step(F, Origin, State, Queue, Bs, SkMap, node(delta, F, N, Origin, [Sub])) :-
    is_delta(F), !,
    resolve_line(State, Origin, N),
    delta_step(F, A, SkMap, Bs),
    Queue1 = [qitem(A, N, fresh) | Queue],
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    build_process(Queue1, Bs1, SkMap, Sub).

%% --- GAMMA: instantiate with a free variable, possibly re-borrowing.
build_step(F, Origin, State, Queue, Bs, SkMap, node(gamma, F, N, Origin, [Sub])) :-
    is_gamma(F), !,
    resolve_line(State, Origin, N),
    gamma_step(F, A),
    assertz(gamma_source(N, F)),
    tag_fvs_with_line(A, N),
    %% One instantiation by default. No automatic re-borrowing, to keep
    %% the search from blowing up combinatorially.
    Queue1 = [qitem(A, N, fresh) | Queue],
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    build_process(Queue1, Bs1, SkMap, Sub).


%% ============================================================
%% BETA, with lists and natural order
%% ============================================================

build_step(F, Origin, State, Queue, Bs, SkMap,
           node(beta, F, N, Origin, [LTree, RTree])) :-
    is_beta(F), !,
    resolve_line(State, Origin, N),
    beta_parts(F, L, R),
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    copy_term(pack(Queue, Bs1, L), pack(QL, BsL, LL)),
    copy_term(pack(Queue, Bs1, R), pack(QR, BsR, RR)),
    ensure_list(LL, LList),
    ensure_list(RR, RList),
    queue_add_list(LList, N, fresh, QL, QueueL),
    queue_add_list(RList, N, fresh, QR, QueueR),
    build_process(QueueL, BsL, SkMap, SubL),
    build_process(QueueR, BsR, SkMap, SubR),
    LTree = node(beta_left, [], 0, N, [SubL]),
    RTree = node(beta_right, [], 0, N, [SubR]).


%% Fallback.
build_step(F, Origin, State, Queue, Bs, SkMap, node(lit, F, N, Origin, [Sub])) :-
    resolve_line(State, Origin, N),
    ( State == done -> Bs1 = Bs ; Bs1 = [F-N | Bs] ),
    build_process(Queue, Bs1, SkMap, Sub).

ensure_list(X, [X]) :- \+ is_list(X), !.
ensure_list(X, X).

queue_add_list(Items, Line, State, Q, Qout) :-
    maplist({Line,State}/[Item, qitem(Item,Line,State)]>>true, Items, QItems),
    append(Q, QItems, Qout).

%% ============================================================
%% CLOSURE BY REDUCTION (and absurdity)
%% ============================================================

%% is_false/1: recognises the shapes absurdity can take.
is_false(F) :- F == $false.
is_false(F) :- F == false___.

%% try_reduction/3: try to close the branch. Returns
%%   red(Complement, LigneComplement, LigneEgalite)
%%   EqualityLine = 0 when no equality was used.

try_reduction(F, Bs, red(P, N, 0)) :-
    direct_reduction(F, Bs, P, N).

try_reduction(Lit, Bs, red(P, N, EqLine)) :-
    functor(Lit, F, _), F \== (=),
    member((L = R)-EqLine, Bs),
    ( paramodulate(Lit, L, R, NewLit) ; paramodulate(Lit, R, L, NewLit) ),
    NewLit \== Lit,
    direct_reduction(NewLit, Bs, P, N).

%% direct_reduction/4: immediate closure (absurdity, equality, literals).
direct_reduction(F, _Bs, '$false', 0) :-
    is_false(F), !.
direct_reduction((A = B), Bs, P, N) :-
    member(P-N, Bs),
    P = ~(C = D),
    ( unify_with_occurs_check(A, C), unify_with_occurs_check(B, D)
    ; unify_with_occurs_check(A, D), unify_with_occurs_check(B, C) ).
direct_reduction(~(A = B), Bs, P, N) :-
    member(P-N, Bs),
    P = (C = D),
    ( unify_with_occurs_check(A, C), unify_with_occurs_check(B, D)
    ; unify_with_occurs_check(A, D), unify_with_occurs_check(B, C) ).
direct_reduction(~(A = B), _Bs, '$false', 0) :-
    unify_with_occurs_check(A, B).
direct_reduction(F, Bs, P, N) :-
    member(P-N, Bs),
    opp_polarity(F, P),
    lit_atom(F, A1),
    lit_atom(P, A2),
    unify_with_occurs_check(A1, A2).

%% paramodulate/4: internal rewriting.
paramodulate_list([], _, _, []).
paramodulate_list([A|As], Old, New, [B|Bs]) :-
    (   unify_with_occurs_check(A, Old) -> B = New
    ;   paramodulate(A, Old, New, B)
    ),
    paramodulate_list(As, Old, New, Bs).

paramodulate(Term, Old, New, Result) :-
    compound(Term),
    Term =.. [F|Args],
    paramodulate_list(Args, Old, New, NewArgs),
    Result =.. [F|NewArgs].

paramodulate(Term, _, _, Term) :-
    \+ compound(Term).


%% ============================================================
%% BUDGET DE GAMMA-DUPLICATION
%% ============================================================

%% gamma_remaining(+GammaForm, -N): how many instances are still allowed.
gamma_remaining(F, N) :-
    ( gamma_budget_of(F, N) -> true
    ; default_gamma_budget(D), N = D,
      assertz(gamma_budget(F, D))
    ).

gamma_budget_of(F, N) :-
    gamma_budget(G, N),
    G =@= F, !.

decrement_gamma(F) :-
    retract(gamma_budget(G, N)),
    G =@= F, !,
    N1 is N - 1,
    assertz(gamma_budget(F, N1)).
decrement_gamma(_).

:- dynamic gamma_budget/2.
:- dynamic witness/2.

%% ============================================================
%% CLASSIFIERS AND DECOMPOSITION
%% ============================================================

is_alpha(~(_ => _)) :- !.
is_alpha(_ & _) :- !.
is_alpha((_,_)) :- !.
is_alpha(~(_ | _)) :- !.
is_alpha(~(_ ; _)) :- !.

is_beta(_ => _) :- !.
is_beta(~(_ & _)) :- !.
is_beta(~(_ , _)) :- !.
is_beta(_ | _) :- !.
is_beta((_ ; _)) :- !.
is_beta(_ <=> _) :- !.
is_beta(~(_ <=> _)) :- !.

is_gamma(~(?[_]:_)) :- !.
is_gamma(![_]:_) :- !.

is_delta(~(![_]:_)) :- !.
is_delta(?[_]:_) :- !.

alpha_parts(~(A => B), A, ~B).
alpha_parts(A & B, A, B).
alpha_parts((A,B), A, B).
alpha_parts(~(A | B), ~A, ~B).
alpha_parts(~(A ; B), ~A, ~B).

beta_parts(A => B, ~A, B).
beta_parts(~(A & B), ~A, ~B).
beta_parts(~(A , B), ~A, ~B).
beta_parts(A | B, A, B).
beta_parts((A ; B), A, B).
%% Dans beta_parts :
beta_parts(A <=> B, [A, B], [~A, ~B]).
beta_parts(~(A <=> B), [A, ~B], [~A, B]).

gamma_step(~(?[X]:F), ~Fi) :-
    fresh_fv(V, _),
    substitute(F, X, V, Fi).
gamma_step(![X]:F, Fi) :-
    fresh_fv(V, _),
    substitute(F, X, V, Fi).

delta_step(~(![X]:F), ~Fi, SkMap, Bs) :-
    retract(delta_count(D)), D1 is D+1, assertz(delta_count(D1)),
    ( member(sk(D1, Nm), SkMap) -> true ; skolem_name(D1, Nm) ),
    collect_fvs_in_branch(Bs, Deps),
    Sk = Nm^Deps,
    substitute(F, X, Sk, Fi).
delta_step(?[X]:F, Fi, SkMap, Bs) :-
    retract(delta_count(D)), D1 is D+1, assertz(delta_count(D1)),
    ( member(sk(D1, Nm), SkMap) -> true ; skolem_name(D1, Nm) ),
    collect_fvs_in_branch(Bs, Deps),
    Sk = Nm^Deps,
    substitute(F, X, Sk, Fi).

%% Collect the free variables occurring in the branch's formulas --
%% these are the dependencies of the fresh Skolem term.
collect_fvs_in_branch(Bs, Deps) :-
    findall(V,
            ( member(Form-_, Bs),
              term_variables(Form, Vs),
              member(V, Vs),
              var(V),
              get_attr(V, fvname, _)
            ),
            RawVs),
    sort(RawVs, Deps).

%% ============================================================
%% POLARITY UTILITIES
%% ============================================================

opp_polarity($false, ~ $false) :- !.      % for consistency
opp_polarity(~ $false, $false) :- !.
opp_polarity(~A, B) :- \+ is_neg(A), \+ is_neg(B), !.
opp_polarity(A, ~B) :- \+ is_neg(A), \+ is_neg(B), !.
opp_polarity(~_, A) :- \+ functor_is(A, ~, 1), !.
opp_polarity(A, ~_) :- \+ functor_is(A, ~, 1).

is_neg(T) :- nonvar(T), functor(T, F, 1), (F == (~) ; F == (-)).

lit_atom(~A, A) :- !.
lit_atom(-A, A) :- !.
lit_atom(A, A).

complementary_polarity(~A, -A) :- !.
complementary_polarity(-A, A) :- !.
complementary_polarity(A, -A).

has_fv(T) :- var(T), get_attr(T, fvname, _), !.
has_fv(T) :- compound(T), T =.. [_|Args], member(A, Args), has_fv(A), !.

is_negative_lit(~_) :- !.
is_negative_lit(-_).

%% ============================================================
%% PRETTY PRINTER DE L'ARBRE
%% ============================================================

%% ============================================================
%% PRETTY PRINTER
%% Helper: emit the line "(N)  F  [Origin]" unless N == Origin
%% (the 'done' case -- the parent already emitted that line).
%% ============================================================

emit_line(N, _F, Origin, _) :-
    N == Origin, !.  %% line already emitted (the 'done' case)
emit_line(N, F, Origin, _) :-
    pretty(F, P),
    ( Origin > 0 -> format("(~w)  ~w    [~w]~n", [N, P, Origin])
    ; format("(~w)  ~w~n", [N, P])
    ).

pretty_tree(node(root, F, N, _Origin, Children)) :-
    pretty(F, P),
    format("(~w)  ~w~n", [N, P]),
    print_children(Children).

pretty_tree(node(lit, F, N, Origin, Children)) :-
    emit_line(N, F, Origin, _),
    print_children(Children).

pretty_tree(node(dneg, F, N, Origin, Children)) :-
    emit_line(N, F, Origin, _),
    print_children(Children).

pretty_tree(node(alpha, F, N, Origin, Children)) :-
    emit_line(N, F, Origin, _),
    print_children(Children).

pretty_tree(node(delta, F, N, Origin, Children)) :-
    emit_line(N, F, Origin, _),
    print_children(Children).

pretty_tree(node(gamma, F, N, Origin, Children)) :-
    emit_line(N, F, Origin, _),
    print_children(Children).

pretty_tree(node(beta, F, N, Origin, [L, R])) :-
    emit_line(N, F, Origin, _),
    format("  [left branch]~n"),
    pretty_tree(L),
    format("  [right branch]~n"),
    pretty_tree(R).

pretty_tree(node(beta_left, _F, _N, _Origin, Children)) :-
    print_children(Children).

pretty_tree(node(beta_right, _F, _N, _Origin, Children)) :-
    print_children(Children).

pretty_tree(node(open, _, _, _, _)) :-
    format("   (branch open - not closed)~n").

pretty_tree(closure(N, _F, ON, _OF, EqLine)) :-
    ( ON == 0 ->
        format("      x    [absurdity]~n")
    ; EqLine == 0 ->
        format("      x    [~w-~w]~n", [N, ON])
    ;
        format("      x    [~w-~w, ~w]~n", [N, ON, EqLine])
    ).

print_children([]).
print_children([C|Cs]) :- pretty_tree(C), print_children(Cs).

%% UTILITIES : free variables with names (attribute-based),
%% Skolem dispensing, literal check, substitution, pretty printing
%% ============================================================

fresh_fv(V, Name) :-
    retract(fv_count(K)), K1 is K+1, assertz(fv_count(K1)),
    fv_name(K1, Name),
    put_attr(V, fvname, Name).

fvname:attr_unify_hook(_Name, _Other).

%% When copy_term duplicates an fv-tagged var, keep the name on the copy.
fvname:attribute_goals(V) --> [put_attr(V, fvname, Name)], { get_attr(V, fvname, Name) }.

%% Second attribute: source line of the gamma step that introduced this fv.
%% Set by tag_fvs_with_line/2 right after the gamma line is emitted.
fvline:attr_unify_hook(_Line, _Other).
fvline:attribute_goals(V) --> [put_attr(V, fvline, L)], { get_attr(V, fvline, L) }.

%% tag_fvs_with_line(+Term, +Line)
%% Walk Term, and for every unbound variable carrying fvname but no fvline,
%% attach fvline(Line). Variables that already have an fvline keep theirs
%% (they were introduced by earlier gamma steps).
tag_fvs_with_line(T, Line) :-
    term_variables(T, Vs),
    tag_fvs_list(Vs, Line).
tag_fvs_list([], _).
tag_fvs_list([V|Vs], Line) :-
    ( var(V), get_attr(V, fvname, _), \+ get_attr(V, fvline, _) ->
        put_attr(V, fvline, Line)
    ;
        true
    ),
    tag_fvs_list(Vs, Line).

%% fv_line_in(+Term, -Line)
%% Find the first variable in Term that carries an fvline attribute,
%% return that line. Fails if none.
fv_line_in(T, Line) :-
    term_variables(T, Vs),
    first_with_fvline(Vs, Line).
first_with_fvline([V|_], Line) :- var(V), get_attr(V, fvline, Line), !.
first_with_fvline([_|Vs], Line) :- first_with_fvline(Vs, Line).

fv_name(1, 'X').
fv_name(2, 'Y').
fv_name(3, 'Z').
fv_name(K, Nm) :-
    K > 3,
    Sub is (K-1) mod 3,
    Div is (K-1) // 3,
    nth0(Sub, ['X','Y','Z'], Base),
    atom_concat(Base, Div, Nm).

next_delta(SkMap, Name) :-
    retract(delta_count(D)), D1 is D+1, assertz(delta_count(D1)),
    ( member(sk(D1, N), SkMap) -> Name = N ; skolem_name(D1, Name) ).

next_line(N, N) :- retract(line_ctr(C)), N = C, C1 is C+1, assertz(line_ctr(C1)).

is_lit(A) :- is_false(A), !.        % $false and false___ count as literals
is_lit(~A) :- !, is_atom_sf(A).
is_lit(A) :- is_atom_sf(A).
is_atom_sf(A) :- atom(A), !, A \== true, A \== false.
is_atom_sf(A) :- compound(A), A =.. [F|_],
    \+ memberchk(F, [',', ';', '&', '|', =>, <=>, ~, -, all, ex, !, ?]).


functor_is(T, F, A) :- nonvar(T), functor(T, F, A).

substitute(F, X, T, T) :- F == X, !.
substitute(F, _, _, F) :- var(F), !.
substitute(F, _, _, F) :- atomic(F), !.
substitute(F, X, T, R) :-
    F =.. [Fu|As], sub_l(As, X, T, Rs), R =.. [Fu|Rs].
sub_l([], _, _, []).
sub_l([A|As], X, T, [R|Rs]) :- substitute(A, X, T, R), sub_l(As, X, T, Rs).

pretty(T, P) :-
    ( var(T) ->
        ( get_attr(T, fvname, N) -> P = N ; P = T )
    ; atomic(T) -> P = T
    ; T =.. [F|As], maplist(pretty, As, Rs), P =.. [F|Rs]
    ).

%% ============================================================
%% TPTP -> internal
%% ============================================================
tptp_to_internal(F, I) :- tptp_to_internal(F, [], I).
tptp_to_internal(V, _, V) :- var(V), !.
%% Handle $false and $true following Jens Otten's convention in leancop_tptp2.pl:
%%   $false  ->  (false___ , ~ false___)     -- explicit contradiction
%%   $true   ->  (true___ => true___)        -- tautology
tptp_to_internal($false, _, (false___ , ~ false___)) :- !.
tptp_to_internal($true,  _, (true___ => true___))    :- !.
tptp_to_internal(A, B, V) :- atomic(A), member(A-V, B), !.
tptp_to_internal(A, _, A) :- atomic(A), !.
tptp_to_internal(![X]:F, B, all V : IF) :- !, tptp_to_internal(F, [X-V|B], IF).
tptp_to_internal(?[X]:F, B, ex V : IF) :- !, tptp_to_internal(F, [X-V|B], IF).
tptp_to_internal(A & Bf, B, (IA, IB)) :- !, tptp_to_internal(A, B, IA), tptp_to_internal(Bf, B, IB).
tptp_to_internal(A | Bf, B, (IA ; IB)) :- !, tptp_to_internal(A, B, IA), tptp_to_internal(Bf, B, IB).
tptp_to_internal(A => Bf, B, IA => IB) :- !, tptp_to_internal(A, B, IA), tptp_to_internal(Bf, B, IB).
tptp_to_internal(~A, B, ~IA) :- !, tptp_to_internal(A, B, IA).
tptp_to_internal(T, B, T2) :-
    compound(T), T =.. [F|As], maplist_tpi(As, B, IAs), T2 =.. [F|IAs].

tptp_to_internal(A != B, Bs, ~(IA = IB)) :- !,
    tptp_to_internal(A, Bs, IA),
    tptp_to_internal(B, Bs, IB).

maplist_tpi([], _, []).
maplist_tpi([A|As], B, [I|Is]) :- tptp_to_internal(A, B, I), maplist_tpi(As, B, Is).

resolve_free_vars(P) :- term_variables(P, Vs), bn(Vs, 0).
bn([], _).
bn([V|Vs], N) :- atom_concat(c_, N, Nm), V = Nm, N1 is N+1, bn(Vs, N1).

collect_skolem_indices(P, S) :- wc(P, R), sort(R, S).
wc(T, []) :- (var(T); atomic(T)), !.
%% A Skolem is N^Deps where Deps is a list (possibly empty) of free-var args.
%% A clause prefix is I^K (entier^entier), NOT caught here.
wc(N^A, [N|R]) :- integer(N), is_list(A), !, wc(A, R).
wc(T, O) :- T =.. [_|A], wcl(A, O).
wcl([], []).
wcl([A|As], O) :- wc(A, O1), wcl(As, O2), append(O1, O2, O).

build_skolem_map([], _, []).
build_skolem_map([N|Ns], K, [sk(N,Nm)|R]) :-
    skolem_name(K, Nm), K1 is K+1, build_skolem_map(Ns, K1, R).

skolem_name(K, Nm) :- K>=1, K=<26, !, C is 0'a+K-1, atom_codes(Nm, [C]).
skolem_name(K, Nm) :- atom_concat(sk_, K, Nm).

%% ============================================================
%% CONCISE MODE (preserved, as in the base)
%% ============================================================

walk_concise([], _, N, _, N).
walk_concise([Item|Rest], SK, N0, Em, Nout) :- !,
    walk_item(Item, SK, N0, Em, N1, Em1),
    walk_concise(Rest, SK, N1, Em1, Nout).
walk_concise(Item, SK, N0, Em, Nout) :-
    walk_item(Item, SK, N0, Em, Nout, _).

/*
walk_item(Item, SK, N0, Em, N1, Em1) :-
    nonvar(Item), Item = (_CId^_K)^_Binding : Sub, !,
    walk_concise(Sub, SK, N0, Em, N1),
    Em1 = Em.
walk_item(Item, SK, N0, Em, N1, Em1) :-
    nonvar(Item), Item = _Idx : Sub, !,
    walk_concise(Sub, SK, N0, Em, N1),
    Em1 = Em.
*/
walk_item(Item, SK, N0, Em, N1, Em1) :-
    nonvar(Item), Item = ((_CId^_K)^_Binding : Sub), !,
    walk_concise(Sub, SK, N0, Em, N1),
    Em1 = Em.
walk_item(Item, SK, N0, Em, N1, Em1) :-
    nonvar(Item), Item = (_Idx : Sub), !,
    walk_concise(Sub, SK, N0, Em, N1),
    Em1 = Em.

walk_item(Lit, SK, N0, Em, N1, Em1) :-
    render_lit(Lit, SK, RLit),
    emit_or_close(RLit, N0, Em, N1, Em1).

emit_or_close(RLit, N0, Em, N1, Em1) :-
    ( is_false(RLit) ->
        format("(~w)  ~w~n", [N0, RLit]),
        format("  x   [absurdity]~n", []),
        N1 is N0 + 1,
        Em1 = Em
    ; ( member(PN-PL, Em), complementary_c(RLit, PL) ) ->
        format("(~w)  ~w~n", [N0, RLit]),
        format("  x   [closure: (~w), (~w)]~n", [PN, N0]),
        N1 is N0 + 1,
        Em1 = Em
    ;
        format("(~w)  ~w~n", [N0, RLit]),
        N1 is N0 + 1,
        Em1 = [N0-RLit | Em]
    ).

render_lit(-L, SK, ~RL) :- !, render_term(L, SK, RL).
render_lit(L, SK, RL) :- render_term(L, SK, RL).
render_term(T, _, T) :- var(T), !.
render_term(T, _, T) :- atomic(T), !.
render_term(N^Args, SK, R) :- integer(N), !, render_skolem(N, Args, SK, R).
render_term(T, SK, R) :-
    T =.. [F|As], render_list(As, SK, Rs), R =.. [F|Rs].
render_list([], _, []).
render_list([A|As], SK, [R|Rs]) :- render_term(A, SK, R), render_list(As, SK, Rs).
render_skolem(N, Args, SK, Term) :-
    ( member(sk(N, Name), SK) -> true ; skolem_name(N, Name) ),
    filter_meta(Args, Real),
    ( Real = [] -> Term = Name
    ; render_list(Real, SK, Rs), Term =.. [Name|Rs]
    ).
filter_meta([], []).
filter_meta([A|As], Rs) :-
    ( var(A) ; (atom(A), atom_concat(c_, _, A)) ), !, filter_meta(As, Rs).
filter_meta([A|As], [A|Rs]) :- filter_meta(As, Rs).

complementary_c(~A, B) :- !, A == B.
complementary_c(A, ~B) :- !, A == B.

%% ============================================================
%% TESTS
%% ============================================================

test_p18      :- beth(?[y]:![x]:(f(y) => f(x))).
test_p18_tree :- beth_tree(?[y]:![x]:(f(y) => f(x))).
test_p19      :- beth(?[x]:![y]:![z]:((p(y) => q(z)) => (p(x) => q(x)))).
test_p19_tree :- beth_tree(?[x]:![y]:![z]:((p(y) => q(z)) => (p(x) => q(x)))).
test_t8       :- beth((![x]:p(x)) => (p(a) & p(b))).
test_t8_tree  :- beth_tree((![x]:p(x)) => (p(a) & p(b))).
