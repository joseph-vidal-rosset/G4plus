% =========================================================================
% G4+ TEST SUITE - Auto-counting, extensible test framework
% =========================================================================
% Architecture:
%   - Each test is registered as a g4_test(Group, Name, Formula) fact
%   - The runner collects all tests automatically via findall
%   - Adding a test = adding ONE g4_test/3 fact. That's it.
%   - The total count is always correct.
%
% Usage:
%   ?- run_all_test_files.        % Run everything
%   ?- run_group(minimal).        % Run one group
%   ?- run_test('Identity').      % Run one test by name
% =========================================================================

% =========================================================================
% OPERATOR DECLARATIONS
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quantifier
:- op( 500, fy, ?).             % existential quantifier
:- op( 500, xfy, :).            % quantifier separator

% =========================================================================
% LATEX OPERATORS (output formatting)
% =========================================================================
:- op( 500, fy, ' \\lnot ').
:- op(1000, xfy, ' \\land ').
:- op(1100, xfy, ' \\lor ').
:- op(1110, xfx, ' \\to ').
:- op(1120, xfx, ' \\leftrightarrow ').
:- op( 500, fy, ' \\forall ').
:- op( 500, fy, ' \\exists ').
:- op( 500, xfy, ' ').
:- op(400, fx, ' \\bot ').

% =========================================================================
% DYNAMIC COUNTER
% =========================================================================
:- dynamic test_counter/1.
:- dynamic test_pass/1.
:- dynamic test_fail/1.
:- dynamic test_error/1.

reset_counters :-
    retractall(test_counter(_)),
    retractall(test_pass(_)),
    retractall(test_fail(_)),
    retractall(test_error(_)),
    assertz(test_counter(0)),
    assertz(test_pass(0)),
    assertz(test_fail(0)),
    assertz(test_error(0)).

inc_counter(Which) :-
    ( Which = total -> Pred = test_counter
    ; Which = pass  -> Pred = test_pass
    ; Which = fail  -> Pred = test_fail
    ; Which = error -> Pred = test_error
    ),
    Term =.. [Pred, N],
    retract(Term),
    N1 is N + 1,
    NewTerm =.. [Pred, N1],
    assertz(NewTerm).

% =========================================================================
% TEST REGISTRY
% =========================================================================
% Format: g4_test(Group, Name, Formula)
%   Group: atom identifying the test category
%   Name:  descriptive string
%   Formula: the formula to prove
%
% To add a new test, just add a g4_test/3 fact anywhere below.
% The runner will find it automatically. No other changes needed.
% =========================================================================

% -----------------------------------------------------------------
% 1. MINIMAL PROPOSITIONAL LOGIC
% -----------------------------------------------------------------
g4_test(minimal, 'Identity (simple)', p => p).
g4_test(minimal, 'Identity (complex)', (p => (q => r)) => (p => (q => r))).
g4_test(minimal, 'Permutation', (p => (q => r)) => (q => (p => r))).
g4_test(minimal, 'Conjunction intro', (p => (q => (p & q)))).
g4_test(minimal, 'Conjunction assoc', ((p & q) & r) => (p & (q & r))).
g4_test(minimal, 'Disjunction intro', p => (p | q)).
g4_test(minimal, 'Disjunction comm', (p | q) => (q | p)).
g4_test(minimal, 'Disjunction elim', ((p => r) & (q => r)) => ((p | q) => r)).
g4_test(minimal, 'Distribution (bicond)', ((p | q) & (p | r)) <=> (p | (q & r))).
g4_test(minimal, 'Biconditional intro', (p => q) => ((q => p) => (p <=> q))).
g4_test(minimal, 'Biconditional elim', (p <=> q) => (p => q)).
g4_test(minimal, 'Modus tollens', ((p => q) & ~ q) => ~ p).
g4_test(minimal, 'Modus tollens complex', ((p => (q => r)) & ~ r) => (p => ~ q)).
g4_test(minimal, 'Absurdity chain (minimal)', p => (~ p => #)).
g4_test(minimal, 'Negation intro', (p => #) => ~ p).
g4_test(minimal, 'Negation elim', (p & ~ p) => #).

% -----------------------------------------------------------------
% 2. INTUITIONISTIC LOGIC
% -----------------------------------------------------------------
g4_test(intuitionistic, 'Ex falso', # => p).
g4_test(intuitionistic, 'Absurdity chain (intuit)', (~ p => #) <=> ((p => #) => p)).
g4_test(intuitionistic, 'DN Peirce', ~ ~ (((p => q) => p) => p)).
g4_test(intuitionistic, 'DN Dummett', ~ ~ ((p => q) | (q => p))).
g4_test(intuitionistic, 'DN Contraposition', ~ ~ ((~ q => ~ p) <=> (p => q))).

% -----------------------------------------------------------------
% 3. CLASSICAL LOGIC
% -----------------------------------------------------------------
g4_test(classical, 'Double negation elim', ~ ~ p => p).
g4_test(classical, 'Excluded middle', p | ~ p).
g4_test(classical, 'Material implication', (~ p | q) <=> (p => q)).
g4_test(classical, 'Strong contraposition', (~ q => ~ p) => (p => q)).
g4_test(classical, 'Absurdity chain (classical)', (~ p => #) => p).

% -----------------------------------------------------------------
% 4. FIRST-ORDER LOGIC - QUANTIFIERS
% -----------------------------------------------------------------
g4_test(fol, 'Universal identity', ![x]:(p(x) => p(x))).
g4_test(fol, 'Universal elim', (![x]:p(x)) => p(a)).
g4_test(fol, 'Universal distribution', (![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
g4_test(fol, 'Existential intro', p(a) => (?[x]:p(x))).
g4_test(fol, 'Existential elim', (?[x]:p(x)) => ((![x]:(p(x) => q)) => q)).
g4_test(fol, 'Mixed quantifiers', (?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))).
g4_test(fol, 'Quantifier negation (bicond)', (~ (![x]:p(x))) <=> (?[x]: ~ p(x))).
g4_test(fol, 'Spinoza: nothing contingent',
    (![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))) & ![x]:(?[z]:d(z,x))) => ![x]: ~ c(x)).
g4_test(fol, 'Lepage p.202 ex.14*-g',
    (![x]:(f(x) <=> g(x)) & ![x]:(h(x) <=> i(x)) & ?[x]:(i(x) & ![y]:(f(y) => j(y)))) => ?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))).
g4_test(fol, 'Bostock p.279',
    ![x]:(?[y]:(f(x) & g(y))) => ?[y]:(![x]:(f(x) & g(y)))).
g4_test(fol, 'Forall instantiation', ![x]:p(x) => ?[x]:p(x)).
g4_test(fol, 'Quantifier permutation', (?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))).
g4_test(fol, 'Russell paradox', (?[y]:(![x]:(~ b(x,x) <=> b(x,y)))) => #).

% -----------------------------------------------------------------
% 5. PRACTICAL REASONING (usual logical truths)
% -----------------------------------------------------------------
g4_test(practical, 'Modus ponens', ((p => q) & p) => q).
g4_test(practical, 'Hypothetical syllogism', ((p => q) & (q => r)) => (p => r)).
g4_test(practical, 'Disjunctive syllogism', ((p | q) & ~ p) => q).
g4_test(practical, 'Universal instantiation', (![x]:(h(x) => m(x)) & h(a)) => m(a)).
g4_test(practical, 'Existential generalization', m(a) => ?[x]:m(x)).

% -----------------------------------------------------------------
% 6. STRESS TESTS
% -----------------------------------------------------------------
g4_test(stress, 'Complex formula', ((p => q) & (r => s)) => ((p & r) => (q & s))).
g4_test(stress, 'Pelletier 17',
    ((p & (q => r)) => s) <=> ((~ p | q | s) & (~ p | ~ r | s))).

% -----------------------------------------------------------------
% 7. PELLETIER PROBLEMS
% -----------------------------------------------------------------
:- dynamic pelletier_timeout/1.
pelletier_timeout(10).

set_pelletier_timeout(Secs) :-
    ( number(Secs), Secs > 0 ->
        retractall(pelletier_timeout(_)),
        assertz(pelletier_timeout(Secs))
    ;
        throw(error(domain_error(positive_number, Secs), set_pelletier_timeout/1))
    ).

% Pelletier tests use a different mechanism (timeout + known_invalid)
pelletier_tests([
    'Pel_01_drinker' - (?[y]:(d(y) => ![x]:(d(x)))),
    'Pel_02_double_neg' - (((p => q) => p) => p),
    'Pel_03_forall_inst' - ((~ (![x]:p(x))) <=> (?[x]: ~ p(x))),
    'Pel_04_CQ' - ((![x]:(p(x) => q)) <=> ((?[x]:p(x)) => q)),
    'Pel_05_contraposition' - (((~ q => ~ p) <=> (p => q))),
    'Pel_06_barber_paradox' - ((?[y]:(![x]:((~ b(x,x)) <=> b(x,y)))) => #),
    'Pel_07_neg_exists' - (~ ?[x]:p(x) <=> ![x]: ~ p(x)),
    'Pel_08_neg_forall' - (~ ![x]:p(x)  <=> ?[x]: ~ p(x)),
    'Pel_10_quant_distrib' - ((?[x]:p(x) | ?[x]:q(x)) <=> ?[x]:(p(x) | q(x))),
    'Pel_11_identity' - (p <=> p),
    'Pel_12_biconditional_assoc' - ((p <=> (q <=> r)) <=> ((p <=> q) <=> r)),
    'Pel_13_disjunction_conjunction' - ((p | (q & r)) <=> ((p | q) & (p | r))),
    'Pel_14_biconditional_expansion' - ((p <=> q) <=> ((q | ~ p) & (~ q | p))),
    'Pel_15_conditional_disjunction' - ((p => q) <=> (~ p | q)),
    'Pel_16_conditional_symmetry' - ((p => q) | (q => p)),
    'Pel_17_complex' - (((p & (q => r)) => s) <=> ((~ p | q | s) & (~ p | ~ r | s))),
    'Pel_18_exists_swap' - ((?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))),
    'Pel_19_demorgan' - (~ (p & q) <=> (~ p | ~ q)),
    'Pel_20_material_cond' - ((p => q) <=> (~ p | q)),
    'Pel_21_constructive_dilemma' - (((p | q) & (p => r) & (q => s)) => (r | s)),
    'Pel_22_conditional_biconditional' - ((![x]:(p <=> q)) => (p <=> q)),
    'Pel_23_biconditional_quantifier' - ((![x]:(p | q(x))) <=> (p | ![x]:q(x))),
   % 'Pel_24_dn_and_exists' - ((~ ?[x]:(s(x) & q(x)) & ![x]:(p(x) => (q(x) | r(x))) & ~ ?[x]:p(x) => ?[x]:q(x)) => ?[x]:(p(x) & r(x))),
    'Pel_25_exists_complex' - ((?[x]:p(x) & ![x]:(f(x) => (~ g(x) & r(x))) & ![x]:(p(x) => (g(x) & f(x))) & (![x]:(p(x) => q(x)) | ?[x]:(p(x) & r(x)))) => ?[x]:(q(x) & p(x))),
    'Pel_26_biconditional_exists' - ((?[x]:p(x) <=> ?[x]:q(x)) & (![x]:(![y]:((p(x) & q(y)) => (r(x) <=> s(y))))) => (![x]:(p(x) => r(x)) <=> ![x]:(q(x) => s(x)))),
    'Pel_27_exists_forall_mix' - ((?[x]:(f(x) & ~ g(x)) & ![x]:(f(x) => h(x)) & ![x]:((j(x) & i(x)) => f(x)) & ((?[x]:(h(x) & ~ g(x))) => ![x]:(i(x) =>  ~ h(x))))=>![x]:(j(x) => ~ i(x)))
]).

known_invalid('Pel_09_quant_distrib_invalid').

% =========================================================================
% SAFE TIMEOUT WRAPPER
% =========================================================================
safe_time_out(Goal, Secs, Result) :-
    ( current_predicate(time_out/3) ->
        catch(time_out(Goal, Secs, R), E, (Result = error(E), !)),
        !,
        map_time_out_result(R, Result)
    ; current_predicate(call_with_time_limit/2) ->
        catch(
            ( call_with_time_limit(Secs, Goal) -> Result = success ; Result = failed ),
            E,
            ( E = time_limit_exceeded -> Result = time_out ; Result = error(E) )
        ),
        !
    ;
        catch(( (call(Goal) -> Result = success ; Result = failed) ),
              E,
              ( Result = error(E) ))
    ).

map_time_out_result(time_out, time_out) :- !.
map_time_out_result(success, success) :- !.
map_time_out_result(failed, failed) :- !.
map_time_out_result(R, success) :- R \= time_out, R \= failed, R \= success, !.

% =========================================================================
% TEST RUNNERS
% =========================================================================

%! run_tests
%  Execute the complete test suite with auto-counting
run_tests :-
    init_eigenvars,
    reset_counters,
    get_time(StartTime),
    nl,
    writeln('##############################################'),
    writeln('#   START OF THE COMPLETE SERIES OF TESTS    #'),
    writeln('##############################################'),
    format('Start: ~w~n~n', [StartTime]),

    % Run theorem tests (auto-counted)
    safe_run(run_theorem_tests, 'Theorem Tests'),

    % Run Pelletier tests
    safe_run(run_pelletier, 'Pelletier Problems'),

    % Run hierarchy tests
    safe_run(run_hierarchy_tests, 'Hierarchy Tests'),

    % Final summary
    get_time(EndTime),
    ElapsedTime is EndTime - StartTime,

    % Count totals
    count_registered_tests(NRegistered),
    pelletier_tests(PelList), length(PelList, NPel),
    count_hierarchy_tests(NHierarchy),
    Total is NRegistered + NPel + NHierarchy,

    test_pass(NPass),
    test_fail(NFail),
    test_error(NError),

    nl,
    writeln('##############################################'),
    writeln('#    END OF THE COMPLETE SERIES OF TESTS     #'),
    writeln('##############################################'),
    format('TOTAL: ~d formulas tested~n', [Total]),
    format('  * ~d registered theorem tests~n', [NRegistered]),
    format('  * ~d Pelletier problems~n', [NPel]),
    format('  * ~d hierarchy tests~n', [NHierarchy]),
    format('  * Passed: ~d  Failed: ~d  Errors: ~d~n', [NPass, NFail, NError]),
    nl,
    writeln('To check disagreements between g4mic and nanoCop:'),
    writeln('  Press Ctrl+F (or Cmd+F on Mac) and search for "Disagreement"'),
    writeln('  Browser shows "0 found" -> 100% agreement!'),
    nl,
    format_execution_time(ElapsedTime),
    nl.

%! count_registered_tests(-N)
%  Count total g4_test/3 facts
count_registered_tests(N) :-
    findall(_, g4_test(_, _, _), All),
    length(All, N).

%! run_theorem_tests
%  Run all g4_test/3 registered tests, grouped by category
run_theorem_tests :-
    writeln('========================================'),
    writeln('THEOREM TEST SUITE'),
    writeln('========================================'),
    nl,
    % Get ordered list of groups
    findall(G, g4_test(G, _, _), AllGroups),
    sort(AllGroups, Groups),
    run_groups(Groups),
    writeln('========================================'),
    writeln('THEOREM TEST SUITE END'),
    writeln('========================================').

run_groups([]).
run_groups([Group|Rest]) :-
    group_label(Group, Label),
    format('~n=== ~w ===~n', [Label]),
    findall(Name-Formula, g4_test(Group, Name, Formula), Tests),
    run_test_list(Tests),
    run_groups(Rest).

%! run_test_list(+Tests)
%  Run a list of Name-Formula pairs
run_test_list([]).
run_test_list([Name-Formula|Rest]) :-
    inc_counter(total),
    test_counter(N),
    format('~d. ~w~n', [N, Name]),
    init_eigenvars,
    catch(
        ( prove(Formula) ->
            inc_counter(pass),
            nl
        ;
            inc_counter(fail),
            format('  *** FAILED: ~w~n~n', [Name])
        ),
        Error,
        ( inc_counter(error),
          format('  *** ERROR on ~w: ~w~n~n', [Name, Error])
        )
    ),
    run_test_list(Rest).

%! run_group(+GroupName)
%  Run tests from a single group
run_group(Group) :-
    reset_counters,
    group_label(Group, Label),
    format('~n=== ~w ===~n', [Label]),
    findall(Name-Formula, g4_test(Group, Name, Formula), Tests),
    run_test_list(Tests),
    test_pass(P), test_fail(F), test_error(E),
    format('~nResults: ~d passed, ~d failed, ~d errors~n', [P, F, E]).

%! run_test(+Name)
%  Run a single test by name
run_test(Name) :-
    ( g4_test(_, Name, Formula) ->
        format('Running: ~w~n', [Name]),
        prove(Formula)
    ;
        format('Test not found: ~w~n', [Name])
    ).

% =========================================================================
% PELLETIER TEST RUNNER (with timeout)
% =========================================================================
run_pelletier :-
    writeln('========================================'),
    writeln('PELLETIER PROBLEMS'),
    writeln('========================================'),
    nl,
    pelletier_tests(Tests),
    pelletier_timeout(Timeout),
    run_pelletier_list(Tests, 1, Timeout),
    writeln('========================================'),
    writeln('PELLETIER PROBLEMS END'),
    writeln('========================================').

run_pelletier_list([], _, _).
run_pelletier_list([Name-Formula|Rest], Idx, Timeout) :-
    format('~n[~d] ~w : ~n', [Idx, Name]),
    ( known_invalid(Name) ->
        write('  SKIPPED (known invalid)'), nl,
        inc_counter(pass)
    ;
        init_eigenvars,
        ( catch(
            ( safe_time_out(prove(Formula), Timeout, Result) ->
                true
            ;
                Result = failed
            ),
            CatchError,
            Result = error(CatchError)
          ) ->
            true
        ;
            Result = failed
        ),
        ( Result = success ->
            inc_counter(pass)
        ; Result = time_out ->
            format('  TIMEOUT (~d sec)~n', [Timeout]),
            inc_counter(fail)
        ; Result = failed ->
            format('  FAILED~n'),
            inc_counter(fail)
        ; Result = error(E) ->
            format('  ERROR: ~w~n', [E]),
            inc_counter(error)
        ;
            inc_counter(pass)  % Other success
        )
    ),
    Idx1 is Idx + 1,
    run_pelletier_list(Rest, Idx1, Timeout).

% =========================================================================
% GROUP LABELS
% =========================================================================
group_label(minimal, 'MINIMAL PROPOSITIONAL LOGIC').
group_label(intuitionistic, 'INTUITIONISTIC LOGIC').
group_label(classical, 'CLASSICAL LOGIC').
group_label(fol, 'FIRST-ORDER LOGIC').
group_label(practical, 'PRACTICAL REASONING').
group_label(stress, 'STRESS TESTS').
group_label(Group, Group).  % fallback: use group name as-is

% =========================================================================
% UTILITIES
% =========================================================================

%! safe_run(+Goal, +Name)
%  Execute a test predicate with error handling and timer
safe_run(Goal, Name) :-
    format('~n--- ~w ---~n', [Name]),
    init_eigenvars,
    get_time(Start),
    catch(
        (call(Goal) ->
            (get_time(End),
             Duration is End - Start,
             format('~n? ~w : SUCCESS (~2f seconds)~n', [Name, Duration]))
        ;
            (get_time(End),
             Duration is End - Start,
             format('~n? ~w : FAILURE (~2f seconds)~n', [Name, Duration]))
        ),
        Error,
        (get_time(End),
         Duration is End - Start,
         format('~n? ~w : ERROR - ~w (~2f seconds)~n', [Name, Error, Duration]))
    ).

%! format_execution_time(+Seconds)
%  Display execution time in readable format
format_execution_time(Seconds) :-
    Seconds < 60, !,
    format('Total execution time: ~2f seconds~n', [Seconds]).
format_execution_time(Seconds) :-
    Seconds < 3600, !,
    Minutes is floor(Seconds / 60),
    RemainingSeconds is Seconds - (Minutes * 60),
    format('Total execution time: ~d min ~2f sec~n', [Minutes, RemainingSeconds]).
format_execution_time(Seconds) :-
    Hours is floor(Seconds / 3600),
    RemainingMinutes is floor((Seconds - (Hours * 3600)) / 60),
    RemainingSeconds is Seconds - (Hours * 3600) - (RemainingMinutes * 60),
    format('Total execution time: ~d h ~d min ~2f sec~n',
           [Hours, RemainingMinutes, RemainingSeconds]).

% =========================================================================
% END OF TEST SUITE
% =========================================================================
% =========================================================================
% LOGIC HIERARCHY VERIFICATION SUITE
% Tests that verify each formula is proved at the CORRECT logic level.
% A test FAILS if the formula is proved at the wrong level.
%
% Format: hierarchy_test(Group, Name, Formula, ExpectedLevel)
%   ExpectedLevel: minimal | intuitionistic | classical
% =========================================================================

% -----------------------------------------------------------------
% GROUP 1: MINIMAL
% Must be proved at minimal level (no EFQ, no DNE, no LEM).
% -----------------------------------------------------------------
hierarchy_test(minimal, 'Identity',
    (p => p), minimal).
hierarchy_test(minimal, 'Modus ponens',
    ((p => q) & p) => q, minimal).
hierarchy_test(minimal, 'Hypothetical syllogism',
    ((p => q) & (q => r)) => (p => r), minimal).
hierarchy_test(minimal, 'Conjunction intro',
    (p => (q => (p & q))), minimal).
hierarchy_test(minimal, 'Conjunction elim left',
    (p & q) => p, minimal).
hierarchy_test(minimal, 'Conjunction elim right',
    (p & q) => q, minimal).
hierarchy_test(minimal, 'Disjunction intro left',
    p => (p | q), minimal).
hierarchy_test(minimal, 'Disjunction intro right',
    q => (p | q), minimal).
hierarchy_test(minimal, 'Disjunction elim',
    ((p | q) & (p => r) & (q => r)) => r, minimal).
hierarchy_test(minimal, 'Modus tollens',
    ((p => q) & ~ q) => ~ p, minimal).
hierarchy_test(minimal, 'Negation intro',
    (p => #) => ~ p, minimal).
hierarchy_test(minimal, 'Absurdity chain',
    p => (~ p => #), minimal).
hierarchy_test(minimal, 'Permutation',
    (p => (q => r)) => (q => (p => r)), minimal).
hierarchy_test(minimal, 'Exportation',
    ((p & q) => r) => (p => (q => r)), minimal).
hierarchy_test(minimal, 'Importation',
    (p => (q => r)) => ((p & q) => r), minimal).
hierarchy_test(minimal, 'Contraposition (weak)',
    (p => q) => (~ q => ~ p), minimal).
hierarchy_test(minimal, 'TNE depth 3 (Johansson)',
    ~ ~ ~ p => ~ p, minimal).
hierarchy_test(minimal, 'TNE depth 5',
               ~ ~ ~ ~ ~ p => ~ p, minimal).
hierarchy_test(minimal, 'De Morgan 1 (minimal)',
               (~ p & ~ q) => ~ (p | q), minimal).
hierarchy_test(minimal, 'De Morgan 2 (minimal)',
               ~ (p | q) => (~ p & ~ q), minimal).
hierarchy_test(minimal, 'De Morgan 3 (minimal)',
               (~ p | ~ q) => ~ (p & q), minimal).
hierarchy_test(minimal, 'Double negation intro',
               p => ~ ~ p, minimal).
hierarchy_test(minimal, 'Ex Falso Minimal',
               # => ~ q, minimal).
hierarchy_test(minimal, 'Contraposition (minimal)',
               (~ q => ~ p) => (~ ~ p => ~ ~ q), minimal).

% -----------------------------------------------------------------
% GROUP 2: INTUITIONISTIC
% Require EFQ but NOT classical axioms (DNE, LEM, Peirce).
% -----------------------------------------------------------------
hierarchy_test(intuitionistic, 'Ex falso quodlibet',
    # => p, intuitionistic).
hierarchy_test(intuitionistic, 'Ex falso (complex)',
    # => (p & q), intuitionistic).
hierarchy_test(intuitionistic, 'Ex falso (implication)',
   ~ p => (p => q), intuitionistic).
hierarchy_test(intuitionistic, 'Negation elim (EFQ form)',
    (p & ~ p) => q, intuitionistic).
hierarchy_test(intuitionistic, 'Disjunctive syllogism',
    ((p | q) & ~ p) => q, intuitionistic).
hierarchy_test(intuitionistic, 'Weakening (bot)',
    (p => #) => (p => q), intuitionistic).

% -----------------------------------------------------------------
% GROUP 3: CLASSICAL ONLY
% Require DNE, LEM, or Peirce. Must fail in intuitionistic.
% -----------------------------------------------------------------
hierarchy_test(classical_only, 'Excluded middle',
    p | ~ p, classical).
hierarchy_test(classical_only, 'Double negation elimination',
    ~ ~ p => p, classical).
hierarchy_test(classical_only, 'Peirce law',
    ((p => q) => p) => p, classical).
hierarchy_test(classical_only, 'Material implication',
    (p => q) <=> (~ p | q), classical).
hierarchy_test(classical_only, 'Strong contraposition',
    (~ q => ~ p) => (p => q), classical).
hierarchy_test(classical_only, 'Ex falso to LEM',
    (~ p => #) => p, classical).
hierarchy_test(classical_only, 'De Morgan 4 (classical)',
    ~ (p & q) => (~ p | ~ q), classical).
hierarchy_test(classical_only, 'Consequentia mirabilis',
    (~ p => p) => p, classical).
hierarchy_test(classical_only, 'Dummett (propositional)',
    (p => q) | (q => p), classical).

% -----------------------------------------------------------------
% GROUP 4: TNE BOUNDARY
% Precise frontier between TNE (minimal) and DNE (classical).
% -----------------------------------------------------------------
hierarchy_test(tne_boundary, 'TNE: ~~~A->~A (minimal)',
    ~ ~ ~ p => ~ p, minimal).
hierarchy_test(tne_boundary, 'TNE: ~~~~~A->~A (minimal)',
    ~ ~ ~ ~ ~ p => ~ p, minimal).
hierarchy_test(tne_boundary, 'DNE: ~~A->A (classical)',
    ~ ~ p => p, classical).
hierarchy_test(tne_boundary, 'DNI: A->~~A (minimal)',
    p => ~ ~ p, minimal).
hierarchy_test(tne_boundary, 'TNE implication (minimal)',
    ~ ~ ~ ~ ~ (p => q) => ~ (p => q), minimal).
hierarchy_test(tne_boundary, 'Suprinsingly minimal',
              (~ ~ p => ~ ~ q) => (~ q => ~ q), minimal).
% =========================================================================
% HIERARCHY TEST RUNNER
% =========================================================================

%! count_hierarchy_tests(-N)
count_hierarchy_tests(N) :-
    findall(_, hierarchy_test(_,_,_,_), All),
    length(All, N).

%! run_hierarchy_tests
%  Run all hierarchy tests, integrated into the main counter.
run_hierarchy_tests :-
    writeln('========================================'),
    writeln('HIERARCHY VERIFICATION TESTS'),
    writeln('========================================'),
    nl,
    findall(G, hierarchy_test(G,_,_,_), AllG),
    sort(AllG, Groups),
    run_hierarchy_groups(Groups),
    writeln('========================================'),
    writeln('HIERARCHY VERIFICATION TESTS END'),
    writeln('========================================').

run_hierarchy_groups([]).
run_hierarchy_groups([G|Rest]) :-
    hierarchy_group_label(G, Label),
    format('~n=== ~w ===~n', [Label]),
    findall(N-F-L, hierarchy_test(G, N, F, L), Tests),
    run_hierarchy_list(Tests),
    run_hierarchy_groups(Rest).

run_hierarchy_list([]).
run_hierarchy_list([Name-Formula-Expected|Rest]) :-
    inc_counter(total),
    test_counter(Num),
    format('~d. ~w ... ', [Num, Name]),
    ( catch(
        ( init_eigenvars,
          decide_silent(Formula, _Proof, ActualLevel) ),
        _Error,
        ActualLevel = error
      ) ->
        ( ActualLevel == Expected ->
            format('OK (~w)~n', [Expected]),
            inc_counter(pass)
        ;
            format('FAILED (expected ~w, got ~w)~n', [Expected, ActualLevel]),
            inc_counter(fail)
        )
    ;
        format('FAILED (not provable, expected ~w)~n', [Expected]),
        inc_counter(fail)
    ),
    run_hierarchy_list(Rest).

%! run_hierarchy_group(+Group)
%  Run a single hierarchy group standalone.
run_hierarchy_group(Group) :-
    hierarchy_group_label(Group, Label),
    format('~n=== ~w ===~n', [Label]),
    findall(N-F-L, hierarchy_test(Group, N, F, L), Tests),
    run_hierarchy_list(Tests).

% =========================================================================
% HIERARCHY GROUP LABELS
% =========================================================================
hierarchy_group_label(minimal,        'MINIMAL (no EFQ/DNE/LEM)').
hierarchy_group_label(intuitionistic, 'INTUITIONISTIC (EFQ, not DNE/LEM)').
hierarchy_group_label(classical_only,      'CLASSICAL ONLY (DNE or LEM required)').
hierarchy_group_label(tne_boundary,        'TNE BOUNDARY (nested negation frontier)').
hierarchy_group_label(G, G).

% =========================================================================
% END OF TEST SUITE
% =========================================================================
