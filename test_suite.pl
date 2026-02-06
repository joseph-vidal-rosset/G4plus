% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quanti
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% Syntaxe d'entree : sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% =========================================================================
% OPERATEURS LATEX (sortie formatee)
% ATTENTION : Respecter exactement les espaces !
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % espace pour quantificateurs
:- op(400, fx, ' \\bot ').      % falsity (#)
% Syntaxe LaTeX : sequent turnstile
:- op(1150, xfx, ' \\vdash ').

% ============================================
% DRIVER - Test Suite Runner with Timer
% ============================================

%! run_all_test_files
%  Execute l'integralite de la suite de tests avec mesure du temps
%  Inclut : tests unitaires, sequents FOL/Prop, Pelletier
run_all_test_files :-
    % Clean state at the very start
    abolish_all_tables,
    init_eigenvars,
    get_time(StartTime),
    writeln(''),
    writeln('##############################################'),
    writeln('#   START OF THE COMPLETE SERIES OF TESTS    #'),
    writeln('##############################################'),
    format('Start : ~w~n~n', [StartTime]),

    safe_run(run_all_tests, ' FOL Theorems '),
    safe_run(run_prop_seq, 'Propositional sequents'),
    safe_run(run_fol_seq, 'FOL Valid Sequents'),
    safe_run(run_pelletier, 'Pelletier Problems'),

    get_time(EndTime),
    ElapsedTime is EndTime - StartTime,

    writeln(''),
    writeln('##############################################'),
    writeln('#    END OF THE COMPLETE SERIES OF TESTS     #'),
    writeln('##############################################'),
    writeln('TOTAL: 134 formulas tested'),
    writeln('  • 107 numbered tests'),
    writeln('  • 27 Pelletier problems'),
    writeln(''),
    writeln('To check disagreements between g4mic and nanoCop:'),
    writeln('  Press Ctrl+F (or Cmd+F on Mac) and search for "Disagreement"'),
    writeln('  Browser shows "0 found" → 100% agreement!'),
    writeln(''),
    format_execution_time(ElapsedTime),
    writeln('').

%! safe_run(+Goal, +Name)
%  Execute un predicat de test avec gestion d'erreurs et chronometre
safe_run(Goal, Name) :-
    format('~n--- ~w ---~n', [Name]),
    % Clean state before each test group
    abolish_all_tables,
    init_eigenvars,
    get_time(Start),
    catch(
        (call(Goal) ->
            (get_time(End),
             Duration is End - Start,
             format('? ~w : SUCCES (~2f secondes)~n', [Name, Duration]))
        ;
            (get_time(End),
             Duration is End - Start,
             format('? ~w : ECHEC (~2f secondes)~n', [Name, Duration]))
        ),
        Error,
        (get_time(End),
         Duration is End - Start,
         format('? ~w : ERREUR - ~w (~2f secondes)~n', [Name, Error, Duration]))
    ).

%! format_execution_time(+Seconds)
%  Display execution time in readable format
format_execution_time(Seconds) :-
    Seconds < 60,
    !,
    format('Total execution time: ~2f seconds~n', [Seconds]).
format_execution_time(Seconds) :-
    Seconds < 3600,
    !,
    Minutes is floor(Seconds / 60),
    RemainingSeconds is Seconds - (Minutes * 60),
    format('Total execution time: ~d min ~2f sec~n', [Minutes, RemainingSeconds]).
format_execution_time(Seconds) :-
    Hours is floor(Seconds / 3600),
    RemainingMinutes is floor((Seconds - (Hours * 3600)) / 60),
    RemainingSeconds is Seconds - (Hours * 3600) - (RemainingMinutes * 60),
    format('Total execution time: ~d h ~d min ~2f sec~n', [Hours, RemainingMinutes, RemainingSeconds]).

% =========================================================================
% EXAMPLES FOR TESTING
% =========================================================================
/*
% Test cases:

% Should warn (term <=> term):
?- validate_and_warn(((a <=> b) & f(a)) => f(b), V).

% Should NOT warn (formula <=> formula):
?- validate_and_warn((p <=> q) => (p => q), V).

% Should warn in FOL context:
?- validate_and_warn(![x]:((x <=> a) => p(x)), V).

% Should NOT warn in propositional context:
?- validate_and_warn((a <=> b) => (b <=> a), V).  % if a,b are prop vars

*/
% =========================================================================
% END OF MODULE
% =========================================================================
% =========================================================================
% tests_pelletier.pl (mise a jour : Pel_18 corrigee en formule valide)
% Suite silencieuse Pelletier + benchmarks avec safe_time_out fallback.
% =========================================================================
/*
:- module(tests_pelletier,
    [ run_pelletier/0,
      run_pelletier_named/1,
      pelletier_tests/1,
      set_pelletier_timeout/1,
      pelletier_timeout/1,
      known_invalid/1
    ]).

:- use_module(library(lists)).
*/
% -------------------------------------------------------------------------
% Timeout configurable (en secondes). Valeur par defaut : 10 secondes.
% -------------------------------------------------------------------------
:- dynamic pelletier_timeout/1.
pelletier_timeout(10).

set_pelletier_timeout(Secs) :-
    ( number(Secs), Secs > 0 ->
        retractall(pelletier_timeout(_)),
        assertz(pelletier_timeout(Secs))
    ;
        throw(error(domain_error(positive_number, Secs), set_pelletier_timeout/1))
    ).

% -------------------------------------------------------------------------
% safe_time_out/3: wrapper robuste pour executer Goal avec timeout.
% - If time_out/3 exists, uses it.
% - Else if call_with_time_limit/2 exists, uses it.
% - Else runs goal without timeout.
% Result: success | failed | time_out | error(E)
% -------------------------------------------------------------------------
safe_time_out(Goal, Secs, Result) :-
    ( current_predicate(time_out/3) ->
        catch(time_out(Goal, Secs, R), E, (Result = error(E), !)),
        !,
        map_time_out_result(R, Result)
    ; current_predicate(call_with_time_limit/2) ->
        catch((call_with_time_limit(Secs, Goal), Result = success),
              time_limit_exceeded,
              ( Result = time_out )),
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

% -------------------------------------------------------------------------
% Liste des tests (Name - Formula)
% Respecte la syntaxe du driver : predicats p,q,... ; constantes a,b,c,... ; vars v,w,x,y,z
% Quantificateurs: ![x]: et ?[x]: (sans espace)
% -------------------------------------------------------------------------
:- multifile pelletier_tests/1.
pelletier_tests([
    'Pel_01_drinker' - (?[y]:(d(y) => ![x]:(d(x)))),
    'Pel_02_dn_forall_exists' - ((~(![x]:p(x))) <=> (?[x]:(~p(x)))),
    'Pel_03_forall_inst' - ((![x]:p(x)) => p(a)),
    'Extra_01_drinker_variant' - (?[x]:(p(x) => ![y]:(p(y) | q(y)))),
    'Pel_04_forall_preserve_exist' - ((![x]:(p(x) => q(x))) => ((?[x]:p(x)) => ?[x]:q(x))),
    'Pel_05_exists_conj_split' - ((?[x]:(p(x) & q(x))) => (?[x]:p(x) & ?[x]:q(x))),
    'Pel_06_leibniz' - (((a = b) & p(a)) => p(b)),
    'Pel_07_eq_sym' - ((a = b) <=> (b = a)),
    'Pel_08_eq_trans' - (((a = b) & (b = c)) => (a = c)),
   %  'Pel_09_quantifier_swap_failure' - (![x]:(?[y]:f(x,y)) => ?[y]:(![x]:f(x,y))),
    'Pel_10_exist_forall_exchange' - ((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))),
    'Pel_11_existential_elim_schema' - ((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)),
    'Pel_12_univ_distrib_impl' - ((![x]:(p(x) => q)) <=> ((?[x]:p(x)) => q)),
    'Pel_13_contraposition_classical' - ((p => q) <=> (~q => ~p)),
    'Pel_14_material_implication' - (((~ p | q) <=> (p => q))),
    'Pel_15_hypothetical_syllogism' - (((p => q) & (q => r)) => (p => r)),
    'Pel_16_existential_preservation' - (((![x]:(p(x) => q(x))) & ?[x]:p(x)) => ?[x]:q(x)),
    'Pel_17_biimp_to_impls' - ((p <=> q) => ((p => q) & (q => p))),
    % Pel_18 corrected: ?x (P(x) ? Q(x)) ? (?x P(x)) ? (?x Q(x))  (valid)
    'Pel_18_classical_choice' - ((?[x]:(p(x) | q(x))) <=> (?[x]:p(x) | ?[x]:q(x))),
    'Pel_19_pelletier_sample1' - ((![x]:(p(x) => ?[y]:q(x,y))) => ?[y]:(![x]:(p(x) => q(x,y)))),
    'Extra_03_choice_like' - ((![x]:(p(x) => q(x)) & ?[x]:p(x)) => ?[x]:q(x)),
    'Extra_04_equality_leibniz_pred' - (((a = b) & r(a)) => r(b)),
    'Extra_05_mixed_quant' - ((?[x]:(![y]:r(x,y))) => (![y]:(?[x]:r(x,y)))),
    'Extra_06_double_negation' - ((~ ~ p) => p),
    'Extra_07_peirce_variant' - ((((p => q) => p) => p)),
    'Extra_08_explosion' - ((p & ~ p) => #),
    'Extra_![x]: ?[y]:r(x,y)=> ?[y]:![x]:r(x,y)09_transfer' - ((![x]:(p(x) & q(x))) => (![x]:p(x) & ![x]:q(x)))
]).

% -------------------------------------------------------------------------
% known_invalid/1: tests intentionally skipped (none for Pel_18 anymore)
% -------------------------------------------------------------------------
:- dynamic known_invalid/1.
% Example: known_invalid('Pel_XX').

% -------------------------------------------------------------------------
% Runner: run_pelletier/0
% -------------------------------------------------------------------------
run_pelletier :-
    % Clean state before starting Pelletier tests
    abolish_all_tables,
    init_eigenvars,
    pelletier_tests(Tests),
    writeln('=== PELLETIER / HARD FOL TEST SUITE (direct execution, no timeout) ==='),
    run_pelletier_list(Tests, 1, 0, 0, 0, Tot),
    Tot = [Total, Proven, Failed, Skipped],
    nl,
    format('Done: ~d tests. Proven: ~d. Failed: ~d. Skipped: ~d.~n', [Total, Proven, Failed, Skipped]),
    writeln('===============================================================').

run_pelletier_list([], _, Proved, Failed, Skipped, [Total,Proved,Failed,Skipped]) :-
    Total is Proved + Failed + Skipped.
run_pelletier_list([Name-Formula|Rest], N, PAcc, FAcc, SAcc, Tot) :-
    format('~n[~d] ~w : ', [N, Name]),
    ( known_invalid(Name) ->
        writeln('SKIPPED (INVALID)'),
        PAcc1 is PAcc, FAcc1 is FAcc, SAcc1 is SAcc + 1
    ;
        % Clean state before each test to avoid table pollution and cyclic terms
        abolish_all_tables,
        init_eigenvars,
        % Direct call without timeout, matching run_all_tests structure
        catch(
            ( prove(Formula) ->
                Outcome = proved
            ;
                Outcome = not_proved
            ),
            E,
            Outcome = error(E)
        ),
        report_outcome(Outcome),
        ( Outcome = proved -> PAcc1 is PAcc + 1 ; PAcc1 is PAcc ),
        ( Outcome = proved -> FAcc1 is FAcc ; FAcc1 is FAcc + 1 ),
        SAcc1 is SAcc
    ),
    N1 is N + 1,
    run_pelletier_list(Rest, N1, PAcc1, FAcc1, SAcc1, Tot).

interpret_safe_result(time_out, _Status, timeout) :- !.
interpret_safe_result(success, proved, proved) :- !.
interpret_safe_result(success, not_proved, not_proved) :- !.
interpret_safe_result(failed, _Status, not_proved) :- !.
interpret_safe_result(error(E), _Status, error(E)) :- !.
interpret_safe_result(_, Status, Outcome) :- ( Status == proved -> Outcome = proved ; Outcome = not_proved ).

report_outcome(proved) :- writeln('PROVED').
report_outcome(not_proved) :- writeln('NOT PROVED').
report_outcome(timeout) :- writeln('TIMEOUT').
report_outcome(error(E)) :- format('ERROR: ~w~n', [E]).

% -------------------------------------------------------------------------
% run single named test
% -------------------------------------------------------------------------
run_pelletier_named(Name) :-
    % Clean state before running individual test
    abolish_all_tables,
    init_eigenvars,
    pelletier_tests(Tests),
    ( member(Name-Formula, Tests) ->
        ( known_invalid(Name) ->
            writeln('SKIPPED (INVALID)')
        ;
            format('Running test ~w...~n', [Name]),
            catch(
                ( prove(Formula) ->
                    writeln('PROVED')
                ;
                    writeln('NOT PROVED')
                ),
                E, format('ERROR: ~w~n', [E])
            )
        )
    ;
        format('Test ~w not found.~n', [Name])
    ).

% =========================================================================
% END of Pelletier tests
% =========================================================================

% =================================================================
% 1. BASIC TESTS - MINIMAL PROPOSITIONAL LOGIC
% =================================================================
% Identity and implication introduction tests
test_identity_simple :-
    write('1.'), nl,
    prove(p => p).
test_identity_complex :-
    write('2.'), nl,
    prove(p => (q => p)).
test_permutation :-
    write('3.'), nl,
    prove(p => (q => (p & q))).
% Conjunction tests
test_conjunction_intro :-
    write('4.'), nl,
    prove((p & q) => (q & p)).
test_conjunction_assoc :-
    write('5.'), nl,
    prove(((p & q) & r) => (p & (q & r))).
% Disjunction tests
test_disjunction_intro :-
    write('6.'), nl,
    prove(p => (p | q)).
test_disjunction_comm :-
    write('7.'), nl,
    prove((p | q) => (q | p)).
test_disjunction_elim :-
    write('8.'), nl,
    prove(((p => r) & (q => r)) => ((p | q) => r)).
% Biconditional tests
test_distrib_disj_over_conj :-
        write('9.'),nl,
        prove(((p | q) & (p | r)) <=> (p | (q & r))).
test_biconditional_intro :-
    write('10.'), nl,
    prove((p => q) => ((q => p) => (p <=> q))).
test_biconditional_elim :-
    write('11.'), nl,
    prove((p <=> q) => (p => q)).
% Modus Tollens tests (CORRECTED)
test_modus_tollens :-
    write('12.'), nl,
    prove(((p => q) & ~ q) => ~ p).
test_modus_tollens_complex :-
    write('13.'), nl,
    prove(((p => (q => r)) & ~ r) => (p => ~ q)).
test_absurdity_chain_m :-
    write('14.'), nl,
    prove(p => (~ p => #)).
% Negation introduction/elimination tests
test_negation_intro :-
    write('15.'), nl,
    prove((p => #) => ~ p).
test_negation_elim :-
    write('16.'), nl,
    prove((p & ~ p) => #).
% =================================================================
% 2. INTUITIONISTIC TESTS - NEGATION
% =================================================================
% Contradiction tests
test_contradiction_anything :-
    write('17.'), nl,
    prove(# => p).
test_absurdity_chain_i :-
    write('18.'), nl,
    prove((~ p => #) <=> ((p => #) => p)).
test_dn_Peirce :-
    write('19.'), nl,
    prove(~  ~  (((p => q) => p) => p)).
test_dn_Dummett :-
    write('20.'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_Dummett :-
    write('21.'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_classical_contraposition :-
    write('22.'), nl,
    prove(~  ~  ((~  q => ~  p) <=> (p => q))).
% =================================================================
% 3. CLASSICAL TESTS - BEYOND INTUITIONISTIC LOGIC
% =================================================================
% Indirect proof tests
test_indirect_proof :-
    write('23.'), nl,
    prove( ~  ~  p => p).
test_excluded_middle :-
    write('24.'), nl,
    prove(p | ~  p).
test_material_implication :-
    write('25.'), nl,
    prove((( ~  p | q) <=> (p => q))).
% Classical contraposition tests
test_contraposition_strong :-
    write('26.'), nl,
    prove(( ~  q => ~  p) => (p => q)).
test_absurdity_chain_c :-
    write('27.'), nl,
    prove((~ p => #) => p), nl.
% =================================================================
% 4. QUANTIFIER TESTS - CORRECTED SYNTAX
% =================================================================
% Basic universal tests
test_universal_intro :-
    write('28.'), nl,
    prove(![x]:(p(x) => p(x))).
test_universal_elim :-
    write('29.'), nl,
    prove((![x]:p(x)) => p(a)).
test_universal_distribution :-
    write('30.'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
% Basic existential tests
test_existential_intro :-
    write('31.'), nl,
    prove(p(a) => (?[x]:p(x))).
test_existential_elim :-
    write('32.'), nl,
    prove((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)).
test_mixed_quantifiers :-
    write('33.'), nl,
    prove((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))).
test_quantifier_negation :-
    write('34.'), nl,
    prove((~ (![x]:p(x))) <=> (?[x]: ~  p(x))).
test_Spinoza :-
        write('35. Spinoza: "nothing is contingent" '), nl,
        prove((![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))) & ![x]:(?[z]:d(z,x))) => ![x]: ~ c(x)).
test_Lepage :-
        write( '36. Lepage, Elements de logique contemporaine, p. 202, ex. 14*-g'), nl,
        prove((![x]:(f(x) <=> g(x)) & ![x]:(h(x) <=> i(x)) & ?[x]:(i(x) & ![y]:(f(y) => j(y)))) => ?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))).
test_Bostock :-
    write( '36-bis. Bostock, Intermediate Logic - Oxford , p. 279'), nl,
    prove(![x]:(?[y]:(f(x) & g(y))) => ?[y]:(![x]:(f(x) & g(y)))).
test_Pelletier_09 :-
    write( '36-ter. Pelletier 09 - counter-model '), nl,
    prove(![x]:(?[y]:f(x,y)) => ?[y]:(![x]:f(x,y))).
test_fol_instantiation :-
    write('37.'), nl,
    prove(![x]:p(x) => ?[x]:p(x)), nl.
test_fol_quantifiers_permutation :-
    write('38.'), nl,
    prove((?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))), nl.
test_russell_paradox :-
    write('38. Russell Paradox '), nl,
    prove((?[y]:(![x]:(~ b(x,x) <=> b(x,y)))) => #), nl.
% =================================================================
% 5. PREMISE TESTS - PRACTICAL REASONING
% =================================================================
% Modus ponens with premises
test_modus_ponens :-
    write('39.'), nl,
    prove(((p => q) & p) => q).
test_hypothetical_syllogism :-
    write('40.'), nl,
    prove(((p => q) & (q => r)) => (p => r)).
test_disjunctive_syllogism :-
    write('41.'), nl,
    prove(((p | q) & ~  p ) => q).

% Complex tests with quantifiers - SIMPLIFIED
test_universal_instantiation :-
    write('42.'), nl,
    prove((![x]:(h(x) => m(x)) & h(a)) => m(a)).
test_existential_generalization :-
    write('43.'), nl,
    prove(m(a) => ?[x]:m(x)).
% =================================================================
% 6. STRESS TESTS - COMPLEX FORMULAS
% =================================================================
test_complex_formula_1 :-
    write('44.'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
test_complex_formula_2 :-
    write('45.'), nl,
    prove(((p => q) & (r => s)) => ((p & r) => (q & s))).
test_Pelletier_17 :-
        write( '46. Pelletier 17' ),
        prove( ( ( p & ( q => r ) ) => s ) <=> ( ( ~ p | q | s ) & ( ~ p | ~ r | s ) ) ).
% =================================================================
% TEST RUNNERS
% =================================================================
run_all_tests :-
    write('========================================'), nl,
    write('FOL PROVER TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    % Minimal propositional tests
    write('=== MINIMAL PROPOSITIONAL LOGIC ==='), nl,
    test_identity_simple, nl,
    test_identity_complex, nl,
    test_permutation, nl,
    test_conjunction_intro, nl,
    test_conjunction_assoc, nl,
    test_disjunction_intro, nl,
    test_disjunction_comm, nl,
    test_disjunction_elim, nl,
    test_distrib_disj_over_conj, nl,
    test_biconditional_intro, nl,
    test_biconditional_elim, nl,
    test_modus_tollens, nl,
    test_modus_tollens_complex, nl,
    test_absurdity_chain_m,nl,
    test_negation_intro, nl,
    test_negation_elim, nl,

    % Intuitionistic tests
    write('=== INTUITIONISTIC LOGIC ==='), nl,
    test_contradiction_anything, nl,
    test_absurdity_chain_i, nl,
    test_dn_Peirce, nl,
    test_dn_Dummett,nl,
    test_dn_classical_contraposition,nl,


    % Classical tests
    write('=== CLASSICAL LOGIC ==='), nl,
    test_indirect_proof, nl,
    test_excluded_middle, nl,
    test_material_implication, nl,
    test_contraposition_strong, nl,

    % Quantifier tests
    write('=== QUANTIFIERS ==='), nl,
    test_universal_intro, nl,
    test_universal_elim, nl,
    test_universal_distribution, nl,
    test_existential_intro, nl,
    test_existential_elim, nl,
    test_mixed_quantifiers, nl,
    test_quantifier_negation, nl,
    test_Spinoza,nl,
    test_Lepage,nl,
    test_Bostock,nl,
    test_Pelletier_09,nl,
    test_fol_instantiation,nl,
    test_fol_quantifiers_permutation,nl,
    test_russell_paradox,nl,


    write('=== Usual logical truths ==='), nl,
    test_modus_ponens, nl,
    test_hypothetical_syllogism, nl,
    test_disjunctive_syllogism, nl,
    test_universal_instantiation, nl,
    test_existential_generalization, nl,

    % Stress tests
    write('=== STRESS TESTS ==='), nl,
   % test_complex_formula_1, nl,
    test_complex_formula_2, nl,
    test_Pelletier_17,nl,

    write('========================================'), nl,
    write('TEST SUITE END'), nl,
    write('========================================'), nl,
    !.

% Quick tests for immediate verification
quick_tests :-
    write('=== QUICK TESTS ==='), nl,
    test_identity_simple, nl,
    test_modus_tollens, nl.

% Individual MT test for debugging
test_mt_only :-
    write('=== ISOLATED MT TEST ==='), nl,
    test_modus_tollens, nl.


% =========================================================================
% TESTS FOL - FORMULES SIMPLES
% =========================================================================

%=================================================================
% SEQUENT TESTS - PROPOSITIONAL LOGIC ONLY
% Tests for sequents with premises (avoiding classical disjunction theorems)
% =================================================================

% =================================================================
% 1. BASIC SEQUENT TESTS - MINIMAL LOGIC
% =================================================================

% Identity with premises
test_seq_identity_premise :-
    write('47.'), nl,
    prove([p] > [p]), nl.

test_seq_weakening :-
    write('48.'), nl,
    prove([p, q] > [p]), nl.

test_seq_implication_intro :-
    write('49.'), nl,
    prove([p] > [q => p]), nl.

% =================================================================
% 2. CONJUNCTION SEQUENTS
% =================================================================

test_seq_conjunction_intro :-
    write('50.'), nl,
    prove([p, q] > [p & q]), nl.

test_seq_conjunction_elim_left :-
    write('51'), nl,
    prove([p & q] > [p]), nl.

test_seq_conjunction_elim_right :-
    write('52.'), nl,
    prove([p & q] > [q]), nl.

test_seq_conjunction_comm :-
    write('53.'), nl,
    prove([p & q] > [q & p]), nl.

test_seq_conjunction_assoc :-
    write('54.'), nl,
    prove([(p & q) & r] > [p & (q & r)]), nl.

test_seq_conjunction_nested :-
    write('55.'), nl,
    prove([p, q, r] > [(p & q) & r]), nl.

% =================================================================
% 3. IMPLICATION SEQUENTS
% =================================================================

test_seq_modus_ponens :-
    write('56.'), nl,
    prove([p => q, p] > [q]), nl.

test_seq_hypothetical_syllogism :-
    write('57.'), nl,
    prove([p => q, q => r] > [p => r]), nl.

test_seq_implication_chain :-
    write('58.'), nl,
    prove([p => q, q => r, p] > [r]), nl.

test_seq_curry :-
    write('59.'), nl,
    prove([(p & q) => r] > [p => (q => r)]), nl.

test_seq_uncurry :-
    write('60.'), nl,
    prove([p => (q => r)] > [(p & q) => r]), nl.

% =================================================================
% 4. DISJUNCTION SEQUENTS (NON-CLASSICAL)
% =================================================================

test_seq_disj_intro_left :-
    write('61.'), nl,
    prove([p] > [(p | q)]), nl.

test_seq_disj_intro_right :-
    write('62.'), nl,
    prove([q] > [(p | q)]), nl.

test_seq_disj_elim :-
    write('63.'), nl,
    prove([(p | q), p => r, q => r] > [r]), nl.

test_seq_disj_syllogism :-
    write('64.'), nl,
    prove([(p | q), ~ p] > [q]), nl.

test_seq_disj_comm :-
    write('65.'), nl,
    prove([(p | q)] > [(q | p)]), nl.

% =================================================================
% 5. NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_negation_intro :-
    write('66.'), nl,
    prove([p => #] > [~ p]), nl.

test_seq_negation_elim :-
    write('67.'), nl,
    prove([p, ~ p] > [#]), nl.

test_seq_explosion :-
    write('68.'), nl,
    prove([#] > [p]), nl.

test_seq_modus_tollens :-
    write('69.'), nl,
    prove([p => q, ~ q] > [~ p]), nl.

test_seq_contraposition_weak :-
    write('70.'), nl,
    prove([p => q] > [~ q => ~ p]), nl.

test_seq_double_negation_intro :-
    write('71.'), nl,
    prove([p] > [~ ~ p]), nl.

% =================================================================
% 6. BICONDITIONAL SEQUENTS
% =================================================================

test_seq_biconditional_intro :-
    write('72.'), nl,
    prove([p => q, q => p] > [p <=> q]), nl.

test_seq_biconditional_elim_left :-
    write('73.'), nl,
    prove([p <=> q] > [p => q]), nl.

test_seq_biconditional_elim_right :-
    write('74.'), nl,
    prove([p <=> q] > [q => p]), nl.

test_seq_biconditional_modus_ponens :-
    write('75.'), nl,
    prove([p <=> q, p] > [q]), nl.

% =================================================================
% 7. COMPLEX SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_complex_1 :-
    write('76.'), nl,
    prove([(p => q) , (q => r), p] > [r]), nl.

test_seq_complex_2 :-
    write('77.'), nl,
    prove([p , (q | r)] > [((p & q) | (p & r))]), nl.

test_seq_complex_3 :-
    write('78.'), nl,
    prove([(p | q) , (p | r)] > [(p | (q & r))]), nl.

test_seq_complex_4 :-
    write('79.'), nl,
    prove([p => (q => r)] > [q => (p => r)]), nl.



% =================================================================
% 8. DOUBLE NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_dn_peirce :-
    write('80.'), nl,
    prove([~ (((p => q) => p) => p)] > [#]), nl.

test_seq_dn_lem :-
    write('81.'), nl,
    prove([~ (p | ~ p)] > [#]), nl.

test_seq_dn_dummett :-
    write('82.'), nl,
    prove([~ ((p => q) | (q => p))] > [#]), nl.

% =================================================================
% TEST RUNNERS
% =================================================================

run_prop_seq :-
    write('========================================'), nl,
    write('SEQUENT TESTS - PROPOSITIONAL LOGIC'), nl,
    write('========================================'), nl, nl,

    write('=== 1. BASIC SEQUENTS ==='), nl,
    test_seq_identity_premise,
    test_seq_weakening,
    test_seq_implication_intro,

    write('=== 2. CONJUNCTION SEQUENTS ==='), nl,
    test_seq_conjunction_intro,
    test_seq_conjunction_elim_left,
    test_seq_conjunction_elim_right,
    test_seq_conjunction_comm,
    test_seq_conjunction_assoc,
    test_seq_conjunction_nested,

    write('=== 3. IMPLICATION SEQUENTS ==='), nl,
    test_seq_modus_ponens,
    test_seq_hypothetical_syllogism,
    test_seq_implication_chain,
    test_seq_curry,
    test_seq_uncurry,

    write('=== 4. DISJUNCTION SEQUENTS ==='), nl,
    test_seq_disj_intro_left,
    test_seq_disj_intro_right,
    test_seq_disj_elim,
    test_seq_disj_syllogism,
    test_seq_disj_comm,

    write('=== 5. NEGATION SEQUENTS ==='), nl,
    test_seq_negation_intro,
    test_seq_negation_elim,
    test_seq_explosion,
    test_seq_modus_tollens,
    test_seq_contraposition_weak,
    test_seq_double_negation_intro,

    write('=== 6. BICONDITIONAL SEQUENTS ==='), nl,
    test_seq_biconditional_intro,
    test_seq_biconditional_elim_left,
    test_seq_biconditional_elim_right,
    test_seq_biconditional_modus_ponens,

    write('=== 7. COMPLEX SEQUENTS ==='), nl,
    test_seq_complex_1,
    test_seq_complex_2,
    test_seq_complex_3,
    test_seq_complex_4,

    write('=== 8. DOUBLE NEGATION SEQUENTS ==='), nl,
    test_seq_dn_peirce,
    test_seq_dn_lem,
    test_seq_dn_dummett,

    write('========================================'), nl,
    write('SEQUENT TESTS END'), nl,
    write('========================================'), nl,
    !.

% Quick tests
quick_sequent_tests :-
    write('=== QUICK SEQUENT TESTS ==='), nl,
    test_seq_identity_premise,
    test_seq_modus_ponens,
    test_seq_disj_syllogism,
    test_seq_ltoto_2,
    write('=== QUICK TESTS END ==='), nl.
% =================================================================
% SEQUENT TESTS - FIRST ORDER LOGIC (FOL)
% Tests for sequents with quantifiers and predicates
% =================================================================

% =================================================================
% BASIC QUANTIFIER SEQUENTS
% =================================================================
test_seq_forall_elim :-
    write('83.'), nl,
    prove([![x]:p(x)] > [p(a)]).

test_seq_exists_intro :-
    write('84.'), nl,
    prove([p(a)] > [?[x]:p(x)]).

test_seq_exists_elim :-
    write('85.'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q)] > [q]).

% =================================================================
% QUANTIFIER DISTRIBUTION
% =================================================================

test_seq_forall_distribution :-
    write('86.'), nl,
    prove([![x]:(p(x) => q(x)), ![x]:p(x)] > [![x]:q(x)]).

test_seq_exists_distribution :-
    write('87.'), nl,
    prove([?[x]:(p(x) & q(x))] > [?[x]:p(x) & ?[x]:q(x)]).

test_seq_mixed_quantifiers :-
    write('88.'), nl,
    prove([?[y]:(![x]:p(x,y))] > [![x]:(?[y]:p(x,y))]).

% =================================================================
% QUANTIFIER NEGATION (DE MORGAN FOR QUANTIFIERS)
% =================================================================

test_seq_neg_forall :-
    write('89.'), nl,
    prove([~ (![x]:p(x))] <> [?[x]: ~ p(x)]).

test_seq_neg_exists :-
    write('90.'), nl,
    prove([~ (?[x]:p(x))] <> [![x]: ~ p(x)]).

% =================================================================
% MODUS PONENS WITH QUANTIFIERS
% =================================================================

test_seq_forall_mp :-
    write('91.'), nl,
    prove([![x]:(p(x) => q(x)), p(a)] > [q(a)]).

test_seq_exists_mp :-
    write('92.'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q(x))] > [?[x]:q(x)]).

% =================================================================
% CLASSICAL LOGIC WITH QUANTIFIERS
% =================================================================

test_seq_barber_paradox :-
    write('93.'), nl,
    prove([?[y]:(![x]:(~ b(x,x) <=> b(x,y)))] > [#]).

test_seq_drinker :-
    write('94.'), nl,
    prove([~ #] > [?[x]:(d(x) => ![y]:d(y))]).

% =================================================================
% SYLLOGISMS WITH QUANTIFIERS
% =================================================================

test_seq_barbara :-
    write('95.'), nl,
    prove([![x]:(m(x) => p(x)), ![x]:(s(x) => m(x))] > [![x]:(s(x) => p(x))]).

test_seq_darii :-
    write('96.'), nl,
    prove([![x]:(m(x) => p(x)), ?[x]:(s(x) & m(x))] > [?[x]:(s(x) & p(x))]).

test_seq_socrates :-
    write('97.'), nl,
    prove([![x]:(h(x) => m(x)), h(socrates)] > [m(socrates)]).

% =================================================================
% EQUALITY REASONING
% =================================================================

test_seq_eq_reflexive :-
    write('98.'), nl,
    prove([~ #] > [a = a]).

test_seq_eq_symmetric :-
    write('99.'), nl,
    prove([a = b] > [b = a]).

test_seq_eq_transitive :-
    write('100.'), nl,
    prove([a = b, b = c] > [a = c]).

test_seq_eq_substitution :-
    write('101.'), nl,
    prove([a = b, p(a)] > [p(b)]).

test_seq_eq_congruence :-
    write('102.'), nl,
    prove([a = b] > [f(a) = f(b)]).

% =================================================================
% COMPLEX FOL SEQUENTS
% =================================================================

test_seq_spinoza :-
    write('103. Spinoza'), nl,
    prove([
        ![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))),
        ![x]:(?[z]:d(z,x))
    ] > [![x]: ~ c(x)]).

test_seq_lepage :-
    write('104. Lepage - intutionistic version '), nl,
    prove([
        ![x]:(f(x) <=> g(x)),
        ![x]:(h(x) <=> i(x)),
        ?[x]:(i(x) & ![y]:(f(y) => j(y)))
             ] > [?[x]:(h(x) & ![y]:(g(y) => j(y)))]).

test_seq_bostock :-
    write('p. 258. Bostock  sequent version'),nl,
    prove([![x]:(?[y]:(f(x) & g(y)))] > [?[y]:(![x]:(f(x) & g(y)))]).

% =================================================================
% BICONDITIONAL SEQUENTS
% =================================================================

test_seq_bicond_left :-
    write('105.'), nl,
    prove([a <=> b, a] > [b]).

test_seq_bicond_right :-
    write('106.'), nl,
    prove([a => b, b => a] > [a <=> b]).

test_seq_bicond_quantifier :-
    write('107.'), nl,
    prove([![x]:(p(x) <=> q(x)), p(a)] > [q(a)]).

% =================================================================
% TEST RUNNERS
% =================================================================

run_fol_seq :-
        retractall(fitch_line(_, _, _, _)),      % <- Nettoyage global
    retractall(abbreviated_line(_)),
    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE START'), nl,
    write('========================================'), nl, nl,

    write('=== BASIC QUANTIFIERS ==='), nl,
    test_seq_exists_intro, nl,
    test_seq_exists_elim, nl,

    write('=== QUANTIFIER DISTRIBUTION ==='), nl,
    test_seq_forall_distribution, nl,
    test_seq_exists_distribution, nl,
    test_seq_mixed_quantifiers, nl,

    write('=== QUANTIFIER NEGATION ==='), nl,
    test_seq_neg_exists, nl,
    test_seq_neg_forall, nl,

    write('=== MODUS PONENS WITH QUANTIFIERS ==='), nl,
    test_seq_forall_mp, nl,
    test_seq_exists_mp, nl,

    write('=== CLASSICAL FOL ==='), nl,
    test_seq_barber_paradox, nl,
    test_seq_drinker, nl,

    write('=== SYLLOGISMS ==='), nl,
    test_seq_barbara, nl,
    test_seq_darii, nl,
    test_seq_socrates, nl,

    write('=== EQUALITY ==='), nl,
    test_seq_eq_reflexive, nl,
    test_seq_eq_symmetric, nl,
    test_seq_eq_transitive, nl,
    test_seq_eq_substitution, nl,
    test_seq_eq_congruence, nl,

    write('=== COMPLEX FOL ==='), nl,
    test_seq_spinoza, nl,
    test_seq_lepage, nl,
    test_seq_bostock, nl,

    write('=== BICONDITIONALS ==='), nl,
    test_seq_bicond_left, nl,
    test_seq_bicond_right, nl,
    test_seq_bicond_quantifier, nl,

    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE END'), nl,
    write('========================================'), nl.

run_quick_fol_sequent_tests :-
    write('=== QUICK FOL SEQUENT TESTS ==='), nl,
    test_seq_forall_elim, nl,
    test_seq_exists_intro, nl,
    test_seq_socrates, nl,
    test_seq_eq_transitive, nl,
    write('=== QUICK TESTS END ==='), nl.
