% =========================================================================
% TEST FILE FOR PURIFIED FITCH
% =========================================================================
:- [g4mic_nanocop_without_sequent].
:- [vii_bis_purified_fitch].

% =========================================================================
% HELPER: Prove theorem (same pipeline as prove/1 in driver)
% =========================================================================
test_theorem(Label, Formula) :-
    write('========================================'), nl,
    format('TEST: ~w~n', [Label]),
    write('========================================'), nl,
    copy_term(Formula, FCopy),
    prepare(FCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    retractall(premiss_list(_)),
    assertz(premiss_list([])),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([] > [F2])),
    abolish_all_tables,
    ( provable_at_level([] > [F2], minimal, Proof) ->
        Logic = minimal
    ; provable_at_level([] > [F2], constructive, Proof) ->
        Logic = intuitionistic
    ; provable_at_level([] > [F2], classical, Proof) ->
        Logic = classical
    ;
        write('FAIL: No proof found'), nl, fail
    ),
    format('OK: Proof found (~w)~n~n', [Logic]),

    write('--- STANDARD FITCH ---'), nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof),
    write('\\end{fitch}'), nl, nl,

    write('--- PURIFIED FITCH ---'), nl,
    render_purified_fitch(Proof),
    nl.


% =========================================================================
% RUN ALL TESTS
% =========================================================================
run_all_tests :-
    write('==========================================================='), nl,
    write('      TESTING PURIFIED FITCH STYLE MODULE                  '), nl,
    write('==========================================================='), nl, nl,

    % Test 1: Dummett - 2 dead L->-> lines expected
    test_theorem('~~(A->B v B->A) [Dummett, 2 dead lines]',
                 ~(~((a => b) | (b => a)))),
    nl,

    % Test 2: Peirce - 1 dead L->-> line expected
    test_theorem('~~(((A->B)->A)->A) [Peirce, 1 dead line]',
                 ~(~(((a => b) => a) => a))),
    nl,

    % Test 3: Identity - 0 dead lines
    test_theorem('A->A [identity, 0 dead lines]',
                 (a => a)),
    nl,

    % Test 4: Contraposition
    test_theorem('~~((~B->~A) <-> (A->B)) [contraposition]',
                 ~(~((~b => ~a) <=> (a => b)))),
    nl,

    % Test 5: Distribution - 0 dead lines
    test_theorem('(A & (B v C)) => ((A & B) v (A & C))',
                 ((a & (b | c)) => ((a & b) | (a & c)))),
    nl,

    write('==========================================================='), nl,
    write('      ALL TESTS COMPLETED                                  '), nl,
    write('==========================================================='), nl.
