% =========================================================================
% TEST LOADER - Load this file to run all tests
% =========================================================================
% Usage: ?- [prover_loader].
%        ?- run_tests.
% =========================================================================

% Load the main prover
:- ['g4mic_nanocop.pl'].
% :- [o_driver].
% Load the test suite
:- ['test_suite.pl'].

% =========================================================================
% Verify that required predicates exist
% =========================================================================
:- initialization((
    (current_predicate(prove/1) ->
        writeln('G4+ prover loaded successfully'),
        count_registered_tests(NT),
        pelletier_tests(PL), length(PL, NP),
        count_hierarchy_tests(NH),
        Total is NT + NP + NH,
        format('Test suite: ~d theorem tests + ~d Pelletier + ~d hierarchy = ~d total~n', [NT, NP, NH, Total]),
        writeln('Type: run_tests.'),
        flush_output
    ;   writeln('ERROR: Main prover not loaded!'),
        flush_output,
        fail
    )
)).
