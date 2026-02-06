% =========================================================================
% TEST LOADER - Load this file to run all tests
% =========================================================================
% This file ensures the main prover is loaded before running tests
% Usage: ?- [test_loader].
%        ?- run_all_test_files.
% =========================================================================

% First, load the main prover (adjust path as needed)
% IMPORTANT: Uncomment ONE of these lines depending on your setup:

% If using the fixed web2 version:
:- ['o_driver.pl'].
%:- ['g4mic_nanocop.pl'].
% :- ['viii_g4mic_nanoCop_driver.pl'].

% If using the original web_en version:
% :- ['g4mic_web_en.pl'].

% Or if you prefer, load it manually before loading this file:
% ?- ['g4mic_web_en.pl'].
?- ['test_suite.pl'].

% =========================================================================
% Verify that required predicates exist
% =========================================================================

:- initialization((
                         (current_predicate(prove/1) ->
                              writeln('✓ g4mic_nanoCop prover loaded successfully'),
			  writeln('To test the prover, type "run_all_test_files ." and press Enter'),
                              flush_output
                         ;   writeln('✗ ERROR: Main prover not loaded!'),
                             flush_output,
                             fail
                         )
                     )).

% =========================================================================
% Now load the test suite
% =========================================================================

% Include all test predicates below
% (This is where your test file content goes)

% =========================================================================
% OPERATOR DECLARATIONS (if not already loaded)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quantifier
:- op( 500, fy, ?).             % existential quantifier
:- op( 500, xfy, :).            % quantifier separator
:- op(800, xfx, <>).            % equivalence operator for sequents

% =========================================================================
% USAGE INSTRUCTIONS
% =========================================================================
% To run all tests:
%   1. Load the main prover first: ?- ['g4mic_web_en.pl'].
%   2. Load this test file: ?- ['test_suite.pl'].
%   3. Run tests: ?- run_all_test_files.
%
% Or in one go:
%   ?- ['g4mic_web_en.pl'], ['test_suite.pl'], run_all_test_files.
% =========================================================================

% ?- ['g4mic_web_en.pl'].
