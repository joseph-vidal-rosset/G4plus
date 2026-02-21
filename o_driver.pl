%============================================================================
% G4+: UNIFIED THEOREM PROVER FOR MINIMAL, INTUITIONISTIC AND CLASSICAL LOGIC
%============================================================================
%%==================================
%              DRIVER
%%==================================
% SYSTEM ARCHITECTURE:
% -------------------
% G4+ is a hybrid theorem prover combining:
%   1. G4 calculus (Roy Dyckhoff) - main proof engine
%   2. nanoCoP connection prover (Jens Otten) - validation & filtering
%   3. TPTP format support - interoperability standard
%
% PROOF STRATEGY:
% --------------
% Progressive logic escalation:
%   Minimal → Intuitionistic → Classical
% This maximizes constructive content while ensuring classical completeness.
%
% OUTPUT FORMATS:
% --------------
% Every successful proof is displayed in three styles:
%   1. G4 Sequent Calculus (bussproofs LaTeX) - direct G4 rules
%   2. Fitch-style Natural Deduction - pedagogical format
%   3. Tree-style Natural Deduction - visual format
%
% KEY FEATURES:
% ------------
% - Automatic logic level detection
% - Pattern-based classical optimization
% - nanoCoP cross-validation (100% agreement)
% - Publication-quality LaTeX output
% - TPTP library compatibility
% - WASM-ready (web deployment)
%
% MAIN INTERFACES:
% ---------------
% prove(Formula)           - Full proof with all styles
% prove(A <=> B)           - Biconditional equivalence
% prove_tptp(fof(...))     - TPTP format
% decide(Formula)          - Quick validity check
%
% AUTHORS:
% -------
% Joseph Vidal-Rosset (Université de Lorraine)
% Built upon: G4 (Roy Dyckhoff), nanoCoP (Jens Otten), leanSeq (Jens Otten)
%
% =========================================================================
% OPERATOR DECLARATIONS - Unified for g4mic + nanocop + TPTP
% =========================================================================
% The system integrates three components:
% - G4 calculus prover (main system)
% - nanoCoP connection prover (validation and filtering)
% - TPTP format support (standard automated reasoning format)
%
% The minimal_driver (ii_minimal_driver) provides the bridge between
% nanoCoP and G4, allowing nanoCoP to act as both a filter (rejecting
% invalid formulas early) and a cross-validator (confirming G4 results).
% =========================================================================
% :- use_module(library(lists)).
% :- use_module(library(statistics)).
% :- use_module(library(terms)).
% :- [i_operators].
% :- [ii_minimal_driver].  % To translate nanocop into g4mic and to  use nanocop as filter
% :- [vii_bis_clean_fitch].
% =========================================================================
% OPERATOR DECLARATIONS - Unified for g4mic + nanoCop + TPTP
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- [i_operators].
:- [ii_prover].
:- [iii_latex].
:- [iv_detections].
:- [v_sc_printer].
:- [vi_common_nd].
:- [vii_flag_style].
:- [viii_tree_style].
:- [ix_clean_fitch].
:- [x_tptp].
:-style_check(-singleton).
:-[nanocop20_swi].
:-[nanocop_proof].
:-[nanocop_tptp2].

% Activer le format d'explication complete d'Otten
:-retractall(proof(_)).
:-assert(proof(readable)).

:-dynamic g4mic_silent_mode/0.

% =========================================================================
% MAIN INTERFACE
% =========================================================================

nanocop_proves(Formula) :-
    % Forcer l'affichage
    retractall(g4mic_silent_mode),

    % Limite d'inferences avec LOGIQUE CORRECTE
    call_with_inference_limit(
        (
            % Detecter l'egalite AVANT traduction
            (nanocop_contains_equality(Formula) ->
                HasEquality = true
            ;
                HasEquality = false
            ),

            translate_formula(Formula, InternalFormula),

            % N'appeler leancop_equal QUE si egalite presente
            (HasEquality = true ->
                leancop_equal(InternalFormula, FormulaToProve)
            ;
                FormulaToProve = InternalFormula
            ),

            % IMPORTANT : PAS DE NEGATION - prove2 gere la refutation en interne
            ( time(prove2(FormulaToProve, [cut,comp(7)], Proof)) ->
              Result='Theorem'
            ;
              Result='Non-Theorem'
            ),
            bmatrix(FormulaToProve, [cut,comp(7)], Matrix),
            output_result(Formula, Matrix, Proof, Result),
            % VERIFIER le resultat
            Result='Theorem'
        ),
        2000000,
        InfResult
    ),
    ( InfResult == inference_limit_exceeded -> fail ; true ),!.

% =========================================================================
% nanocop_decides/1 :   Version SILENCIEUSE (avec stats)
% =========================================================================

nanocop_decides(Formula) :-
    assertz(g4mic_silent_mode),

    % Detecter l'egalite AVANT traduction
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    translate_formula(Formula, InternalFormula),

    % N'appeler leancop_equal QUE si egalite presente
    (HasEquality = true ->
        leancop_equal(InternalFormula, FormulaToProve)
    ;
        FormulaToProve = InternalFormula
    ),

    % IMPORTANT : PAS DE NEGATION - prove2 gere la refutation en interne
    prove2(FormulaToProve, [cut,comp(7)], _Proof),
    retractall(g4mic_silent_mode), !.

% =========================================================================
% EQUALITY DETECTION (copie de minimal_driver.pl)
% =========================================================================

nanocop_contains_equality((_ = _)) :- !.

nanocop_contains_equality(~A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(A & B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A | B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A => B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A <=> B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(![_]: A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(?[_]:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(all _:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(ex _:A) :- !,
    nanocop_contains_equality(A).

% Compound terms (check arguments recursively)
nanocop_contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg), !.

% Base case: no equality
nanocop_contains_equality(_) :- fail.

% =========================================================================
% OUTPUT RESULT
% =========================================================================

output_result(Formula, Matrix, Proof, Result) :-
    ( g4mic_silent_mode ->
        true
    ;
        nl,
        format('================================================================~n'),
        format('                     NANOCOP THEOREM PROVER~n'),
        format('================================================================~n~n'),
        write('Formula:         '), write(Formula), nl,
        write('Result:    '), write(Result), nl, nl,
        ( var(Proof) ->
            write('No proof found.      '), nl
        ;
            write('==========================================================='), nl,
            nanocop_proof(Matrix, Proof),
            write('==========================================================='), nl
        ), nl
    ),!.

% =========================================================================
% FORMULA TRANSLATION - COPIED EXACTLY FROM minimal_driver.pl
% =========================================================================

%% translate_formula(+InputFormula, -OutputFormula)
%% Translates from TPTP syntax to nanocop internal syntax
translate_formula(F, F_out) :-
    translate_operators(F, F_out).

% =========================================================================
% OPERATOR TRANSLATION - COPIED EXACTLY FROM minimal_driver.pl
% =========================================================================

% Bottom/falsum: # is translated to ~(p0 => p0) which represents _|_
translate_operators(F, (~(p0 => p0))) :-
    nonvar(F),
    (F == '#' ; F == f ; F == bot ; F == bottom ; F == falsum),
    !.

% Top/verum: t is translated to (p0 => p0) which represents T
translate_operators(F, (p0 => p0)) :-
    nonvar(F),
    (F == t ; F == top ; F == verum),
    !.

% Atomic formulas
translate_operators(F, F) :-
    atomic(F),
    \+ (F == '#'), \+ (F == f), \+ (F == bot),
    \+ (F == t), \+ (F == top),
    !.

% Variables
translate_operators(F, F) :-
    var(F), !.

% Negation
translate_operators(~A, (~A1)) :-
    !, translate_operators(A, A1).

% Disjunction
translate_operators(A | B, (A1 ; B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Conjunction
translate_operators(A & B, (A1 , B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Implication
translate_operators(A => B, (A1 => B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Biconditional
translate_operators(A <=> B, (A1 <=> B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Universal quantifier with brackets: ![X]:F
translate_operators(![Var]:A, (all RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Existential quantifier with brackets: ?[X]:F
translate_operators(?[Var]:A, (ex RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Universal quantifier simple syntax: !X:F (alternative)
translate_operators(!Var:A, (all VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% Existential quantifier simple syntax: ?X:F (alternative)
translate_operators(?Var:A, (ex VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% General compound terms (predicates with arguments)
translate_operators(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].

% =========================================================================
% VARIABLE SUBSTITUTION - COPIED EXACTLY FROM minimal_driver.pl
% =========================================================================

%% substitute_var_in_formula(+Formula, +OldVar, +NewVar, -NewFormula)
substitute_var_in_formula(Var, OldVar, NewVar, NewVar) :-
    atomic(Var), Var == OldVar, !.

substitute_var_in_formula(Atom, _OldVar, _NewVar, Atom) :-
    atomic(Atom), !.

substitute_var_in_formula(Var, _OldVar, _NewVar, Var) :-
    var(Var), !.

substitute_var_in_formula(Term, OldVar, NewVar, NewTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(substitute_var_in_formula_curry(OldVar, NewVar), Args, NewArgs),
    NewTerm =.. [F|NewArgs].

substitute_var_in_formula_curry(OldVar, NewVar, Arg, NewArg) :-
    substitute_var_in_formula(Arg, OldVar, NewVar, NewArg).


% =======================================================================================================================
% NANOCOP WRAPPER - (nanocop as Filter: a formula that is invalid according to nanocop is not submitted to g4mic)
% =======================================================================================================================
% This wrapper provides a silent interface to nanoCoP for use as a filtering mechanism.
% Key features:
% - WASM compatible: uses inference limits instead of time limits
% - Preserves occurs_check flag state
% - Returns silently (no output) - success/failure indicates validity
% - Used internally by G4+ to avoid attempting proofs of invalid formulas
%
% The filter strategy improves efficiency by eliminating hopeless proof attempts early.
% =======================================================================================================================

%  WASM compatible version
nanocop_decides_silent(Formula) :-
    current_prolog_flag(occurs_check, OriginalFlag),
    %  call inference limit instead of time limit
    catch(
        setup_call_cleanup(
            true,
            call_with_inference_limit(nanocop_decides(Formula), 2000000, _Result),
            set_prolog_flag(occurs_check, OriginalFlag)
        ),
        _Error,
        (set_prolog_flag(occurs_check, OriginalFlag), fail)
    ).

% =========================================================================
% NANOCOP REFUTATION ANALYSIS
% =========================================================================
% When nanoCoP determines a formula is invalid, this predicate provides
% detailed diagnostic information to help understand WHY it's invalid.
%
% The analysis includes:
% 1. Raw matrix construction (internal nanoCoP representation)
% 2. Open path extraction (path through matrix without complementary connection)
% 3. Counter-model assignments (truth value assignments that falsify the formula)
%
% This is particularly useful for:
% - Debugging formula errors
% - Understanding counter-examples
% - Teaching purposes (showing why a formula doesn't hold)
% =========================================================================

% STARTUP BANNER
% =========================================================================
% Disable automatic SWI-Prolog banner
:- set_prolog_flag(verbose, silent).

%
:- initialization(show_banner).

show_banner :-
    current_prolog_flag(version_data, swi(Major, Minor, Patch, _)),
    format('SWI-Prolog version ~w.~w.~w~n', [Major, Minor, Patch]),
    nl,
    write('================================================================'), nl,
    write('  G4+  --  Unified Prover for Minimal, Intuitionistic and'), nl,
    write('           Classical First-Order Logic (G4 + nanoCoP)'), nl,
    write('================================================================'), nl,
    write('  NOTE: Your formula must follow the correct syntax.'), nl,
    write('        Type  help.  for details.'), nl,
    write('----------------------------------------------------------------'), nl,
    write('  prove(Formula).           full proof with validation'), nl,
    write('  decide(Formula).          concise validity check'), nl,
    write('  prove_tptp(fof(...)).     TPTP format support'), nl,
    write('  prove_tptp_file(File).    process a TPTP .p file'), nl,
    write('  nanocop_proves(Formula).  nanoCoP engine, verbose'), nl,
    write('  nanocop_decides(Formula). nanoCoP engine, concise'), nl,
    write('  help.                     detailed help'), nl,
    write('  examples.                 formula examples'), nl,
    write('----------------------------------------------------------------'), nl,
    write('  End each query with a dot.'), nl,
    write('================================================================'), nl,
    nl.

% =========================================================================
% ITERATION LIMITS CONFIGURATION  (DO NOT CHANGE THESE VALUES !)
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 4).
logic_iteration_limit(minimal, 5).
logic_iteration_limit(intuitionistic, 3).
logic_iteration_limit(fol, 4).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% =========================================================================
% DYNAMIC DECLARATIONS
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.
:- dynamic current_logic_level/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================
% This section implements intelligent detection of classical logic patterns
% to optimize proof search strategy.
%
% Key optimizations:
% 1. Double negation elimination: ~~A -> A (in safe contexts)
% 2. Excluded middle detection: A \/ ~A patterns
% 3. DNE (Double Negation Elimination) presence checking
% 4. Peirce's law detection: ((A -> B) -> A) -> A
%
% Strategy:
% - If classical patterns detected early -> skip minimal/intuitionistic attempts
% - Start directly with classical logic rules
% - Avoid wasting time on constructive proof attempts for inherently classical formulas
%
% This is a significant performance optimization: formulas like ~~A -> A or
% A \/ ~A cannot be proven constructively, so detecting them early saves
% unnecessary backtracking through minimal and intuitionistic logic levels.
%
% Pattern detection is conservative: only triggers on clear classical markers
% to avoid false positives.
% =========================================================================

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :-
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !,
    formula_complexity(A, CA),
    C is CA + 2.
formula_complexity(A => B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !,
    formula_complexity(A, CA),
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !,
    formula_complexity(A, CA),
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :-
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================
% This is the main entry point for the G4+ theorem prover.
%
% Supported input formats:
% 1. Theorems: prove(F)
%    - Proves |- F (F is a tautology)
%
% 2. Biconditionals: prove(A <=> B)
%    - Equivalence between two formulas
%    - Proves both A -> B and B -> A
%
% For each input, the system:
% - Validates syntax
% - Detects required logic level (minimal/intuitionistic/classical)
% - Attempts proof with nanoCoP validation
% - Displays proofs in three styles (sequent calculus, Fitch, tree)
% =========================================================================


% =========================================================================
% BICONDITIONAL - Complete corrected section (grouped by proof style)
% =========================================================================
% Handles biconditional formulas (equivalences): prove(A <=> B)
%
% A biconditional A <=> B is proven by establishing both directions:
% - Direction 1: A -> B  (forward implication)
% - Direction 2: B -> A  (backward implication)
%
% Special handling:
% 1. If formula contains equality or function symbols:
%    -> Route exclusively to nanoCoP (G4 doesn't handle equality natively)
%
% 2. For pure propositional/FOL formulas:
%    -> Prove both directions with G4
%    -> Validate each direction with nanoCoP
%    -> Display proofs in all three styles (sequent, Fitch, tree)
%
% The system groups output by proof style rather than by direction,
% making it easier to compare the two directions in the same format.
%
% Bug fix applied: premiss_list is now properly initialized before
% each Fitch proof generation to ensure correct context rendering.
% =========================================================================

prove(Left <=> Right) :-
    % EQUALITY OR FUNCTIONS: ROUTE TO NANOCOP (EXCLUSIVE)
    g4mic_needs_nanocop(Left <=> Right),
    !,

    nl,
    write('============================================================='), nl,
    write('    - EQUALITY/FUNCTIONS DETECTED -> USING NANOCOP ENGINE    '), nl,
    write('============================================================='), nl,
    nl,

    validate_and_warn(Left <=> Right, _),

    write('Calling nanoCoP...'), nl, nl,

    % DIRECT CALL to nanocop_proves/1 - THAT'S ALL!
    nanocop_proves(Left <=> Right),

    write('==============================================================='), nl,
    write('Q.E.D.'), nl, nl,!.

%  ALTERNATIVE Clause - no equality/functions: g4mic

prove(Left <=> Right) :-
    \+ g4mic_needs_nanocop(Left <=> Right),  % Exclude equality and functions
    validate_and_warn(Left <=> Right, _ValidatedFormula),

        % ===============================================================
        % FILTRE NANOCOP (comme prove(Formula))
        % ===============================================================
        validate_and_warn(Left, _),
        validate_and_warn(Right, _),

        % NANOCOP FILTER (WASM version)
        current_prolog_flag(occurs_check, OriginalFlag),
        ( catch(
              setup_call_cleanup(
                  true,
                  % Use inference limit here as well
                  call_with_inference_limit(nanocop_decides(Left <=> Right), 2000000, _),
                  set_prolog_flag(occurs_check, OriginalFlag)
              ),
              _,
              (set_prolog_flag(occurs_check, OriginalFlag), fail)
          ) ->
          true
        ;
        szs_disproved_status(Left <=> Right, DisprStatus694),
        format('% SZS status ~w~n', [DisprStatus694]), !, fail
        ),

        % ===============================================================
        % PHASE 1 & 2: g4mic PROOF SEARCH (both directions)
        % ===============================================================
        % Test direction 1
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent(Left => Right)),
        ( catch(time((decide_silent(Left => Right, Proof1, Logic1))), _, fail) ->
            Direction1Valid = true
        ;
            Direction1Valid = false, Proof1 = none, Logic1 = none
        ),

        % Test direction 2
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent(Right => Left)),
        ( catch(time((decide_silent(Right => Left, Proof2, Logic2))), _, fail) ->
            Direction2Valid = true
        ;
            Direction2Valid = false, Proof2 = none, Logic2 = none
        ),

        nl,
        write('================================================================'), nl,
        write('           <->  BICONDITIONAL:  Proving Both Directions           '), nl,
        write('================================================================'), nl, nl,

        % ===============================================================
        % SEQUENT CALCULUS (both directions)
        % ===============================================================
        write('--- Sequent Calculus Proofs ---'), nl, nl,

        % Direction 1 - Sequent
        write('----------------------------------------------------------------'), nl,
        write('                ->   DIRECTION 1                                '), nl,
        write('           '), write(Left => Right), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction1Valid = true ->
            output_logic_label(Logic1), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % Direction 2 - Sequent
        write('----------------------------------------------------------------'), nl,
        write('                    <-   DIRECTION 2                            '), nl,
        write('               '), write(Right => Left), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction2Valid = true ->
            output_logic_label(Logic2), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % ===============================================================
        % NATURAL DEDUCTION - TREE STYLE (both directions)
        % ===============================================================
        write('--- Natural Deduction (tree style) ---'), nl, nl,

        % Direction 1 - ND Tree
        write('----------------------------------------------------------------'), nl,
        write('                     ->   DIRECTION 1                            '), nl,
        write('                '), write(Left => Right), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction1Valid = true ->
            render_nd_tree_proof(Proof1), nl, nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % Direction 2 - ND Tree
        write('----------------------------------------------------------------'), nl,
        write('                   <-   DIRECTION 2                              '), nl,
        write('                 '), write(Right => Left), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction2Valid = true ->
            render_nd_tree_proof(Proof2), nl, nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % ===============================================================
        % NATURAL DEDUCTION - FITCH STYLE (both directions)
        % ===============================================================
        write('--- Natural Deduction (flag style) ---'), nl, nl,

        % Direction 1 - Fitch
        write('----------------------------------------------------------------'), nl,
        write('                     ->   DIRECTION 1                           '), nl,
        write('                '), write(Left => Right), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction1Valid = true ->
            % write('\\begin{fitch}'), nl,
            % g4_to_fitch_theorem(Proof1),
            % write('\\end{fitch}'), nl, nl,
          render_clean_fitch(Proof1),nl,nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % Direction 2 - Fitch
        write('----------------------------------------------------------------'), nl,
        write('              <-   DIRECTION 2                                   '), nl,
        write('             '), write(Right => Left), nl,
        write('----------------------------------------------------------------'), nl, nl,
        ( Direction2Valid = true ->
            % write('\\begin{fitch}'), nl,
            % g4_to_fitch_theorem(Proof2),
            % write('\\end{fitch}'), nl, nl,
          render_clean_fitch(Proof2),nl,nl,
            write('Q.E.D.'), nl, nl
        ; write('  failed'), nl, nl
        ),

        % ===============================================================
        % SUMMARY
        % ===============================================================
        write('================================================================'), nl,
        write('                          - SUMMARY                             '), nl,
        write('================================================================'), nl,
        write('Direction 1 ('), write(Left => Right), write('): '),
        ( Direction1Valid = true ->
            write('  valid in '), write(Logic1), write(' logic')
        ; write('  failed')
        ), nl,
        write('Direction 2 ('), write(Right => Left), write('): '),
        ( Direction2Valid = true ->
            write('  valid in '), write(Logic2), write(' logic')
        ; write('  failed')
        ), nl, nl,

        % Validation
        nl,
        write('--- Validation ---'), nl,
        nl,
        write('g4mic_decides:   '),
        ( catch(g4mic_decides(Left <=> Right), _, fail) ->
            write('true'), nl,
            G4micResult = valid
        ;
            write('false'), nl,
            G4micResult = invalid
        ),
        write('nanocop_decides: '),
        ( catch(time(nanocop_decides(Left <=> Right)), _, fail) ->
            write('true'), nl,
            NanoCopResult = valid
        ;
            write('false'), nl,
            NanoCopResult = invalid
        ),
        nl,
        ( G4micResult = valid, NanoCopResult = valid ->
            write('Both provers agree: valid.'), nl
        ; G4micResult = invalid, NanoCopResult = invalid ->
            write('Both provers agree: invalid.'), nl
        ; G4micResult = valid, NanoCopResult = invalid ->
            write('[!] SOUNDNESS BUG: g4mic=true, nanoCoP=false'), nl,
            write('    Please report to: joseph@vidal-rosset.net'), nl
        ; G4micResult = invalid, NanoCopResult = valid ->
            write('[!] COMPLETENESS ISSUE: g4mic=false, nanoCoP=true'), nl,
            write('    Please report to: joseph@vidal-rosset.net'), nl
        ),
        nl, nl, !.


% =========================================================================
% THEOREMS - Unified proof with 3 clear phases
% =========================================================================
% =========================================================================
% THEOREMS - Unified proof with 3 clear phases
% =========================================================================
prove(Formula) :-
    % EQUALITY OR FUNCTIONS: ROUTE TO NANOCOP (EXCLUSIVE)
    g4mic_needs_nanocop(Formula),
    !,

    nl,
    write('============================================================='), nl,
    write('    - EQUALITY/FUNCTIONS DETECTED -> USING NANOCOP ENGINE    '), nl,
    write('============================================================='), nl,
    nl,

    validate_and_warn(Formula, _),

    write('Calling nanoCoP...'), nl, nl,

    % DIRECT CALL to nanocop_proves/1 - THAT'S ALL!
    nanocop_proves(Formula),

    write('==============================================================='), nl,
    write('Q.E.D.'), nl, nl,!.

% ALTERNATIVE CLAUSE: No equality/functions -> normal g4mic flow
prove(Formula) :-
    \+ g4mic_needs_nanocop(Formula),  % Exclude equality and functions
    validate_and_warn(Formula, _ValidatedFormula),
    % ===============================================================
    % NANOCOP FILTER (negative only)
    % ===============================================================
    % NANOCOP FILTER (WASM version)
    current_prolog_flag(occurs_check, OriginalFlag),
    ( catch(
          setup_call_cleanup(
              true,
              % Use inference limit here as well
              call_with_inference_limit(nanocop_decides(Formula), 2000000, _),
              set_prolog_flag(occurs_check, OriginalFlag)
          ),
          _,
          (set_prolog_flag(occurs_check, OriginalFlag), fail)
      ) ->
      true
    ;
    szs_disproved_status(Formula, DisprStatus),
    format('% SZS status ~w~n', [DisprStatus]), !, fail
    ),

    % ===============================================================
    % g4mic PROOF
    % ===============================================================
    write('--- G4 Proof for: '), write(Formula), nl,
    write('-----------------------------------------------------------'), nl,
    nl,

    retractall(premiss_list(_)),
    retractall(current_proof_sequent(_)),

    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),

    statistics(walltime, [Start|_]),

    ( provable_at_level([] > [F2], minimal, Proof) ->
        write('--- Minimal logic ---'), nl,
        Logic = minimal,
        OutputProof = Proof

    ; provable_at_level([] > [F2], constructive, Proof) ->
        write('--- Intuitionistic logic ---'), nl,
        Logic = intuitionistic,
        OutputProof = Proof

    ; provable_at_level([] > [F2], classical, Proof) ->
        write('--- Classical logic ---'), nl,
        Logic = classical,
        OutputProof = Proof

    ;
        nl,
        write('[!] UNEXPECTED: g4mic failed but nanoCoP validated!'), nl,
        nl,
        write('This is likely a BUG in G4-mic.'), nl,
        write('Please help improve G4-mic by reporting this issue:'), nl,
        nl,
        write('  *  Email: joseph@vidal-rosset.net'), nl,
        write('  -  Include: the formula and this error message'), nl,
        nl,
        write('Thank you for your contribution!'), nl,
        nl,
        fail
    ),

    statistics(walltime, [End|_]),
    Time is (End - Start) / 1000,

    nl,
    format('G4mic time: ~3f seconds~n', [Time]),
    nl,
    format("% SZS status Theorem~n"), nl, output_proof_results(OutputProof, Logic, Formula),
    !,


    % ===============================================================
    % PHASE 3: EXTERNAL VALIDATION (displayed)
    % ===============================================================
    nl,
    write('================================================================'), nl,
    write('                  - PHASE 3: VALIDATION                         '), nl,
    write('================================================================'), nl,
    nl,

    % g4mic VALIDATION
    write('==============================================================='), nl,
    write('- g4mic_decides output'), nl,
    write('==============================================================='), nl,
    ( catch(g4mic_decides(Formula), _, fail) ->
        write('true.'), nl,
        G4micResult = valid
    ;
        write('false. '), nl,
        G4micResult = invalid
    ),
    nl,

    % NANOCOP VALIDATION (SILENCIEUX mais avec time/1)
    write('==============================================================='), nl,
    write('- nanocop_decides output'), nl,
    write('==============================================================='), nl,
    ( catch(time(nanocop_decides(Formula)), _, fail) ->
        write('true.'), nl,
        NanoCopResult = valid
    ;
        write('false.'), nl,
        NanoCopResult = invalid
    ),
    nl,

    % VALIDATION SUMMARY
    write('==============================================================='), nl,
    write('- Validation Summary'), nl,
    write('==============================================================='), nl,
    ( G4micResult = valid, NanoCopResult = valid ->
        write('  Both provers agree: '), write('true'), nl
    ; G4micResult = invalid, NanoCopResult = invalid ->
        write('  Both provers agree: '), write('false'), nl
    ; G4micResult = valid, NanoCopResult = invalid ->
        nl,
        write('============================================================='), nl,
        write('  DISAGREEMENT: g4mic=true, nanoCoP=false'), nl,
        write('============================================================='), nl,
        nl,
        write('This is a SOUNDNESS BUG in G4-mic (false positive).'), nl,
        write('G4-mic proved an invalid formula!'), nl,
        nl,
        write('URGENT: Please report this issue immediately:'), nl,
        write('  *  Email: joseph@vidal-rosset.net'), nl,
        write('  -  Include: the formula and full output'), nl,
        nl
    ; G4micResult = invalid, NanoCopResult = valid ->
        nl,
        write('============================================================='), nl,
        write('  DISAGREEMENT: g4mic=false, nanoCoP=true'), nl,
        write('============================================================='), nl,
        nl,
        write('This is a COMPLETENESS issue in G4-mic (false negative).'), nl,
        write('G4-mic failed to prove a valid formula.'), nl,
        nl,
        write('Please help improve G4-mic by reporting this:'), nl,
        write('  *  Email: joseph@vidal-rosset.net'), nl,
        write('  -  Include: the formula and validation output'), nl,
        nl
    ),
    nl, nl.
% =========================================================================
% HELPERS
% =========================================================================

% Prepare a list of formulas
% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, _OriginalFormula) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    retractall(current_logic_level(_)),
    assertz(current_logic_level(LogicType)),

    % Display logic label
    output_logic_label(LogicType),

    % Sequent Calculus
    write('--- Sequent Calculus Proof ---'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,

    write('--- Natural Deduction (tree style) ---'), nl, nl,
    render_nd_tree_proof(Proof), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('--- Natural Deduction (flag style) ---'), nl, nl,
    render_clean_fitch(Proof),nl,nl,
    write('Q.E.D.'), nl, nl,
    !.

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),

    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], minimal, Proof) ->
        Logic = minimal
    ; provable_at_level([] > [Formula], intuitionistic, Proof) ->
        Logic = intuitionistic
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL
% =========================================================================

provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,  % Initialize before each attempt
    ( g4mic_proves(Gamma > Delta, [], Threshold, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; init_eigenvars, g4mic_proves(Gamma > Delta, [], Threshold, 1, _, intuitionistic, P)     % <- Then intuitionistic if failure
    ),
    !.

provable_at_level(Sequent, LogicLevel, Proof) :-
    LogicLevel \= classical,  % For non-classical logics
    logic_iteration_limit(LogicLevel, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,
    g4mic_proves(Gamma > Delta, [], Threshold, 1, _, LogicLevel, Proof),
    !.

% =========================================================================
% CLASSICAL LOGIC
% =========================================================================
provable_at_level(Sequent, classical, Proof) :-
    Sequent = (Gamma > Delta),
    logic_iteration_limit(classical, MaxIter),
    for(Threshold, 0, MaxIter),
    init_eigenvars,
    g4mic_proves(Gamma > Delta, [], Threshold, 1, _, classical, Proof),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================

output_logic_label(minimal) :-
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :-
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :-
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).

% =========================================================================
% MINIMAL INTERFACE g4mic_decides/1
% =========================================================================

% g4mic_decides/1 for biconditionals
g4mic_decides(Left <=> Right) :- ! ,
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),

    % Test direction 1: Left => Right
    time((decide_silent(Left => Right, _Proof1, Logic1))),
    write('Direction 1 ('), write(Left => Right), write(') is valid in '),
    write(Logic1), write(' logic'), nl,

    % Test direction 2: Right => Left
    time((decide_silent(Right => Left, _Proof2, Logic2))),
    write('Direction 2 ('), write(Right => Left), write(') is valid in '),
    write(Logic2), write(' logic'), nl,
    !.



% g4mic_decides/1 for theorems (catch-all - must come last)
g4mic_decides(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),

    % Follow the same logic progression as prove/1
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        % Double negation detected - try constructive first
        write('- Double negation detected -> Trying constructive logic first'), nl,
        ((time(provable_at_level([] > [F2], constructive, Proof1))) ->
            ((time(provable_at_level([] > [F2], minimal, _))) ->
                write('Valid in minimal logic'), nl
            ;
                ( proof_uses_lbot(Proof1) ->
                    write('Valid in intuitionistic logic'), nl
                ;
                    write('Valid in intuitionistic logic'), nl
                )
            )
        ;
            time(provable_at_level([] > [F2], classical, _)),
            write('Valid in classical logic'), nl
        )
    ; is_classical_pattern(F2) ->
        % Classical pattern detected - but still try constructive first!
        write('- Classical pattern detected -> Trying constructive logic first'), nl,
        ((time(provable_at_level([] > [F2], constructive, Proof2))) ->
            ((time(provable_at_level([] > [F2], minimal, _))) ->
                write('Valid in minimal logic'), nl
            ;
                ( proof_uses_lbot(Proof2) ->
                    write('Valid in intuitionistic logic'), nl
                ;
                    write('Valid in intuitionistic logic'), nl
                )
            )
        ;
            time(provable_at_level([] > [F2], classical, _)),
            write('Valid in classical logic'), nl
        )
    ;
        % Normal progression: minimal -> intuitionistic -> classical
        ( time(provable_at_level([] > [F2], minimal, _)) ->
            write('Valid in minimal logic'), nl
        ; time(provable_at_level([] > [F2], constructive, Proof3)) ->
            ( proof_uses_lbot(Proof3) ->
                write('Valid in intuitionistic logic'), nl
            ;
                write('Valid in intuitionistic logic'), nl
            )
        ; time(provable_at_level([] > [F2], classical, _)) ->
            write('Valid in classical logic'), nl
        ;
            write('Failed to prove'), nl, fail
        )
    ),
    !.

% =========================================================================
% BACKWARD COMPATIBILITY ALIAS
% =========================================================================
% decide/1 is kept as an alias for g4mic_decides/1
decide(X) :- g4mic_decides(X).


% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('*****************************************************************'), nl,
    write('*                      G4 PROVER GUIDE                          *'), nl,
    write('*****************************************************************'), nl,
    write('## MAIN COMMANDS '), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  g4mic_decides(Formula).    - says either true or false'), nl,
    write('  decide(Formula).           - alias for g4mic_decides'), nl,
    write('## SYNTAX EXAMPLES '), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('    prove(~ p | p).                   - Excluded Middle (classical)'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('  TPTP:'), nl,
    write('    prove_tptp(fof(test, conjecture, p => p)).'), nl,
    write('    prove_tptp_file(\'myfile.p\').'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS '), nl,
    write('  ~ A , (A & B) , (A | B) , (A => B) , (A <=> B) ,  # , ![x]:A ,  ?[x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    write('  % Conjunction elimination'), nl,
    write('  ?- prove((p & q) => p).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Biconditional'), nl,
    write('  ?- prove(p <=> ~ ~ p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(?[y]:(d(y) => ![x]:d(x))).'), nl,
    nl.
% =========================================================================
% INTERNAL BICONDITIONAL TRANSLATION
% A <=> B becomes (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantifiers: pass recursively into the body
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Propositional connectives
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Base case: atomic formulas
subst_bicond(A, A).

% =========================================================================
% NEGATION SUBSTITUTION (preprocessing)
% =========================================================================
% Double negation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Negation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditional
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Basic case
subst_neg(A, A).
%=================================
% END OF DRIVER
%=================================
