% G4+ : UNIFIED THEOREM PROVER FOR MINIMAL, INTUITIONISTIC AND CLASSICAL LOGIC
% =========================================================================
%%=====================================
% DRIVER
%%====================================
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
%   Minimal -> Intuitionistic -> Classical
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
% Joseph Vidal-Rosset (Universite de Lorraine)
% Built upon: G4 (Roy Dyckhoff), nanoCoP (Jens Otten), leanSeq (Jens Otten)
%
% =========================================================================
% -------------------------------------------------------------------------
% CORE LOGICAL OPERATORS (shared by all)
% -------------------------------------------------------------------------
:- op( 500, fy,  ~).              % negation
:- op(1000, xfy, &).              % conjunction
:- op(1100, xfy, '|').            % disjunction
:- op(1110, xfy, =>).             % implication
:- op(1130, xfy, <=>).            % biconditional (STANDARD: 1130)
:- op( 500, xfy, :).              % quantifier separator
% -------------------------------------------------------------------------
% QUANTIFIERS - Dual syntax (TPTP + internal)
% -------------------------------------------------------------------------
:- op( 500, fy,  !).              % universal (TPTP): ![X]:
:- op( 500, fy,  ?).              % existential (TPTP): ?[X]:
:- op( 500, fy,  all).            % universal (internal): all X:
:- op( 500, fy,  ex).             % existential (internal): ex X:
% -------------------------------------------------------------------------
% EXTENDED TPTP OPERATORS (from nanocop_tptp)
% -------------------------------------------------------------------------
:- op(1130, xfy, <~>).            % negated equivalence
:- op(1110, xfy, <=).             % reverse implication
:- op(1100, xfy, '~|').           % negated disjunction (NOR)
:- op(1000, xfy, ~&).             % negated conjunction (NAND)
% :- op( 400, xfx, =).              % equality
:- op( 300, xf,  !).              % negated equality (for !=)
:- op( 299, fx,  $).              % TPTP constants ($true/$false)
% =========================================================================
% g4mic specific
% =========================================================================
% Input syntax: sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
% :- op(800, xfx, <>).
% =========================================================================
% LATEX OPERATORS (formatted output)
% ATTENTION: Respect spaces exactly!
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % space for quantifiers
:- op(400, fx, ' \\bot ').      % falsity (#)
% LaTeX syntax: sequent turnstile
% :- op(1150, xfx, ' \\vdash ').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% End of operators list
%% File: minimal_driver_equal.pl  -  Version: 7.3 FINAL (time seulement dans proves)

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
% - Rforall first: eigenvariable introduced before any left rules fire
% - L& before L0->: decompose conjunctions before modus ponens
% - L0-> with guard: avoid re-deriving already present formulas
% - L\/-> before branching rules: deterministic simplification first
% - IP just before R->: classical law applied before implication decomposition
% - Lforall after right rules: universal instantiation guided by Skolem terms
% =========================================================================

% =========================================================================
% EIGENVARIABLE REGISTRY (backtrackable global state)
% =========================================================================

init_eigenvars :- b_setval(g4_eigenvars, []).

member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem, !.

% =========================================================================
% RULE 0: AXIOM (separate predicate, not tabled)
% =========================================================================

g4mic_ax(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A \= (_ & _),
    A \= (_ | _),
    A \= (_ => _),
    A \= (! _),
    A \= (? _),
    Delta = [B],
    unify_with_occurs_check(A, B).

% =========================================================================
% g4mic_proves/7
% g4mic_proves(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut,
%              LogicLevel, Proof)
% =========================================================================

% :- table g4mic_proves/7.

% --- Rule 0: Axiom (tested first, non-tabled) ----------------------------
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% =========================================================================
% QUANTIFIER RIGHT RULE (before all left rules)
% Rforall fires first: eigenvariable is immediately available for left rules
% =========================================================================

% --- Rule 1: Rforall -----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves(Gamma > [A1 | D1], FV, Th, J1, SO, LL, P).

% =========================================================================
% PROPOSITIONAL RULES (deterministic, no branching)
% =========================================================================

% --- Rule 2: L& -----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, land(Gamma>Delta, P)) :-
    select((A & B), Gamma, G1), !,
    g4mic_proves([A, B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 3: L0-> (modus ponens on context) -------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, l0cond(Gamma>Delta, P)) :-
    select((A => B), Gamma, G1),
    member(A, G1),
    !,
    g4mic_proves([B | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 4: L&-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, landto(Gamma>Delta, P)) :-
    select(((A & B) => C), Gamma, G1), !,
    g4mic_proves([(A => (B => C)) | G1]>Delta, FV, Th, SI, SO, LL, P).

% --- Rule 6: L\/-> (optimized) --------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lorto(Gamma>Delta, P)) :-
    select(((A | B) => C), Gamma, G1), !,
    ( member(A, G1), member(B, G1) ->
        g4mic_proves([B=>C, A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(A, G1) ->
        g4mic_proves([A=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ; member(B, G1) ->
        g4mic_proves([B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ;
        g4mic_proves([A=>C, B=>C | G1]>Delta, FV, Th, SI, SO, LL, P)
    ).

% =========================================================================
% IMPLICATION RULES
% =========================================================================
% --- Rule 7: L-bot -----------------------------------------------------
g4mic_proves(Gamma>Delta, _, _, SI, SI, LL, lbot(Gamma>Delta, #)) :-
    member(LL, [intuitionistic, classical]),
    member(#, Gamma), !.

% --- Rule 8: IP (indirect proof -- classical only) ------------------------
% Placed just before R->: classical law applied before decomposition
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Th > 0,
    g4mic_proves([(A => #) | Gamma]>[#], FV, Th, SI, SO, classical, P).

% --- Rule 9: R-> ---------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rcond(Gamma>Delta, P)) :-
    Delta = [A => B], !,
    g4mic_proves([A | Gamma]>[B], FV, Th, SI, SO, LL, P).


% =========================================================================
% BRANCHING RULES
% =========================================================================
%% Left rules first
%==========================================================================
% --- Rule 10: L->-> --------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A => B) => C), Gamma, G1),
    \+ (B = #, member(A, G1)),
    !,
    g4mic_proves([A, (B => C) | G1]>[B], FV, Th, SI, J1, LL, P1),
    g4mic_proves([C | G1]>Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 11: L\/ (left disjunction) ---------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, lor(Gamma>Delta, P1, P2)) :-
    select((A | B), Gamma, G1), !,
    g4mic_proves([A | G1]>Delta, FV, Th, SI, J1, LL, P1),
    g4mic_proves([B | G1]>Delta, FV, Th, J1, SO, LL, P2).

% --- Rule 12: R\/ ----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, ror(Gamma>Delta, P)) :-
    Delta = [(A | B)], !,
    (   g4mic_proves(Gamma>[A], FV, Th, SI, SO, LL, P)
    ;   g4mic_proves(Gamma>[B], FV, Th, SI, SO, LL, P)
    ).

% --- Rule 13: R& ----------------------------------------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A & B)], !,
    g4mic_proves(Gamma>[A], FV, Th, SI, J1, LL, P1),
    g4mic_proves(Gamma>[B], FV, Th, J1, SO, LL, P2).

% =========================================================================
% QUANTIFIER  RULES (except Rforall which is above)
% =========================================================================

% --- Rule 14: Lexists ----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(SI, FV):A1, FV)),
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SI, FV), UsedVars),
    b_setval(g4_eigenvars, [f_sk(SI, FV) | UsedVars]),
    J1 is SI + 1,
    g4mic_proves([A1 | G1] > Delta, FV, Th, J1, SO, LL, P).

% --- Rule 15: Lforall (universal instantiation, Otten's limitation) -----------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    length(FV, Len), Len =< Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves([A1 | Gamma] > Delta, [Y | FV], Th, SI, SO, LL, P), !.

% --- Rule 16: Rexists ----------------------------------------------------------
g4mic_proves(Gamma > Delta, FV, Th, SI, SO, LL, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FV, Len), Len < Th,
    copy_term((X:A, FV), (Y:A1, FV)),
    g4mic_proves(Gamma > [A1 | D1], [Y | FV], Th, SI, SO, LL, P), !.

% =========================================================================
% QUANTIFIER CONVERSION RULES
% =========================================================================

% --- Rule 17: CQ_c (classical quantifier shift) ---------------------------
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, classical, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    ( member((?[ZT-YT]:AT) => B, G1),
      \+ \+ ((A => B) = AT) ->
        g4mic_proves([?[ZT-YT]:AT | G1]>Delta, FV, Th, SI, SO, classical, P)
    ;
        g4mic_proves([?[Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, classical, P)
    ).

% --- Rule 18: CQ_m (quantifier conversion, all logics) -------------------
% (?[X]:A => B) -> ![X]:(A => B)
g4mic_proves(Gamma>Delta, FV, Th, SI, SO, LL, cq_m(Gamma>Delta, P)) :-
    select((?[Z-X]:A) => B, Gamma, G1),
    g4mic_proves([![Z-X]:(A => B) | G1]>Delta, FV, Th, SI, SO, LL, P).

% =========================================================================
% HELPER PREDICATES
% =========================================================================

% is_nested_negation(Formula, Target, Depth)
% Checks if Formula = not^Depth(Target)
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

% =========================================================================
% END of Prover
% =========================================================================
%==========================================================================
% LATEX  UTILITIES
%========================================================================
%========================
% Fitch section
% ========================

% =========================================================================
% RENDERING PRIMITIVES
% =========================================================================

% render_hypo/7: Display a hypothesis in Fitch style

render_hypo(Scope, Formula, Label, _CurLine, NextLine, VarIn, VarOut) :-
    with_output_to(atom(LatexLine), (
        render_fitch_indent(Scope),
        write(' \\fh '),
        rewrite(Formula, VarIn, VarOut, LatexFormula),
        write_formula_with_parens(LatexFormula),
        write(' &  '),
        write(Label),
        write('\\\\'), nl
    )),
    write(LatexLine),
    ( integer(NextLine) -> assertz(fitch_line_latex(NextLine, LatexLine)) ; true ).


% render_fitch_indent/1: Genere l'indentation Fitch (\\fa)

render_fitch_indent(0) :- !.

render_fitch_indent(N) :-
    N > 0,
    write('\\fa '),
    N1 is N - 1,
    render_fitch_indent(N1).

render_have(Scope, Formula, Just, _CurLine, NextLine, VarIn, VarOut) :-
    with_output_to(atom(LatexLine), (
        render_fitch_indent(Scope),
        ( Scope = 0 -> write('\\fa ') ; true ),
        rewrite(Formula, VarIn, VarOut, LatexFormula),
        write_formula_with_parens(LatexFormula),
        write(' &  '),
        write(Just),
        write('\\\\'), nl
    )),
    write(LatexLine),
    ( integer(NextLine) -> assertz(fitch_line_latex(NextLine, LatexLine)) ; true ).

% =========================================================================
% SIMPLE RULE: (Antecedent) => (Consequent) except for atoms
% =========================================================================

% Test if a formula is atomic
is_atomic_formula(Formula) :-
    atomic(Formula).

% -------------------------------------------------------------------------
% NEW: Test if a formula is a negation (in LaTeX display sense)
% A negative formula is represented as (' \\lnot ' X) par rewrite/4.
% We want to consider any formula starting with ' \\lnot ' as
% "non-parenthesable" - i.e. ne PAS entourer par des parentheses externe.
% -------------------------------------------------------------------------
is_negative_formula((' \\lnot ' _)) :- !.

% Helper: treat negative formulas as "atomic-like" for parentheses suppression
is_atomic_or_negative_formula(F) :-
    is_atomic_formula(F) ;
    is_negative_formula(F).

% =========================================================================
% TEST IF QUANTIFIER BODY NEEDS PARENTHESES
% =========================================================================

quantifier_body_needs_parens((_ ' \\to ' _)) :- !.
quantifier_body_needs_parens((_ ' \\land ' _)) :- !.
quantifier_body_needs_parens((_ ' \\lor ' _)) :- !.
quantifier_body_needs_parens((_ ' \\leftrightarrow ' _)) :- !.
quantifier_body_needs_parens(_) :- fail.

% =========================================================================
% ALL write_formula_with_parens/1 CLAUSES GROUPED
% =========================================================================

% Writing an implication with smart parentheses
write_formula_with_parens((A ' \\to ' B)) :-
    !,
    write_implication_with_parens(A, B).

write_formula_with_parens('='(A, B)) :- !,
    write('('), write_formula_with_parens(A), write(' = '), write_formula_with_parens(B), write(')').

% Autres operateurs
write_formula_with_parens((A ' \\lor ' B)) :-
    !,
    write_with_context(A, 'lor_left'),
    write(' \\lor '),
    write_with_context(B, 'lor_right').

write_formula_with_parens((A ' \\land ' B)) :-
    !,
    write_with_context(A, 'land_left'),
    write(' \\land '),
    write_with_context(B, 'land_right').

write_formula_with_parens((A ' \\leftrightarrow ' B)) :-
    !,
    write_bicond_component(A),
    write(' \\leftrightarrow '),
    write_bicond_component(B).

write_formula_with_parens((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    write_with_context(A, 'not').

% QUANTIFIERS WITH SMART PARENTHESES
write_formula_with_parens((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens(Other) :-
    write(Other).

% =========================================================================
% HELPER PREDICATES FOR BICONDITIONAL FORMATTING
% =========================================================================

% Helper: write biconditional component with parens if not a literal
write_bicond_component(A) :-
    is_latex_literal(A), !,
    write_formula_with_parens(A).
write_bicond_component(A ' \\to ' B) :- !,
    % Implications need parentheses in biconditional context
    write('('),
    write_implication_with_parens(A, B),
    write(')').
write_bicond_component(A) :-
    % Any other complex formula gets parentheses
    write('('),
    write_formula_with_parens(A),
    write(')').

% Check if a LaTeX formula is a literal (atom, negated atom, or predicate application)
is_latex_literal(A) :-
    atomic(A), !.
is_latex_literal((' \\lnot ' A)) :-
    atomic(A), !.
is_latex_literal((' \\lnot ' (' \\lnot ' A))) :-
    % Double negation of literal is still considered "atomic-like"
    is_latex_literal(A), !.
is_latex_literal(A) :-
    compound(A),
    A \= (_ ' \\to ' _),
    A \= (_ ' \\land ' _),
    A \= (_ ' \\lor ' _),
    A \= (_ ' \\leftrightarrow ' _),
    A \= (' \\lnot ' _),
    !.

% =========================================================================
% SPECIALIZED FUNCTION FOR IMPLICATIONS
% =========================================================================

write_implication_with_parens(Antecedent, Consequent) :-
    % Antecedent: do not parenthesize if atomic OR negative formula
    ( is_atomic_or_negative_formula(Antecedent) ->
        write_formula_with_parens(Antecedent)
    ;
        write('('),
        write_formula_with_parens(Antecedent),
        write(')')
    ),
    write(' \\to '),
    % Consequent: parenthesize except if atomic OR negative formula
    % NOTE: we consider any form (' \\lnot ' _) as "negative" even if
    % it contains several nested negations (~  ~ ~  A).
    ( is_atomic_or_negative_formula(Consequent) ->
        write_formula_with_parens(Consequent)
    ;
        write('('),
        write_formula_with_parens(Consequent),
        write(')')
    ).

% =========================================================================
% ALL write_with_context/2 CLAUSES GROUPED
% =========================================================================

% IMPLICATIONS in all contexts - use write_implication_with_parens
write_with_context((A ' \\to ' B), 'lor_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'lor_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'not') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

% CONJUNCTIONS in disjunctions
write_with_context((A ' \\land ' B), 'lor_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\land ' B), 'lor_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% CONJUNCTIONS in negations
write_with_context((A ' \\land ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% DISJUNCTIONS in negations
write_with_context((A ' \\lor ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% DISJUNCTIONS in conjunctions
write_with_context((A ' \\lor ' B), 'land_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\lor ' B), 'land_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% BICONDITIONALS in negations
write_with_context((A ' \\leftrightarrow ' B), 'not') :-
    !,
    write('('),
    write_bicond_component(A),
    write(' \\leftrightarrow '),
    write_bicond_component(B),
    write(')').

% FALLBACK CLAUSE
write_with_context(Formula, _Context) :-
    write_formula_with_parens(Formula).

% =========================================================================
% ADAPTED  SYSTEM: direct rewrite on formulas with standard operators
% VERSION WITH ELEGANT PREDICATE SIMPLIFICATION
% =========================================================================

% rewrite/4 - Adapted version that handles formulas directly
rewrite(#, J, J, '\\bot') :- !.
rewrite(# => #, J, J, '\\top') :- !.

% NEW CLAUSE TO HANDLE SKOLEM CONSTANTS
% Converts f_sk(K) to a simple name like 'a', 'b', etc. (single argument version)
rewrite(f_sk(K), J, J, Name) :-
    integer(K),
    !,
    constant_name(K, Name).

% Converts f_sk(K,_) to a simple name like 'a', 'b', etc. (two arguments version)
rewrite(f_sk(K,_), J, J, Name) :-
    !,
    constant_name(K, Name).

% BASE CASE: atomic formulas
rewrite(A, J, J, A_latex) :-
    atomic(A),
    !,
    toggle(A, A_latex).

% Recognizes ((A => B) & (B => A)) (or reverse order) as A <=> B for LaTeX display
% Must be placed BEFORE the generic rewrite((A & B), ...) clause
rewrite((X & Y), J, K, (C ' \\leftrightarrow ' D)) :-
    % case 1: X = (A => B), Y = (B => A)
    ( X = (A => B), Y = (B => A)
    % case 2: reverse order
    ; X = (B => A), Y = (A => B)
    ),
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Conjunction with standard operator &
rewrite((A & B), J, K, (C ' \\land ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Disjunction with standard operator |
rewrite((A | B), J, K, (C ' \\lor ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% COSMETIC DISPLAY: A => # becomes ~A
rewrite((A => #), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% Implication with standard operator =>
rewrite((A => B), J, K, (C ' \\to ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Biconditional with standard operator <=>
rewrite((A <=> B), J, K, (C ' \\leftrightarrow ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Negation with standard operator ~
rewrite((~A), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% QUANTIFIERS WITH ASQ ANNOTATIONS: strip asq(...) and use variable name
% CRITICAL: Replace only the SPECIFIC asq term, not all asq terms
rewrite((![X-asq(A,B)]:Body), J, K, (' \\forall ' X ' ' C)) :-
    !,
    replace_specific_asq(asq(A,B), X, Body, CleanBody),
    rewrite(CleanBody, J, K, C).

rewrite((?[X-asq(A,B)]:Body), J, K, (' \\exists ' X ' ' C)) :-
    !,
    replace_specific_asq(asq(A,B), X, Body, CleanBody),
    rewrite(CleanBody, J, K, C).

% QUANTIFIERS: X-Y format - generate x, y, z based on counter
rewrite((![_-_]:A), J, K, (' \\forall ' VarName ' ' C)) :-
    !,
    xyz_name(J, VarName),  % Generate x, y, z, x0, y0...
    J1 is J + 1,
    rewrite(A, J1, K, C).

rewrite((?[_-_]:A), J, K, (' \\exists ' VarName ' ' C)) :-
    !,
    xyz_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).

% QUANTIFIERS: Simple X format - generate x, y, z based on counter
rewrite((![_]:A), J, K, (' \\forall ' VarName ' ' C)) :-
    !,
    xyz_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).

rewrite((?[_]:A), J, K, (' \\exists ' VarName ' ' C)) :-
    !,
    xyz_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).
% =========================================================================
% ELEGANT PREDICATE SIMPLIFICATION
% P(x,y,z) -> Pxyz for all predicates
% =========================================================================
% --- Replace the previous "concatenate predicate name and args" clause by this safer version.
% We avoid applying this cosmetic concatenation to equality and other logical operators.
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    % Do NOT collapse standard logical operators or equality into a single atom:
    % exclude '=' and the main logical connectives (=>, <=>, &, |, ~)
    \+ member(F, ['=', '=>', '<=>', '&', '|', '~']),
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).

% PREDICATES AND TERMS (general clause)
rewrite(X, J, K, Y) :-
    X =.. [F|L],
    toggle(F, G),
    rewrite_list(L, J, K, R),
    Y =.. [G|R].


% =========================================================================
% AUXILIARY PREDICATES FOR SIMPLIFICATION
% =========================================================================

all_simple_terms([]).
all_simple_terms([H|T]) :-
    simple_term(H),
    all_simple_terms(T).

% A simple term is ONLY: atomic, variable, or internal Skolem function
% User functions like f(a), g(x,y) are NOT simple terms
simple_term(X) :-
    atomic(X), !.
simple_term(X) :-
    var(X), !.
simple_term(f_sk(_)) :-
    !.
simple_term(f_sk(_,_)) :-
    !.
% No other compound terms are simple - this prevents simplification of user functions

rewrite_args_list([], J, J, []).
rewrite_args_list([H|T], J, K, [RH|RT]) :-
    rewrite_term(H, J, TempJ, RH),
    rewrite_args_list(T, TempJ, K, RT).

concatenate_all([X], X) :-
    atomic(X), !.
concatenate_all([H|T], Result) :-
    length([H|T], Len),
    Len =< 5,
    !,
    concatenate_all_impl([H|T], Result).
concatenate_all(_, _) :-
    fail.

concatenate_all_impl([X], X) :-
    atomic(X), !.
concatenate_all_impl([X], Result) :-
    % Handle compound terms: flatten them
    compound(X),
    !,
    flatten_term(X, Flattened),
    concatenate_all_impl(Flattened, Result).
concatenate_all_impl([H|T], Result) :-
    atomic(H),
    !,
    concatenate_all_impl(T, TempResult),
    atom_concat(H, TempResult, Result).
concatenate_all_impl([H|T], Result) :-
    % Handle compound terms in list
    compound(H),
    !,
    flatten_term(H, Flattened),
    append(Flattened, T, NewList),
    concatenate_all_impl(NewList, Result).

% Helper: flatten a compound term into a list of atoms
flatten_term(Term, [Atom]) :-
    atomic(Term),
    !,
    term_to_atom(Term, Atom).
flatten_term(Term, Flattened) :-
    compound(Term),
    Term =.. [Functor|Args],
    atom(Functor),
    maplist(flatten_term, Args, ArgLists),
    append(ArgLists, Flattened).
flatten_term(Var, ['_']) :-
    var(Var).

% =========================================================================
% LIST AND TERM PROCESSING
% =========================================================================

rewrite_list([], J, J, []).
rewrite_list([X|L], J, K, [Y|R]) :-
    rewrite_term(X, J, H, Y),
    rewrite_list(L, H, K, R).

rewrite_term(V, J, K, V) :-
    var(V),
    !,
    constant_name(J, V),
    K is J+1.

rewrite_term(f_sk(K), J, J, N) :-
    integer(K),
    !,
    constant_name(K, N).

rewrite_term(f_sk(K,_), J, J, N) :-
    !,
    constant_name(K, N).

% NEW: If the term is a simple atom (constant), DO NOT capitalize it
% Because it is an argument of a predicate/function
rewrite_term(X, J, J, X) :-
    atomic(X),
    !.

rewrite_term(X, J, K, Y) :-
    X =.. [F|L],
    rewrite_list(L, J, K, R),
    Y =.. [F|R].

% Generateur de noms elegants pour variables liees
% Use x, y, z instead of a, b, c to avoid collision with constants
rewrite_name(K, N) :-
    K < 3,
    !,
    J is K+0'x,  % Generates x, y, z
    char_code(N, J).

rewrite_name(K, N) :-
    J is (K mod 3)+0'x,  % For K >= 3, generates x0, y0, z0, x1, y1, z1...
    H is K div 3,
    number_codes(H, L),
    atom_codes(N, [J|L]).

% =========================================================================
% CONSTANT NAME GENERATOR
% For instantiation terms (eigenvariables and gamma-rule witnesses)
% Generates a, b, c, d, ..., w, a1, b1, c1, ... (skipping x, y, z)
% =========================================================================
constant_name(K, N) :-
    Index is K mod 23,
    Suffix is K div 23,
    Code is Index + 0'a,
    char_code(Base, Code),
    (   Suffix =:= 0 ->
        N = Base
    ;   atom_concat(Base, Suffix, N)
    ).

% Toggle majuscules/minuscules
toggle(X, Y) :-
    atom_codes(X, L),
    toggle_list(L, R),
    atom_codes(Y, R).

toggle_list([], []).
toggle_list([X|L], [Y|R]) :-
    toggle_code(X, Y),
    toggle_list(L, R).

toggle_code(X, Y) :-
    0'a =< X, X =< 0'z,
    !,
    Y is X - 0'a + 0'A.

toggle_code(X, Y) :-
    0'A =< X, X =< 0'Z,
    !,
    Y is X - 0'A + 0'a.

toggle_code(X, X).

% =========================================================================
% SYSTEME PREPARE
% =========================================================================

prepare_premisses_list([], []) :- !.
prepare_premisses_list([H|T], [PreparedH|PreparedT]) :-
    prepare(H, [], PreparedH),
    prepare_premisses_list(T, PreparedT).

prepare(#, _, #) :- !.

prepare((A & B), Q, (C & D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A | B), Q, (C | D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A => B), Q, (C => D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A <=> B), Q, (C <=> D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((~A), Q, (~C)) :-
    !,
    prepare(A, Q, C).

prepare((![Z]:A), Q, (![Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare((?[Z]:A), Q, (?[Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare(X, _, X) :-
    var(X),
    !.

prepare(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_term(X, _, X) :-
    var(X),
    !.

prepare_term(X, Q, Y) :-
    atom(X),
    member(X-Y, Q),
    !.

prepare_term(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_list([], _, []).
prepare_list([X|L], Q, [Y|R]) :-
    prepare_term(X, Q, Y),
    prepare_list(L, Q, R).

% =========================================================================
% RENDER LATEX FORMULA - Unified with write_formula_with_parens
% =========================================================================
% =========================================================================
% ASQ REPLACEMENT HELPER
% =========================================================================
% Replace SPECIFIC asq(A,B) term (not all asq terms) with variable X in formulas
% Used when rendering quantifiers with asq annotations

% Match the EXACT asq term (using unification with ==)
replace_specific_asq(AsqTerm, Var, Term, Var) :-
    Term == AsqTerm, !.

% For compound terms, recurse but skip quantifier structures
replace_specific_asq(AsqTerm, Var, Term, Result) :-
    compound(Term),
    Term \= ![_|_],
    Term \= ?[_|_],
    !,
    Term =.. [F|Args],
    maplist(replace_specific_asq(AsqTerm, Var), Args, NewArgs),
    Result =.. [F|NewArgs].

% Atoms and variables pass through
replace_specific_asq(_, _, Term, Term).

% =========================================================================
% END OF LATEX UTILITIES FILE
% =========================================================================
% =========================================================================
% VARIOUS DETECTIONS (Logic level detection, equality, etc. )
% =========================================================================

:- dynamic formula_level/1.

% =========================================================================
% MAIN DETECTION
% =========================================================================

detect_and_set_logic_level(Formula) :-
    retractall(formula_level(_)),
    ( is_fol_formula(Formula) ->
        assertz(formula_level(fol))
    ;
        assertz(formula_level(propositional))
    ).

% =========================================================================
% FOL DETECTION HEURISTICS
% A formula is FOL if it contains:
% - Quantifiers (!, ?)
% - Predicate applications p(t1,...,tn) with n > 0
% - Equalities between terms
% - Skolem functions
% =========================================================================

is_fol_formula(Formula) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.

% =========================================================================
% DETECTION DES COMPOSANTS
% =========================================================================

% Quantificateurs
contains_quantifier(![_-_]:_) :- !.
contains_quantifier(?[_-_]:_) :- !.
contains_quantifier(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_quantifier(Arg).


% Predicate applications (compound terms that are not connectives)
contains_predicate_application(Term) :-
    compound(Term),
    \+ is_logical_connective_structure(Term),
    Term =.. [_F|Args],
    Args \= [],  % Must have at least one argument
    !.
contains_predicate_application(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_predicate_application(Arg).

% Logical connective structures (to exclude)
is_logical_connective_structure(_ => _).
is_logical_connective_structure(_ & _).
is_logical_connective_structure(_ | _).
is_logical_connective_structure(_ <=> _).
is_logical_connective_structure(_ = _).  % Equality treated separately
is_logical_connective_structure(~ _).
is_logical_connective_structure(#).
is_logical_connective_structure(![_-_]:_).
is_logical_connective_structure(?[_-_]:_).

% Equality
contains_equality(_ = _) :- !.
contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_equality(Arg).

% Detect USER function symbols (not internal f_sk Skolem functions)
% A user function is a compound term with arguments that is not:
%   - A logical connective
%   - A quantifier
%   - An internal Skolem function (f_sk)
%   - A predicate at top level
contains_user_function(Term) :-
    compound(Term),
    Term \= f_sk(_),
    Term \= f_sk(_,_),
    Term \= (_ = _),
    Term \= (~ _),
    Term \= (_ & _),
    Term \= (_ | _),
    Term \= (_ => _),
    Term \= (_ <=> _),
    Term \= (![_]:_),
    Term \= (?[_]:_),
    % Now check if Term or its arguments contain functions
    (   has_function_in_args(Term)
    ;   Term =.. [_F|Args],
        Args \= [],
        member(Arg, Args),
        contains_user_function(Arg)
    ).

% Check if a term has function symbols in its arguments
% This handles cases like p(f(x)) where f(x) is a function inside predicate p
has_function_in_args(Term) :-
    compound(Term),
    Term =.. [_Pred|Args],
    Args \= [],
    member(Arg, Args),
    is_user_function_term(Arg).

% Check if a term itself is a function (not a predicate at top level)
is_user_function_term(Term) :-
    compound(Term),
    Term \= f_sk(_),
    Term \= f_sk(_,_),
    Term \= (_ = _),
    Term \= (~ _),
    Term \= (_ & _),
    Term \= (_ | _),
    Term \= (_ => _),
    Term \= (_ <=> _),
    Term \= (![_]:_),
    Term \= (?[_]:_),
    Term =.. [_F|Args],
    Args \= [].

% Keep old name for backward compatibility (Skolem functions only)
contains_function_symbol(f_sk(_)) :- !.
contains_function_symbol(f_sk(_,_)) :- !.
contains_function_symbol(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_function_symbol(Arg).

% =========================================================================
% FORMULA EXTRACTION FROM A G4 PROOF
% =========================================================================

extract_formula_from_proof(Proof, Formula) :-
    Proof =.. [_RuleName, Sequent|_],
    ( Sequent = (_ > [Formula]) ->
        true
    ; Sequent = (_ > Goals), Goals = [Formula|_] ->
        true
    ;
        Formula = unknown
    ).
% =========================================================================
% VALIDATION & WARNINGS MODULE
% Detection of typing errors and misuse of logical operators
% =========================================================================
% This module validates formulas before proof attempt and warns about
% common mistakes, particularly the confusion between:
%   <=>  biconditional (propositional connective between formulas)
%   =    equality (relation between terms in FOL)
% =========================================================================


:- use_module(library(lists)).

% =========================================================================
% VALIDATION MODE CONFIGURATION
% =========================================================================
% Modes:
%   permissive - warn but continue (default)
%   strict     - reject invalid formulas automatically
%   silent     - no warnings

:- dynamic validation_mode/1.
validation_mode(permissive).

% =========================================================================
% KNOWN PREDICATES REGISTRY
% =========================================================================
% Users can register predicate symbols to improve detection accuracy

:- dynamic known_predicate/1.

% Default predicates (common in logic examples)
known_predicate(p).
known_predicate(q).
known_predicate(r).
known_predicate(s).
known_predicate(h).
known_predicate(m).

clear_predicates :-
    retractall(known_predicate(_)).

% =========================================================================
% MAIN VALIDATION ENTRY POINT
% =========================================================================

validate_and_warn(Formula, ValidatedFormula) :-
    validation_mode(Mode),

    % Check 1: Sequent syntax confusion (ALWAYS check, even in propositional logic)
    check_sequent_syntax_confusion(Formula, SyntaxWarnings),

    % Check 2: Biconditional misuse (only in FOL context)
/*
    detect_fol_context(Formula, IsFOL),
    (   IsFOL ->
        check_bicond_misuse(Formula, BicondWarnings)
    ;   BicondWarnings = []
    ),
*/
    % Combine warnings
    append(SyntaxWarnings, _BicondWarnings, AllWarnings),

    % Handle combined warnings
    handle_warnings(AllWarnings, Mode, ValidatedFormula, Formula).

% Handle warnings according to mode
handle_warnings([], _, Formula, Formula) :- !.
handle_warnings(_Warnings, silent, Formula, Formula) :- !.
handle_warnings(Warnings, permissive, Formula, Formula) :-
    report_warnings(Warnings),
    prompt_continue.
handle_warnings(Warnings, strict, _, _) :-
    report_warnings(Warnings),
    write('  Validation failed (strict mode). Formula rejected.'), nl,
    fail.

% Prompt user to continue
prompt_continue :-
    write('Continue despite warnings? (y/n): '),
    read(Response),
    (   Response = y -> true
    ;   Response = yes -> true
    ;   write('  Proof attempt cancelled.'), nl, fail
    ).
% =========================================================================
% FOL CONTEXT DETECTION
% =========================================================================
% A formula is in FOL context if it contains:
%   - Quantifiers (?, ?)
%   - Predicate applications p(t1,...,tn) with n > 0
%   - Equality between terms
%   - Function symbols (including Skolem functions)

detect_fol_context(Formula, true) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.
detect_fol_context(_, false).

% Logical connective identification
is_logical_connective(_ => _).
is_logical_connective(_ & _).
is_logical_connective(_ | _).
is_logical_connective(_ <=> _).
is_logical_connective(~ _).
is_logical_connective(#).
is_logical_connective(![_-_]:_).
is_logical_connective(?[_-_]:_).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION
% =========================================================================
% Detects <=> used between terms instead of formulas
% Example: (a <=> b) should likely be (a = b) in FOL

check_bicond_misuse(Formula, Warnings) :-
    findall(Warning, detect_bicond_in_terms(Formula, Warning), Warnings).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION (IMPROVED)
% =========================================================================
% Only warn if <=> appears in a TERM CONTEXT (not formula context)

detect_bicond_in_terms(A <=> B, warning(bicond_between_terms, A, B)) :-
    % Both sides are clearly terms (constants or function applications)
    is_definitely_term(A),
    is_definitely_term(B),
    !.

detect_bicond_in_terms(Term, Warning) :-
    compound(Term),
    Term \= (_ <=> _),  % Don't recurse into biconditionals we already checked
    Term =.. [_|Args],
    member(Arg, Args),
    detect_bicond_in_terms(Arg, Warning).

% =========================================================================
% DEFINITELY A TERM (not a formula)
% =========================================================================
% Conservative: only flag obvious cases
is_definitely_term(![_]:_) :- !, fail.  % Universal quantification = formula
is_definitely_term(?[_]:_) :- !, fail.  % Existential quantification = formula

is_definitely_term(X) :-
    var(X), !.  % Variable (term)

is_definitely_term(X) :-
    atomic(X),
    \+ known_predicate(X),  % Constant, not predicate
    !.

is_definitely_term(f_sk(_)) :- !.  % Skolem function (single arg)
is_definitely_term(f_sk(_,_)) :- !.  % Skolem function

is_definitely_term(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    % Must be a KNOWN function symbol (not predicate)
    is_known_function(F),
    !.

% =========================================================================
% KNOWN FUNCTION REGISTRY
% =========================================================================
% Users can register function symbols to improve detection

:- dynamic known_function/1.

% Default common function symbols
known_function(succ).   % Successor
known_function(plus).
known_function(times).
known_function(father).  % father(x) is a term
known_function(mother).

is_known_function(F) :-
    known_function(F), !.

% Heuristic fallback: if NOT a known predicate, assume function
% (This is conservative - avoid false positives)
is_known_function(F) :-
    \+ known_predicate(F),
    \+ member(F, [f, g, h, i, j, k, p, q, r, s]),  % Ambiguous symbols
    !.

% =========================================================================
% SEQUENT SYNTAX CONFUSION DETECTION
% =========================================================================
% Detects common mistakes:
%   [P] => [Q]  (WRONG - looks like sequent but uses =>)
%   P > Q       (WRONG - looks like implication but uses >)

check_sequent_syntax_confusion(Formula, Warnings) :-
    findall(Warning, detect_sequent_confusion(Formula, Warning), Warnings).

% Case 1: [List] => [List] - user probably meant sequent syntax
detect_sequent_confusion([_|_] => [_|_], warning(list_implication, 'Use > for sequents, not =>')) :- !.
detect_sequent_confusion([_|_] => _, warning(list_implication_left, 'Left side is a list - use > for sequents')) :- !.
detect_sequent_confusion(_ => [_|_], warning(list_implication_right, 'Right side is a list - use > for sequents')) :- !.

% Case 2: Atom > Atom - user probably meant implication
detect_sequent_confusion(A > B, warning(atom_turnstile, 'Use => for implication, not >')) :-
    atomic(A),
    atomic(B),
    !.

% Case 3: Complex formula > Complex formula - likely implication
detect_sequent_confusion(A > B, warning(formula_turnstile, 'Use => for implication between formulas, not >')) :-
    is_formula(A),
    is_formula(B),
    !.

% Recursive search
detect_sequent_confusion(Term, Warning) :-
    compound(Term),
    Term \= (_ => _),  % Don't recurse into implications
    Term \= (_ > _),   % Don't recurse into turnstiles
    Term =.. [_|Args],
    member(Arg, Args),
    detect_sequent_confusion(Arg, Warning).

% Helper: check if something is a formula (not a list or term)
is_formula(Term) :-
    compound(Term),
    (   is_logical_connective(Term)
    ;   Term =.. [F|Args], Args \= [], known_predicate(F)
    ).

% Term identification (not a formula)
% A term is: constant, variable, or function application
is_term_not_formula(X) :-
    atomic(X), !.  % Constant or variable
is_term_not_formula(f_sk(_)) :- !.  % Skolem function (single arg)
is_term_not_formula(f_sk(_,_)) :- !.  % Skolem function
is_term_not_formula(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    \+ known_predicate(F),  % Function, not predicate
    !.

% =========================================================================
% WARNING REPORTS
% =========================================================================

report_warnings([]) :- !.
report_warnings(Warnings) :-
    length(Warnings, N),
    nl,
    format('  ~d warning(s) detected:~n', [N]),
    nl,
    maplist(print_warning, Warnings),
    nl,
    write('  Tips:'), nl,
    write('   o Theorems:  prove(p => q).        % implication'), nl,
    write('   o Sequents:  prove([p] > [q]).     % turnstile ?'), nl,
    write('   o FOL:       use = for equality, <=> for biconditional'), nl,
    nl.

print_warning(warning(bicond_between_terms, A, B)) :-
    format('  warning: (~w <=> ~w): biconditional between terms detected.~n', [A, B]),
    format('      -> Did you mean (~w = ~w)?~n', [A, B]).

% NEW: Sequent syntax warnings
print_warning(warning(list_implication, Msg)) :-
    format('  syntax warning: ~w~n', [Msg]),
    write('      Example: prove([p, q] > [p & q]).  % CORRECT'), nl,
    write('               prove([p, q] => [p & q]). % WRONG'), nl.

print_warning(warning(list_implication_left, Msg)) :-
    format('  syntax warning: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(list_implication_right, Msg)) :-
    format('  syntax warning: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(atom_turnstile, Msg)) :-
    format('  syntax warning: ~w~n', [Msg]),
    write('      Example: prove(p => q).       % CORRECT (implication)'), nl,
    write('               prove(p > q).        % WRONG'), nl,
    write('               prove([p] > [q]).    % CORRECT (sequent)'), nl.

print_warning(warning(formula_turnstile, Msg)) :-
    format('  syntax warning: ~w~n', [Msg]),
    write('      -> Use => for implications, > only for sequents'), nl,
    write('      -> Sequent syntax: [Premisses] > [Conclusions]'), nl.



% =========================================================================
% HELPER: DETECTION OF EQUALITY AND FUNCTIONS
% =========================================================================

% Main predicate: decide if formula needs nanoCoP
% (due to equality or user-defined function symbols)
g4mic_needs_nanocop(Formula) :-
    (   g4mic_contains_equality_direct(Formula)
    ;   contains_user_function(Formula)
    ), !.

% Equality detection (only descends through logical connectives)
g4mic_contains_equality_direct(_ = _) :- !.
g4mic_contains_equality_direct(~A) :- !, g4mic_contains_equality_direct(A).
g4mic_contains_equality_direct(A & B) :- !, (g4mic_contains_equality_direct(A) ; g4mic_contains_equality_direct(B)).
g4mic_contains_equality_direct(A | B) :- !, (g4mic_contains_equality_direct(A) ; g4mic_contains_equality_direct(B)).
g4mic_contains_equality_direct(A => B) :- !, (g4mic_contains_equality_direct(A) ; g4mic_contains_equality_direct(B)).
g4mic_contains_equality_direct(A <=> B) :- !, (g4mic_contains_equality_direct(A) ; g4mic_contains_equality_direct(B)).
g4mic_contains_equality_direct(![_]: A) :- !, g4mic_contains_equality_direct(A).
g4mic_contains_equality_direct(?[_]:A) :- !, g4mic_contains_equality_direct(A).
% No recursive descent into arbitrary compound terms - only through logical operators
g4mic_contains_equality_direct(_) :- fail.


%=========================================================================
% END OF DETECTIONS
%=========================================================================
% =========================================================================
% G4 PRINTER SPECIALIZED FOR BUSSPROOFS
% Optimized LaTeX rendering for  G4 rules
% =========================================================================

% =========================================================================
% G4 rules
% =========================================================================

% 1. Ax.
render_bussproofs(ax(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$Ax.$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% 2. L0-implies
render_bussproofs(l0cond(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L0\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 3. L-and-implies
render_bussproofs(landto(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\land\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% TNE
render_bussproofs(tne(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 4. L-or-implies
render_bussproofs(lorto(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\lor\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% L-exists-or
render_bussproofs(lex_lor(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\exists\\lor$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 5. L-and
render_bussproofs(land(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\land$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 6. L-or
render_bussproofs(lor(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\lor$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 7. R-implies
render_bussproofs(rcond(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 8. R-or
render_bussproofs(ror(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\lor$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 9. L-implies-implies
render_bussproofs(ltoto(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\to\\to$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 10. R-and
render_bussproofs(rand(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$R\\land$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 11. L-bot
render_bussproofs(lbot(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$L\\bot$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% IP : Indirect proof (with DNE_m detection)
render_bussproofs(ip(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    Seq = (_ > [Goal]),
    render_bussproofs(Proof, VarCounter, TempCounter),
    ( Goal = (_ => #) ->
        write('\\RightLabel{\\scriptsize{$DNE_{m}$}}'), nl
    ;
        write('\\RightLabel{\\scriptsize{$IP$}}'), nl
    ),
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
%  FOL QUANTIFICATION RULES
% =========================================================================

% 12. R-forall
render_bussproofs(rall(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\forall$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 13. L-exists
render_bussproofs(lex(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\exists$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 14. R-exists
render_bussproofs(rex(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\exists$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 15. L-forall
render_bussproofs(lall(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\forall$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_c : Classical conversion rule
render_bussproofs(cq_c(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$CQ_{c}$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_m : Minimal conversion rule
render_bussproofs(cq_m(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$CQ_{m}$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% SEQUENT RENDERING
% =========================================================================

% Filter and render sequent
render_sequent(Gamma > Delta, VarCounter, FinalCounter) :-
    % ALWAYS use Gamma from sequent, NOT premiss_list!
    filter_top_from_gamma(Gamma, FilteredGamma0),
    filter_empty_lists(FilteredGamma0, FilteredGamma),

    ( FilteredGamma = [] ->
        % Theorem: no premisses to display
        write(' \\vdash '),
        TempCounter = VarCounter
    ;
        % Sequent with premisses
        render_formula_list(FilteredGamma, VarCounter, TempCounter),
        write(' \\vdash ')
    ),

    filter_empty_lists(Delta, FilteredDelta),
    ( FilteredDelta = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(FilteredDelta, TempCounter, FinalCounter)
    ).

% filter_empty_lists/2: Remove empty list [] elements
filter_empty_lists([], []).
filter_empty_lists([[]|T], Filtered) :- !, filter_empty_lists(T, Filtered).
filter_empty_lists([H|T], [H|RestFiltered]) :- filter_empty_lists(T, RestFiltered).

% filter_top_from_gamma/2: Remove top (T) from premisses list
filter_top_from_gamma([], []).
filter_top_from_gamma([H|T], Filtered) :-
    ( is_top_formula(H) ->
        filter_top_from_gamma(T, Filtered)
    ;
        filter_top_from_gamma(T, RestFiltered),
        Filtered = [H|RestFiltered]
    ).

% is_top_formula/1: Detect if a formula is top (T)
% Top is represented as (# => #) or sometimes ~ #
is_top_formula((# => #)) :- !.
is_top_formula(((# => #) => #) => #) :- !.  % Double negation of top
is_top_formula(_) :- fail.

% =========================================================================
% FORMULA LIST RENDERING
% =========================================================================

% Empty list
render_formula_list([], VarCounter, VarCounter) :- !.

% Single formula
render_formula_list([F], VarCounter, FinalCounter) :-
    !,
    rewrite(F, VarCounter, FinalCounter, F_latex),
    write_formula_with_parens(F_latex).

% List of formulas with commas
render_formula_list([F|Rest], VarCounter, FinalCounter) :-
    rewrite(F, VarCounter, TempCounter, F_latex),
    write(F_latex),
    write(', '),
    render_formula_list(Rest, TempCounter, FinalCounter).

% =========================================================================
% INTEGRATION WITH MAIN SYSTEM
% =========================================================================

% =========================================================================
% COMMENTS AND DOCUMENTATION
% =========================================================================

% This G4 printer is specially optimized for:
%
% 1. AUTHENTIC G4 RULES:
%    - L0-> (modus ponens G4 signature)
%    - L-and->, L-or-> (curried transformations)
%    - L->-> (special G4 rule)
%    - Exact order from multiprover.pl
%
% 2. MULTI-FORMAT COMPATIBILITY:
%    - Uses rewrite/4 system from latex_utilities.pl
%    - Compatible with FOL quantifiers
%    - Handles anti-sequents for failures
%
% 3. PROFESSIONAL LATEX RENDERING:
%    - Standard bussproofs.sty
%    - Compact and clear labels
%    - Automatic variable counter management
%
% USAGE:
% ?- decide(Formula).  % Automatically uses this printer
% ?- render_g4_proof(Proof).  % Direct proof rendering

% =========================================================================
% END OF G4 PRINTER
% =========================================================================
%========================================================================
% COMMON ND PRINTING
%========================================================================
% =========================================================================
% CYCLIC TERMS HANDLING
% =========================================================================
make_acyclic_term(Term, Safe) :-
    catch(
        make_acyclic_term(Term, [], _MapOut, Safe),
        _,
        Safe = cyc(Term)
    ).

make_acyclic_term(Term, MapIn, MapOut, Safe) :-
    ( var(Term) ->
        Safe = Term, MapOut = MapIn
    ; atomic(Term) ->
        Safe = Term, MapOut = MapIn
    ; find_pair(Term, MapIn, Value) ->
        Safe = Value, MapOut = MapIn
    ;
        gensym(cyc, Patom),
        Placeholder = cyc(Patom),
        MapMid = [pair(Term, Placeholder)|MapIn],
        Term =.. [F|Args],
        make_acyclic_args(Args, MapMid, MapAfterArgs, SafeArgs),
        SafeTermBuilt =.. [F|SafeArgs],
        replace_pair(Term, Placeholder, SafeTermBuilt, MapAfterArgs, MapOut),
        Safe = SafeTermBuilt
    ).

make_acyclic_args([], Map, Map, []).
make_acyclic_args([A|As], MapIn, MapOut, [SA|SAs]) :-
    make_acyclic_term(A, MapIn, MapMid, SA),
    make_acyclic_args(As, MapMid, MapOut, SAs).

find_pair(Term, [pair(Orig,Val)|_], Val) :- Orig == Term, !.
find_pair(Term, [_|Rest], Val) :- find_pair(Term, Rest, Val).

replace_pair(Term, OldVal, NewVal, [pair(Orig,OldVal)|Rest], [pair(Orig,NewVal)|Rest]) :-
    Orig == Term, !.
replace_pair(Term, OldVal, NewVal, [H|T], [H|T2]) :-
    replace_pair(Term, OldVal, NewVal, T, T2).
replace_pair(_, _, _, [], []).

% =========================================================================
% HELPER COMBINATORS
% =========================================================================

% Helper: Remove ALL annotations (not just quantifiers)
strip_annotations_deep(@(Term, _), Stripped) :-
    !, strip_annotations_deep(Term, Stripped).
strip_annotations_deep(![_-X]:Body, ![X]:StrippedBody) :-
    !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(?[_-X]:Body, ?[X]:StrippedBody) :-
    !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(A & B, SA & SB) :-
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A | B, SA | SB) :-
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A => B, SA => SB) :-
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A <=> B, SA <=> SB) :-
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(Term, Term).

% =========================================================================
% FITCH DERIVATION HELPERS
% =========================================================================

derive_and_continue(Scope, Formula, RuleTemplate, Refs, RuleTerm, SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, DerivLine, _, VarIn, V1),
    fitch_g4_proof(SubProof, [DerivLine:Formula|Context], Scope, DerivLine, NextLine, ResLine, V1, VarOut).

derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    NextLine is CurLine + 1,
    assert_safe_fitch_line(NextLine, Formula, RuleTerm, Scope),
    format(atom(Just), RuleTemplate, Refs),
    render_have(Scope, Formula, Just, CurLine, NextLine, VarIn, VarOut),
    ResLine = NextLine.

assume_in_scope(Assumption, _Goal, SubProof, Context, ParentScope, StartLine, EndLine, GoalLine, VarIn, VarOut) :-
    AssLine is StartLine + 1,
    assert_safe_fitch_line(AssLine, Assumption, assumption, ParentScope),
    render_hypo(ParentScope, Assumption, 'AS', StartLine, AssLine, VarIn, V1),
    NewScope is ParentScope + 1,
    fitch_g4_proof(SubProof, [AssLine:Assumption|Context], NewScope, AssLine, EndLine, GoalLine, V1, VarOut).

% =========================================================================
% FORMULA EXTRACTION & HELPERS
% =========================================================================

extract_new_formula(CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ member(NewFormula, CurrentPremisses),
    !.
extract_new_formula(_CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ is_quantified(NewFormula),
    !.
extract_new_formula(CurrentPremisses, SubProof, _) :-
    format('% ERROR extract_new_formula: No suitable formula found~n', []),
    format('%   CurrentPremisses: ~w~n', [CurrentPremisses]),
    SubProof =.. [Rule|[(SubPremisses > _)|_]],
    format('%   SubProof rule: ~w~n', [Rule]),
    format('%   SubPremisses: ~w~n', [SubPremisses]),
    fail.

% =========================================================================
% FIND_CONTEXT_LINE: Match formulas in context
% =========================================================================
% ABSOLUTE PRIORITY: PREMISSES (lines 1-N where N = number of premisses)
% =========================================================================

% FIXED: Search in entire context, prefer most recent (highest line number)
% This ensures derived formulas are used instead of premisses when both exist
find_context_line(Formula, Context, LineNumber) :-
    premiss_list(PremList),
    length(PremList, NumPremises),
    % Search ONLY in the first N lines
    member(LineNumber:ContextFormula, Context),
    LineNumber =< NumPremises,
    % Match with different possible variants
    ( ContextFormula = Formula
    ; strip_annotations_match(Formula, ContextFormula)
    ; formulas_equivalent(Formula, ContextFormula)
    ),
    !.  % Stop as soon as found in premisses

% =========================================================================
% PRIORITY -1: QUANTIFIER NEGATION (original ~ form)
% =========================================================================

% Search for (![x-x]:Body) => # but context has ~![x]:Body (original form)
find_context_line((![_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Original form with ~
        ContextFormula = (~ ![_]:Body)
    ;
        % Transformed form
        ContextFormula = ((![_]:Body) => #)
    ;
        % Transformed form with annotation
        ContextFormula = ((![_-_]:Body) => #)
    ),
    !.

% Same for existential
find_context_line((?[_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (~ ?[_]:Body)
    ;
        ContextFormula = ((?[_]:Body) => #)
    ;
        ContextFormula = ((?[_-_]:Body) => #)
    ),
    !.

% =========================================================================
% PRIORITY 0: QUANTIFIERS - MATCH COMPLEX INTERNAL STRUCTURE
% =========================================================================

% Universal: match internal structure independently of transformation
find_context_line(![Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Case 1: Context without annotation
        ContextFormula = (![Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        % Case 2: Context with annotation - compare bodies after stripping annotations
        ContextFormula = (![Z-_]:ContextBody),
        (
            formulas_equivalent(SearchBody, ContextBody)
        ;
            % Fallback: strip all annotations and compare structurally
            strip_annotations_deep(SearchBody, StrippedSearch),
            strip_annotations_deep(ContextBody, StrippedContext),
            StrippedSearch =@= StrippedContext
        )
    ),
    !.

% Existential: match internal structure
find_context_line(?[Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        ContextFormula = (?[Z-_]:ContextBody),
        (
            formulas_equivalent(SearchBody, ContextBody)
        ;
            % Fallback: strip all annotations and compare structurally
            strip_annotations_deep(SearchBody, StrippedSearch),
            strip_annotations_deep(ContextBody, StrippedContext),
            StrippedSearch =@= StrippedContext
        )
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITY 1: NEGATIONS (original ~ notation vs transformed => #)
% -------------------------------------------------------------------------

% Case 1: Search for ?[x]:A => # but context has ~ ?[x]:A
find_context_line((?[Z-_]:A) => #, Context, LineNumber) :-
    member(LineNumber:(~ ?[Z]:A), Context), !.

% Case 2: Search for ![x]:(A => #) but context has ![x]: ~A
find_context_line(![Z-_]:(A => #), Context, LineNumber) :-
    member(LineNumber:(![Z]: ~A), Context), !.

% Case 3: Search for A => # but context has ~A (simple formula)
find_context_line(A => #, Context, LineNumber) :-
    A \= (?[_]:_),
    A \= (![_]:_),
    member(LineNumber:(~A), Context), !.

% -------------------------------------------------------------------------
% PRIORITY 2: QUANTIFIERS (with/without variable annotations)
% -------------------------------------------------------------------------

% Universal: search for ![x-x]:Body but context has ![x]:Body
find_context_line(![Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (![Z]:Body)      % Without annotation
    ;
        ContextFormula = (![Z-_]:Body)    % With different annotation
    ),
    !.

% Existential: search for ?[x-x]:Body but context has ?[x]:Body
find_context_line(?[Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:Body)      % Without annotation
    ;
        ContextFormula = (?[Z-_]:Body)    % With different annotation
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITY 3: BICONDITIONALS (decomposed)
% -------------------------------------------------------------------------

find_context_line((A => B) & (B => A), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

find_context_line((B => A) & (A => B), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

% -------------------------------------------------------------------------
% PRIORITY 4: EXACT MATCH
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:Formula, Context), !.

% -------------------------------------------------------------------------
% PRIORITY 5: UNIFICATION
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    unify_with_occurs_check(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% PRIORITY 6: STRUCTURE MATCHING
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    match_formula_structure(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% FALLBACK: WARNING if no match found
% -------------------------------------------------------------------------

% Silent fallback for formulas with asq (antisequent eigenvariables) - expected to not match
find_context_line(Formula, _Context, 0) :-
    sub_term(asq(_,_), Formula),
    !.

find_context_line(Formula, _Context, 0) :-
    format('% WARNING: Formula ~w not found in context~n', [Formula]).

% =========================================================================
% HELPER: Formula equivalence (pure structural comparison)
% =========================================================================

% Helper: match by removing annotations
strip_annotations_match(![_-X]:Body, ![X]:Body) :- !.
strip_annotations_match(![X]:Body, ![_-X]:Body) :- !.
strip_annotations_match(?[_-X]:Body, ?[X]:Body) :- !.
strip_annotations_match(?[X]:Body, ?[_-X]:Body) :- !.
strip_annotations_match(A, B) :- A = B.

% Biconditional: match structure without considering order
formulas_equivalent((A1 => B1) & (B2 => A2), C <=> D) :-
    !,
    (
        (formulas_equivalent(A1, C), formulas_equivalent(A2, C),
         formulas_equivalent(B1, D), formulas_equivalent(B2, D))
    ;
        (formulas_equivalent(A1, D), formulas_equivalent(A2, D),
         formulas_equivalent(B1, C), formulas_equivalent(B2, C))
    ).

formulas_equivalent(A <=> B, (C => D) & (D2 => C2)) :-
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(A, C2),
         formulas_equivalent(B, D), formulas_equivalent(B, D2))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(A, D2),
         formulas_equivalent(B, C), formulas_equivalent(B, C2))
    ).

formulas_equivalent((A <=> B), (C <=> D)) :-
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(B, D))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(B, C))
    ).

% Transformed negation
formulas_equivalent(A => #, ~ B) :- !, formulas_equivalent(A, B).
formulas_equivalent(~ A, B => #) :- !, formulas_equivalent(A, B).

% Quantifiers: compare bodies only (ignore variable)
formulas_equivalent(![_]:Body1, ![_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_]:Body1, ![_-_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_-_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).

formulas_equivalent(?[_]:Body1, ?[_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_]:Body1, ?[_-_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_-_]:Body2) :-
    !, formulas_equivalent(Body1, Body2).

% Binary connectives
formulas_equivalent(A & B, C & D) :-
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A | B, C | D) :-
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A => B, C => D) :-
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).

% Bottom
formulas_equivalent(#, #) :- !.

% Predicates/Terms: compare structure (ignore variables)
formulas_equivalent(Term1, Term2) :-
    compound(Term1),
    compound(Term2),
    !,
    Term1 =.. [Functor|_Args1],
    Term2 =.. [Functor|_Args2],
    % Same functor is sufficient (we ignore arguments that are variables)
    !.

% Strict identity
formulas_equivalent(A, B) :- A == B, !.

% Fallback: atomic terms with same name
formulas_equivalent(A, B) :-
    atomic(A), atomic(B),
    !.

% Helper: match two formulas by structure (modulo variable renaming)

% Negations
match_formula_structure(A => #, B => #) :-
    !, match_formula_structure(A, B).
match_formula_structure(~A, B => #) :-
    !, match_formula_structure(A, B).
match_formula_structure(A => #, ~ B) :-
    !, match_formula_structure(A, B).
match_formula_structure(~ A, ~ B) :-
    !, match_formula_structure(A, B).

% Quantifiers
match_formula_structure(![_-_]:Body1, ![_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).
match_formula_structure(?[_-_]:Body1, ?[_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).

% Binary connectives
match_formula_structure(A & B, C & D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A | B, C | D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A => B, C => D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A <=> B, C <=> D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).

% Bottom
match_formula_structure(#, #) :- !.

% Strict equality
match_formula_structure(A, B) :-
    A == B, !.

% Subsumption
match_formula_structure(A, B) :-
    subsumes_term(A, B) ; subsumes_term(B, A).

% =========================================================================
% ADDITIONAL FITCH HELPERS
% =========================================================================

find_disj_context(L, R, Context, Line) :-
    ( member(Line:(CL | CR), Context), subsumes_term((L | R), (CL | CR)) -> true
    ; member(Line:(CL | CR), Context), \+ \+ ((L = CL, R = CR))
    ).

extract_witness(SubProof, Witness) :-
    SubProof =.. [_Rule|Args],
    Args = [(Prem > _)|_],
    % Find first witness with Skolem
    member(Witness, Prem),
    contains_skolem(Witness),
    !.
extract_witness(SubProof, Witness) :-
    SubProof =.. [_, (_ > _), SubSP|_],
    extract_witness(SubSP, Witness).

% Check if witness already exists in context (structurally, ignoring annotations)
witness_in_context(Witness, Context) :-
    member(_:CtxFormula, Context),
    strip_annotations_deep(Witness, StrippedWitness),
    strip_annotations_deep(CtxFormula, StrippedCtx),
    StrippedWitness =@= StrippedCtx,
    !.

is_quantified(![_-_]:_) :- !.
is_quantified(?[_-_]:_) :- !.

contains_skolem(Formula) :-
    Formula =.. [_|Args],
    member(Arg, Args),
    (Arg = f_sk(_) ; Arg = f_sk(_,_) ; compound(Arg), contains_skolem(Arg)).

is_direct_conjunct(G, (A & B)) :- (G = A ; G = B), !.
is_direct_conjunct(G, (A & R)) :- (G = A ; is_direct_conjunct(G, R)).

extract_conjuncts((A & B), CLine, Scope, CurLine, [L1:A, L2:B], L2, VarIn, VarOut) :-
    L1 is CurLine + 1,
    L2 is CurLine + 2,
    assert_safe_fitch_line(L1, A, land(CLine), Scope),
    assert_safe_fitch_line(L2, B, land(CLine), Scope),
    format(atom(Just1), '$ \\land E $ ~w', [CLine]),
    format(atom(Just2), '$ \\land E $ ~w', [CLine]),
    render_have(Scope, A, Just1, CurLine, L1, VarIn, V1),
    render_have(Scope, B, Just2, L1, L2, V1, VarOut).

% =========================================================================
% IMMEDIATE DERIVATION LOGIC
% =========================================================================

derive_immediate(Scope, Formula, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Formula, RuleTerm, Scope),
    format(atom(Just), JustFormat, JustArgs),
    render_have(Scope, Formula, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

try_derive_immediately(Goal, Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ResLine:Goal, Context),
    !,
    NextLine = CurLine,
    VarOut = VarIn.

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(MajLine:(Ant => Goal), Context),
    member(MinLine:Ant, Context),
    !,
    RuleTerm = l0cond(MajLine, MinLine),
    JustFormat = '$ \\to E $ ~w,~w',
    JustArgs = [MajLine, MinLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ConjLine:(A & B), Context),
    (Goal = A ; Goal = B),
    !,
    RuleTerm = land(ConjLine),
    JustFormat = '$ \\land E $ ~w',
    JustArgs = [ConjLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(FLine: #, Context),
    !,
    RuleTerm = lbot(FLine),
    JustFormat = '$ \\bot E $ ~w',
    JustArgs = [FLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L | R),
    ( member(SLine:L, Context) -> true ; member(SLine:R, Context) ),
    !,
    RuleTerm = ror(SLine),
    JustFormat = '$ \\lor I $ ~w',
    JustArgs = [SLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L & R),
    member(LLine:L, Context),
    member(RLine:R, Context),
    !,
    RuleTerm = rand(LLine, RLine),
    JustFormat = '$ \\land I $ ~w,~w',
    JustArgs = [LLine, RLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% SHARED HYPOTHESIS MAP CONSTRUCTION
% =========================================================================

build_hypothesis_map([], Map, Map).
build_hypothesis_map([N-Formula-assumption-Scope|Rest], AccMap, FinalMap) :-
    !,
    ( member(M-Formula-assumption-Scope, Rest), M > N ->
        build_hypothesis_map(Rest, [M-N|AccMap], FinalMap)
    ;
        build_hypothesis_map(Rest, AccMap, FinalMap)
    ).
build_hypothesis_map([_|Rest], AccMap, FinalMap) :-
    build_hypothesis_map(Rest, AccMap, FinalMap).

% =========================================================================
% End of common ND PRINTING
% =========================================================================
% =========================================================================
% NATURAL DEDUCTION PRINTER IN FLAG STYLE
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic fitch_line_latex/2.
:- dynamic abbreviated_line/1.
% =========================================================================
% FROM G4 Sequent Calculus To Natural Deduction in Fitch Style
% =========================================================================
% This module converts G4 sequent calculus proofs into Fitch-style natural
% deduction proofs for pedagogical purposes and readability.
%
% Fitch-style format features:
% - Flag-style indentation showing subproof structure
% - Line-by-line derivation with justifications
% - LaTeX output for publication-quality rendering
% - Tracks context and line references automatically
%
% Conversion strategy:
% 1. Traverse G4 proof tree bottom-up
% 2. Map sequent rules to corresponding natural deduction rules
% 3. Manage subproof indentation (Fitch flags)
% 4. Track line numbers and justifications
% 5. Generate LaTeX using fitch.sty package syntax
%
% Rule mappings:
% - Sequent right rules -> Introduction rules
% - Sequent left rules -> Elimination rules
% - Structural rules -> Reiteration and assumption management
%
% The resulting Fitch proof is more intuitive than raw sequent calculus
% and suitable for teaching and publication.
% =========================================================================
% g4_to_fitch_theorem/1 : For theorems
g4_to_fitch_theorem(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(fitch_line_latex(_, _)),
    retractall(abbreviated_line(_)),
    fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _).
% =========================================================================
% ASSERTION SECURISEE
% =========================================================================
assert_safe_fitch_line(N, Formula, Just, Scope) :-
    catch(
        (
            ( acyclic_term(Formula) ->
                Safe = Formula
            ;
                make_acyclic_term(Formula, Safe)
            ),
            assertz(fitch_line(N, Safe, Just, Scope))
        ),
        Error,
        (
            format('% Warning: Could not assert line ~w: ~w~n', [N, Error]),
            assertz(fitch_line(N, error_term(Formula), Just, Scope))
        )
    ).

% =========================================================================
% GESTION DES SUBSTITUTIONS @
% =========================================================================

fitch_g4_proof(@(ProofTerm, _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    fitch_g4_proof(ProofTerm, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% AXIOME
% =========================================================================

fitch_g4_proof(ax((Premisses > [Goal]), _Tag), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

fitch_g4_proof(ax((Premisses > [Goal])), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

% =========================================================================
% PROPOSITIONAL RULES
% =========================================================================
% L0->
fitch_g4_proof(l0cond((Premisss > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    select((Ant => Cons), Premisss, Remaining),
    member(Ant, Remaining),
    find_context_line((Ant => Cons), Context, MajLine),
    find_context_line(Ant, Context, MinLine),
    DerLine is CurLine + 1,
    format(atom(Just), '$ \\to E $ ~w,~w', [MajLine, MinLine]),
    render_have(Scope, Cons, Just, CurLine, DerLine, VarIn, V1),
    assert_safe_fitch_line(DerLine, Cons, l0cond(MajLine, MinLine), Scope),
    fitch_g4_proof(SubProof, [DerLine:Cons|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut).

% L/\->
fitch_g4_proof(landto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select(((A & B) => C), Premisses, _),
    once(member(ImpLine:((A & B) => C), Context)),
    derive_and_continue(Scope, NewFormula, '$ \\land \\to E $ ~w', [ImpLine],
                       landto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% L\/-> : Disjunction to implications
fitch_g4_proof(lorto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    findall(F, (member(F, SubPremisses), \+ member(F, Premisses)), NewFormulas),
    select(((A | B) => C), Premisses, _),
    find_context_line(((A | B) => C), Context, ImpLine),
    ( NewFormulas = [F1, F2] ->
        Line1 is CurLine + 1,
        Line2 is CurLine + 2,
        assert_safe_fitch_line(Line1, F1, lorto(ImpLine), Scope),
        assert_safe_fitch_line(Line2, F2, lorto(ImpLine), Scope),
        format(atom(Just), '$ \\lor \\to E $ ~w', [ImpLine]),
        render_have(Scope, F1, Just, CurLine, Line1, VarIn, V1),
        render_have(Scope, F2, Just, Line1, Line2, V1, V2),
        fitch_g4_proof(SubProof, [Line2:F2, Line1:F1|Context], Scope, Line2, NextLine, ResLine, V2, VarOut)
    ; NewFormulas = [F1] ->
        derive_and_continue(Scope, F1, '$ \\lor \\to E $ ~w', [ImpLine],
                           lorto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ).


% L/\ : Conjunction elimination
fitch_g4_proof(land((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((A & B), Premisses, _),
   % member(ConjLine:(A & B), Context), corrected by next line
    find_context_line((A & B), Context, ConjLine),
    ( is_direct_conjunct(Goal, (A & B)) ->
        derive_formula(Scope, Goal, '$ \\land E $ ~w', [ConjLine], land(ConjLine),
                      CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        extract_conjuncts((A & B), ConjLine, Scope, CurLine, ExtCtx, LastLine, VarIn, V1),
        append(ExtCtx, Context, NewCtx),
        fitch_g4_proof(SubProof, NewCtx, Scope, LastLine, NextLine, ResLine, V1, VarOut)
    ).

% L_|_ : Explosion
fitch_g4_proof(lbot((Premisss > [Goal]), _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(#, Premisss),
    member(FalseLine: #, Context),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, lbot(FalseLine), Scope),
    format(atom(Just), '$ \\bot E $ ~w', [FalseLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% R\/ : Disjunction introduction
fitch_g4_proof(ror((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (_ | _), try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
        true
    ; fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, DisjunctLine, VarIn, V1),
      OrLine is SubEnd + 1,
      assert_safe_fitch_line(OrLine, Goal, ror(DisjunctLine), Scope),
      format(atom(Just), '$ \\lor I $ ~w', [DisjunctLine]),
      render_have(Scope, Goal, Just, SubEnd, OrLine, V1, VarOut),
      NextLine = OrLine,
      ResLine = OrLine
    ).

% =========================================================================
% RULES WITH ASSUMPTIONS (ASSUME-DISCHARGE)
% =========================================================================

% R-> : Implication introduction
fitch_g4_proof(rcond((_ > [A => B]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% TNE : Triple negation elimination
fitch_g4_proof(tne((_ > [(A => B)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% IP : Indirect proof / Classical
fitch_g4_proof(ip((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (A => #) ->
        Assumption = ((A => #) => #),
        Rule = 'DNE_m'
    ;
        Assumption = (Goal => #),
        Rule = 'IP'
    ),
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, Assumption, assumption, Scope),
    render_hypo(Scope, Assumption, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:Assumption|Context], NewScope, HypLine, SubEnd, BotLine, V1, V2),
    IPLine is SubEnd + 1,
    assert_safe_fitch_line(IPLine, Goal, ip(HypLine, BotLine), Scope),
    format(atom(Just), '~w ~w-~w', [Rule, HypLine, BotLine]),
    render_have(Scope, Goal, Just, SubEnd, IPLine, V2, VarOut),
    NextLine = IPLine,
    ResLine = IPLine.

% L\/ : Disjunction elimination
% L-or: Disjunction elimination with DS optimization
% DISJUNCTIVE SYLLOGISM (DS): If we have A \/ B and ~A, derive B directly
% Valid in intuitionistic and classical logic (not minimal logic)
% Pattern: One branch uses explosion (~A with A), other branch derives Goal from B
fitch_g4_proof(lor((Premisss > [_Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    % Try DS optimization: Check if we have A \/ B and ~A (A => #)
    select((A | B), Premisss, _),
    % Check if ~A (i.e., A => #) is available
    ( member((A => #), Premisss) ->
        % We have A \/ B and ~A, so we can use DS to derive B directly
        % This is valid because SP1 would just derive _|_ from A and ~A, then Goal by _|_E
        % Find the disjunction and negation in context
        ( find_disj_context(A, B, Context, DisjLine) -> true
        ; find_context_line((A | B), Context, DisjLine)
        ),
        % CORRECTION: Chercher explicitement (A => #) dans le contexte
        % Do not use find_context_line which could match another implication
        member(NegLine:NegFormula, Context),
        NegFormula = (A => #),  % Verifier EXACTEMENT que c'est bien A => #
        % Derive B by DS (without showing the explosion subproof)
        DerLine is CurLine + 1,
        assert_safe_fitch_line(DerLine, B, ds(DisjLine, NegLine), Scope),
        format(atom(Just), '$ DS $ ~w,~w', [DisjLine, NegLine]),
        render_have(Scope, B, Just, CurLine, DerLine, VarIn, V1),
        % Continue with Goal derivation from B
        fitch_g4_proof(SP2, [DerLine:B|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut),
        !
    ; member((B => #), Premisss) ->
        % Symmetric case: We have A \/ B and ~B, derive A by DS
        ( find_disj_context(A, B, Context, DisjLine) -> true
        ; find_context_line((A | B), Context, DisjLine)
        ),
        % CORRECTION: Chercher explicitement (B => #) dans le contexte
        member(NegLine:NegFormula, Context),
        NegFormula = (B => #),  % Verifier EXACTEMENT que c'est bien B => #
        DerLine is CurLine + 1,
        assert_safe_fitch_line(DerLine, A, ds(DisjLine, NegLine), Scope),
        format(atom(Just), '$ DS $ ~w,~w', [DisjLine, NegLine]),
        render_have(Scope, A, Just, CurLine, DerLine, VarIn, V1),
        fitch_g4_proof(SP1, [DerLine:A|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut),
        !
    ;
        fail  % DS not applicable, fall through to regular \/E
    ).

% L-or: Disjunction elimination (regular case with full \/E)
fitch_g4_proof(lor((Premisss > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
       true
    ;
      select((A | B), Premisss, _),
      find_disj_context(A, B, Context, DisjLine),
      AssLineA is CurLine + 1,
      assert_safe_fitch_line(AssLineA, A, assumption, Scope),
      render_hypo(Scope, A, 'AS', CurLine, AssLineA, VarIn, V1),
      NewScope is Scope + 1,
      fitch_g4_proof(SP1, [AssLineA:A|Context], NewScope, AssLineA, EndA, GoalA, V1, V2),
      AssLineB is EndA + 1,
      assert_safe_fitch_line(AssLineB, B, assumption, Scope),
      render_hypo(Scope, B, 'AS', EndA, AssLineB, V2, V3),
      fitch_g4_proof(SP2, [AssLineB:B|Context], NewScope, AssLineB, EndB, GoalB, V3, V4),
      ElimLine is EndB + 1,
      assert_safe_fitch_line(ElimLine, Goal, lor(DisjLine, AssLineA, EndA, AssLineB, EndB), Scope),
      format(atom(Just), '$ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, AssLineA, EndA, AssLineB, EndB]),
      render_have(Scope, Goal, Just, EndB, ElimLine, V4, VarOut),
      NextLine = ElimLine,
      ResLine = ElimLine
    ).

% =========================================================================
% BINARY RULES
% =========================================================================

% R/\ : Conjunction introduction
fitch_g4_proof(rand((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    Goal = (L & _R),
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) -> true
    ; fitch_g4_proof(SP1, Context, Scope, CurLine, End1, LeftLine, VarIn, V1),
      fitch_g4_proof(SP2, [LeftLine:L|Context], Scope, End1, End2, RightLine, V1, V2),
      derive_formula(Scope, Goal, '$ \\land I $ ~w,~w', [LeftLine, RightLine], rand(LeftLine, RightLine),
                    End2, NextLine, ResLine, V2, VarOut)
    ).

% L->-> : Special G4 rule
fitch_g4_proof(ltoto((Premisses > _), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select(((Ant => Inter) => Cons), Premisses, _),
    find_context_line(((Ant => Inter) => Cons), Context, ComplexLine),

    % STEP 1: Derive (Inter => Cons) by L->->
    ExtractLine is CurLine + 1,
    format(atom(ExtractJust), '\\to \\to E $ ~w', [ComplexLine]),
    render_have(Scope, (Inter => Cons), ExtractJust, CurLine, ExtractLine, VarIn, V1),
    assert_safe_fitch_line(ExtractLine, (Inter => Cons), ltoto(ComplexLine), Scope),

    % STEP 2: Assume Ant
    AssLine is ExtractLine + 1,
    assert_safe_fitch_line(AssLine, Ant, assumption, Scope),
    render_hypo(Scope, Ant, 'AS', ExtractLine, AssLine, V1, V2),
    NewScope is Scope + 1,

    % STEP 3: Prove Inter with [Ant, (Inter=>Cons) | Context]
    fitch_g4_proof(SP1, [AssLine:Ant, ExtractLine:(Inter => Cons)|Context],
                  NewScope, AssLine, SubEnd, InterLine, V2, V3),

    % STEP 4: Derive (Ant => Inter) by ->I
    ImpLine is SubEnd + 1,
    assert_safe_fitch_line(ImpLine, (Ant => Inter), rcond(AssLine, InterLine), Scope),
    format(atom(Just1), '$ \\to I $ ~w-~w', [AssLine, InterLine]),
    render_have(Scope, (Ant => Inter), Just1, SubEnd, ImpLine, V3, V4),

    % STEP 5: Derive Cons by ->E
    MPLine is ImpLine + 1,
    assert_safe_fitch_line(MPLine, Cons, l0cond(ComplexLine, ImpLine), Scope),
    format(atom(Just2), '$ \\to E $ ~w,~w', [ComplexLine, ImpLine]),
    render_have(Scope, Cons, Just2, ImpLine, MPLine, V4, V5),

    % STEP 6: Continue with SP2
    fitch_g4_proof(SP2, [MPLine:Cons, ImpLine:(Ant => Inter), ExtractLine:(Inter => Cons)|Context],
                  Scope, MPLine, NextLine, ResLine, V5, VarOut).
% =========================================================================
% QUANTIFICATION RULES
% =========================================================================
% Rforall

fitch_g4_proof(rall((_ > [(![Z-X]:A)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, BodyLine, VarIn, V1),
    derive_formula(Scope, (![Z-X]:A), '$ \\forall I $ ~w', [BodyLine], rall(BodyLine),
                   SubEnd, NextLine, ResLine, V1, VarOut).

% Lforall : Universal Elimination
fitch_g4_proof(lall((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses > _, SubProof, NewFormula),

    % Find the universal quantifier that generates NewFormula
    (
        % Case 1: NewFormula is a direct instance of a universal in Premises
        (
            member((![Z-X]:Body), Premisses),
            % Check if Body (with substitution) gives NewFormula
            strip_annotations_deep(Body, StrippedBody),
            strip_annotations_deep(NewFormula, StrippedNew),
            unifiable(StrippedBody, StrippedNew, _),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 2: Search by equivalent structure
            member((![Z-X]:Body), Premisses),
            formulas_equivalent(Body, NewFormula),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 3: Fallback - take the first (current behavior)
            select((![Z-X]:Body), Premisses, _),
            UniversalFormula = (![Z-X]:Body)
        )
    ),

    find_context_line(UniversalFormula, Context, UnivLine),
    derive_and_continue(Scope, NewFormula, '$ \\forall E $ ~w', [UnivLine], lall(UnivLine),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% Rexists
fitch_g4_proof(rex((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, _WitnessLine, VarIn, V1),
    % CORRECTION: Reference SubEnd (witness line), not WitnessLine
    derive_formula(Scope, Goal, '$ \\exists I $ ~w', [SubEnd], rex(SubEnd),
                  SubEnd, NextLine, ResLine, V1, VarOut).
% Lexists
fitch_g4_proof(lex((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),
    extract_witness(SubProof, Witness),
    % Check if witness already in context (structurally)
    ( witness_in_context(Witness, Context) ->
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ; WitLine is CurLine + 1,
      NewScope is Scope + 1,
      assert_safe_fitch_line(WitLine, Witness, assumption, Scope),
      render_hypo(Scope, Witness, 'AS', CurLine, WitLine, VarIn, V1),
      fitch_g4_proof(SubProof, [WitLine:Witness|Context], NewScope, WitLine, SubEnd, _GoalLine, V1, V2),
      ElimLine is SubEnd + 1,
      assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, SubEnd), Scope),
      % CORRECTION: Reference SubEnd (last line of subproof)
      format(atom(Just), '$ \\exists E $ ~w,~w-~w', [ExistLine, WitLine, SubEnd]),
      render_have(Scope, Goal, Just, SubEnd, ElimLine, V2, VarOut),
      NextLine = ElimLine, ResLine = ElimLine
    ).
% Lexists\/ : Combined existential-disjunction
fitch_g4_proof(lex_lor((Premisses > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SP1 =.. [_, (Prem1 > _)|_],
    SP2 =.. [_, (Prem2 > _)|_],
    member(WitA, Prem1), contains_skolem(WitA), \+ is_quantified(WitA),
    member(WitB, Prem2), contains_skolem(WitB), \+ is_quantified(WitB),

    % CORRECTION: Trouver le quantificateur existentiel comme dans lex normale
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),

    WitLine is CurLine + 1,
    % CORRECTION: Ajouter assert_safe_fitch_line AVANT render_hypo
    assert_safe_fitch_line(WitLine, (WitA | WitB), assumption, Scope),
    render_hypo(Scope, (WitA | WitB), 'AS', CurLine, WitLine, VarIn, V1),
    NewScope is Scope + 1,
    assume_in_scope(WitA, Goal, SP1, [WitLine:(WitA | WitB)|Context],
                   NewScope, WitLine, EndA, GoalA, V1, V2),
    assume_in_scope(WitB, Goal, SP2, [WitLine:(WitA | WitB)|Context],
                   NewScope, EndA, EndB, GoalB, V2, V3),
    DisjElim is EndB + 1,
    CaseAStart is WitLine + 1,
    CaseBStart is EndA + 1,
    % CORRECTION: Ajouter assert_safe_fitch_line AVANT render_have pour lor
    format(atom(DisjJust), '$ \\lor E $ ~w,~w-~w,~w-~w',
           [WitLine, CaseAStart, GoalA, CaseBStart, GoalB]),
    assert_safe_fitch_line(DisjElim, Goal, lor(WitLine, CaseAStart, CaseBStart, GoalA, GoalB), NewScope),
    render_have(NewScope, Goal, DisjJust, EndB, DisjElim, V3, V4),
    ElimLine is DisjElim + 1,
    % CORRECTION: Use the actual ExistLine found with find_context_line
    format(atom(ExistJust), '$ \\exists E $ ~w-~w', [WitLine, DisjElim]),
    assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, DisjElim), Scope),
    render_have(Scope, Goal, ExistJust, DisjElim, ElimLine, V4, VarOut),
    NextLine = ElimLine, ResLine = ElimLine.

% CQ_c : Classical quantifier conversion
fitch_g4_proof(cq_c((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((![Z-X]:A) => B, Premisses, _),
    find_context_line((![Z-X]:A) => B, Context, Line),  % Find the right line in context
    derive_and_continue(Scope, NewFormula, '$ CQ_{c} $ ~w', [Line], cq_c(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% CQ_m : Minimal quantifier conversion
fitch_g4_proof(cq_m((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((?[Z-X]:A)=>B, Premisses, _),
    find_context_line((?[Z-X]:A)=>B, Context, Line),  % Find the right line in context
    derive_and_continue(Scope, NewFormula, '$ CQ_{m} $ ~w', [Line], cq_m(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% EQUALITY RULES - CORRECTED VERSION
% =========================================================================

% Reflexivity

% Symmetry

% Transitivity

% Substitution (Leibniz) - MAIN CASE

% Congruence

% Substitution in equality

% Transitivity chain
% =========================================================================
% FALLBACK
% =========================================================================
fitch_g4_proof(UnknownRule, _Context, _Scope, CurLine, CurLine, CurLine, VarIn, VarIn) :-
    format('% WARNING: Unknown rule ~w~n', [UnknownRule]).
% =========================================================================
% END OF FLAG STYLE PRINTER
% =========================================================================
% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic fitch_line_latex/2.
:- dynamic abbreviated_line/1.
% =========================================================================
% DISPLAY PREMISS LIST FOR TREE STYLE
% =========================================================================
% render_premiss_list_silent/5: Silent version for tree style
render_premiss_list_silent([], _, Line, Line, []) :- !.

render_premiss_list_silent([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    assert_safe_fitch_line(CurLine, LastPremiss, premiss, Scope),
    NextLine is CurLine + 1.

render_premiss_list_silent([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    assert_safe_fitch_line(CurLine, Premiss, premiss, Scope),
    NextCurLine is CurLine + 1,
    render_premiss_list_silent(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% TREE STYLE INTERFACE
% =========================================================================
% This module converts G4 proofs into tree-style natural deduction format.
%
% Tree-style natural deduction features:
% - Top-down visual tree structure
% - Premises at the leaves
% - Conclusion at the root
% - Horizontal lines showing rule applications
% - LaTeX output using bussproofs package
%
% Advantages over Fitch-style:
% - More compact for short proofs
% - Shows logical structure at a glance
% - Traditional format used in logic textbooks
% - Better for visualizing proof flow
%
% The tree format is particularly effective for:
% - Teaching natural deduction
% - Showing structural properties
% - Comparing different proof strategies
% - Publication in formal logic contexts
%
% Disadvantages:
% - Can become unwieldy for complex proofs
% - Less explicit about subproof scope
% - Harder to follow step-by-step
% =========================================================================
render_nd_tree_proof(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    extract_formula_from_proof(Proof, TopFormula),
    detect_and_set_logic_level(TopFormula),
    catch(
        (
            ( premiss_list(PremissList), PremissList = [_|_] ->
                render_premiss_list_silent(PremissList, 0, 1, NextLine, InitialContext),
                LastPremLine is NextLine - 1,
                % Capture ResLine (6th argument) and LastLine (5th) which is the conclusion line
                % FIXED: Suppress Fitch output with with_output_to
                with_output_to(atom(_), fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _)),
                % If no line was added (pure axiom), add reiteration line
                ( LastLine = LastPremLine ->
                    NewLine is LastPremLine + 1,
                    fitch_line(ResLine, Conclusion, _, _),
                    assert_safe_fitch_line(NewLine, Conclusion, reiteration(ResLine), 0),
                    RootLine = NewLine
                ;
                    RootLine = ResLine
                )
            ;
                % No premisses
                with_output_to(atom(_), fitch_g4_proof(Proof, [], 1, 0, _, ResLine, 0, _)),
                RootLine = ResLine
            ),
            % Use RootLine as the root of the tree
            collect_and_render_tree(RootLine)
        ),
        Error,
        (
            format('% Error rendering ND tree: ~w~n', [Error]),
            write('% Skipping tree visualization'), nl
        )
    ).
% =========================================================================
% COLLECT AND RENDER TREE
% =========================================================================

collect_and_render_tree(RootLineNum) :-
    findall(N-Formula-Just-Scope,
            (fitch_line(N, Formula, Just, Scope), \+ abbreviated_line(N)),
            Lines),
    predsort(compare_lines, Lines, SortedLines),
    ( SortedLines = [] ->
        write('% Empty proof tree'), nl
    ;
        % Collect all premiss formulas for conditional wrapping
        findall(F, fitch_line(_, F, premiss, _), AllPremisses),

        ( build_buss_tree(RootLineNum, SortedLines, Tree) ->

            % Check if the conclusion is simple (premiss/reiteration) AND there are multiple premisses
            % FIX: Check RootLineNum for justification, not just any line.
            ( is_simple_conclusion(RootLineNum, AllPremisses) ->
                % Force structure to display ALL premisses as branches
                wrap_premisses_in_tree(RootLineNum, AllPremisses, FinalTree)
            ;
                FinalTree = Tree
            ),

            write('\\begin{prooftree}'), nl,
            render_buss_tree(FinalTree),
            write('\\end{prooftree}'), nl
        ;
            write('% Warning: missing referenced line(s) or broken tree structure'), nl
        )
    ).

compare_lines(Delta, N1-_-_-_, N2-_-_-_) :-
    compare(Delta, N1, N2).

% Helper to check if conclusion is a simple reiteration or premiss
% FIX: Ensures the justification check is for the RootLineNum.
is_simple_conclusion(RootLineNum, AllPremisses) :-
    length(AllPremisses, N),
    N > 1, % Must have multiple premisses
    fitch_line(RootLineNum, _, Just, _), % Check RootLineNum's justification
    ( Just = premiss ; Just = reiteration(_) ),
    !.

% Helper to force creation of n-ary premiss node
wrap_premisses_in_tree(RootLineNum, AllPremisses, FinalTree) :-
    % Create a list of premiss_node(F) for all premisses
    findall(premiss_node(F), member(F, AllPremisses), PremissTrees),
    % Get the conclusion formula
    fitch_line(RootLineNum, FinalFormula, _, _),

    % Create the forced node
    FinalTree = n_ary_premiss_node(FinalFormula, PremissTrees).

% =========================================================================
% BUSSPROOFS TREE CONSTRUCTION
% =========================================================================

build_buss_tree(LineNum, FitchLines, Tree) :-
    ( member(LineNum-Formula-Just-_Scope, FitchLines) ->
        % Normal case: build tree from justification of this line
        build_tree_from_just(Just, LineNum, Formula, FitchLines, Tree)
    ;
        fail
    ).

% =========================================================================
% HELPER FOR TREE CONSTRUCTION
% =========================================================================
% Helper: Find available line if LineNum doesn't exist
find_closest_before(LineNum, FitchLines, ClosestLine) :-
    ( member(LineNum-_-_-_, FitchLines) ->
        ClosestLine = LineNum
    ;
        findall(N, (member(N-_-_-_, FitchLines), N < LineNum), BeforeLines),
        ( BeforeLines \= [] ->
            max_list(BeforeLines, ClosestLine)
        ;
            ClosestLine = LineNum  % Fallback
        )
    ).

% =========================================================================
% BUILD TREE FROM JUSTIFICATION
% =========================================================================
% -- Reiteration (Rule moved for priority, fixes P, Q |- P) --
build_tree_from_just(reiteration(SourceLine), _LineNum, Formula, FitchLines, reiteration_node(Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% -- Leaves --
build_tree_from_just(assumption, LineNum, Formula, _FitchLines, assumption_node(Formula, LineNum)) :- !.
% Axiom in G4 (A |- A) must be rendered as R (reiteration) in tree-style ND
build_tree_from_just(axiom, _LineNum, Formula, _FitchLines, reiteration_node(Formula, axiom_node(Formula))) :- !.
build_tree_from_just(premiss, _LineNum, Formula, _FitchLines, premiss_node(Formula)) :- !.

% -- Implication Rules --

% R-> (Implication Introduction)
build_tree_from_just(rcond(HypNum, GoalNum), _LineNum, Formula, FitchLines, discharged_node(rcond, HypNum, Formula, SubTree)) :-
    !,
    find_closest_before(GoalNum, FitchLines, ActualGoalNum),
    build_buss_tree(ActualGoalNum, FitchLines, SubTree).

% L0-> (Modus Ponens)
build_tree_from_just(l0cond(MajLine, MinLine), _LineNum, Formula, FitchLines, binary_node(l0cond, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(MajLine, FitchLines, TreeA), build_buss_tree(MinLine, FitchLines, TreeB).

% L->-> (Special G4 Rule)
build_tree_from_just(ltoto(Line), _LineNum, Formula, FitchLines, unary_node(ltoto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Disjunction Rules --
% R\/ (Intro Or)
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L\/ (Elim Or) - Ternary
build_tree_from_just(lor(DisjLine, HypA, EndA, HypB, EndB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !,
    build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(EndA, FitchLines, TreeA),
    build_buss_tree(EndB, FitchLines, TreeB).

% L\/-> (Left disjunction to conditional)
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Conjunction Rules --
% L/\ (Elim And)
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R/\ (Intro And)
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% L/\-> (Left conjunction to conditional)
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Falsum / Negation Rules --
% L_|_ (Bot Elim)
build_tree_from_just(lbot(BotLine), _LineNum, Formula, FitchLines, unary_node(lbot, Formula, SubTree)) :-
    !, build_buss_tree(BotLine, FitchLines, SubTree).

% IP (Indirect proof / Classical) - with DNE_m detection
build_tree_from_just(ip(HypNum, BotNum), _LineNum, Formula, FitchLines, discharged_node(RuleName, HypNum, Formula, SubTree)) :-
    !,
    % Detect if hypothesis is ~~A (double negation)
    ( member(HypNum-HypFormula-_-_, FitchLines),
      HypFormula = ((_ => #) => #) ->
        RuleName = dne_m
    ;
        RuleName = ip
    ),
    build_buss_tree(BotNum, FitchLines, SubTree).

% -- Quantifier Rules --
% Lexists (Exist Elim)
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines,
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree),
    build_buss_tree(GoalNum, FitchLines, GoalTree).

% Rexists (Exist Intro)
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% Lforall (Forall Elim) - Special case when UnivLine = 0 (not found in context)
build_tree_from_just(lall(0), _LineNum, Formula, _FitchLines, axiom_node(Formula)) :-
    !.

% Lforall (Forall Elim) - Normal case
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% Rforall (Forall Intro)
build_tree_from_just(rall(BodyLine), _LineNum, Formula, FitchLines, unary_node(rall, Formula, SubTree)) :-
    !, build_buss_tree(BodyLine, FitchLines, SubTree).

% Quantifier Conversions
build_tree_from_just(cq_c(Line), _LineNum, Formula, FitchLines, unary_node(cq_c, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

build_tree_from_just(cq_m(Line), _LineNum, Formula, FitchLines, unary_node(cq_m, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Equality Rules --







% DS: Disjunctive Syllogism (binary rule)
build_tree_from_just(ds(DisjLine, NegLine), _LineNum, Formula, FitchLines, binary_node(ds, Formula, DisjTree, NegTree)) :-
    !, build_buss_tree(DisjLine, FitchLines, DisjTree), build_buss_tree(NegLine, FitchLines, NegTree).

% Fallback
build_tree_from_just(Just, LineNum, Formula, _FitchLines, unknown_node(Just, LineNum, Formula)) :-
    format('% WARNING: Unknown justification type: ~w~n', [Just]).



% =========================================================================
% RECURSIVE TREE RENDERING (LaTeX Bussproofs)
% =========================================================================

% render_buss_tree(+Tree)
% Generates LaTeX commands for the tree

% -- Leaves --
render_buss_tree(axiom_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

render_buss_tree(premiss_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Assumptions (FIXED STYLE: Number in small size, noLine, Formula) --
render_buss_tree(assumption_node(F, HypNum)) :-
    format('\\AxiomC{\\scriptsize{~w}}', [HypNum]), nl,
    write('\\noLine'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Reiteration --
render_buss_tree(reiteration_node(F, SubTree)) :-
    render_buss_tree(SubTree),
    % Fix: Use write/nl to ensure inference is rendered
    write('\\RightLabel{\\scriptsize{$ R $}}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- N-ary FORCED nodes for displaying all premisses (simple conclusion case) --
render_buss_tree(n_ary_premiss_node(F, Trees)) :-
    % 1. Render all subtrees (premisses)
    maplist(render_buss_tree, Trees),

    % 2. Add Wk (Weakening) label
    write('\\RightLabel{\\scriptsize{$ R $}}'), nl,

    % 3. Use BinaryInfC if N=2 (P and Q)
    length(Trees, N),
    ( N = 2 ->
        % BinaryInfC command takes the last two AxiomC, exactly matching the P, Q |- P requirement
        write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
    ;
        % For N > 2, use TrinaryInfC if possible, otherwise a message
        ( N = 3 ->
            write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        ;
            % If N>3 (unlikely for simple proof), fall back to BinaryInfC to keep document compilable
            format('% Warning: Simplified N=~w inference to BinaryInfC for display.~n', [N]),
            write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        )
    ).

% -- Unary Nodes --
render_buss_tree(unary_node(Rule, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Binary Nodes --
render_buss_tree(binary_node(Rule, F, TreeA, TreeB)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Ternary Nodes --
render_buss_tree(ternary_node(Rule, HypA, HypB, F, TreeA, TreeB, TreeC)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    render_buss_tree(TreeC),
    format_rule_label(Rule, Label),
    ( Rule = lor ->
        format('\\RightLabel{\\scriptsize{~w} ~w,~w}~n', [Label, HypA, HypB])
    ;
        format('\\RightLabel{\\scriptsize{~w}}~n', [Label])
    ),
    write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Nodes with Discharge (Assumptions) --
% For rcond (->I): check for vacuous discharge
render_buss_tree(discharged_node(rcond, HypNum, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(rcond, BaseLabel),
    % Check if discharge is vacuous (hypothesis doesn't appear in subtree)
    ( tree_contains_assumption(SubTree, HypNum) ->
        % Non-vacuous discharge: show hypothesis number
        format('\\RightLabel{\\scriptsize{~w}  ~w}~n', [BaseLabel, HypNum])
    ;
        % Vacuous discharge: don't show hypothesis number
        format('\\RightLabel{\\scriptsize{~w}}~n', [BaseLabel])
    ),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% For other rules (ip, rall): ALWAYS show hypothesis number (never vacuous)
render_buss_tree(discharged_node(Rule, HypNum, F, SubTree)) :-
    Rule \= rcond,  % Already handled above
    render_buss_tree(SubTree),
    format_rule_label(Rule, BaseLabel),
    % Always indicate the discharged assumption index
    format('\\RightLabel{\\scriptsize{~w}  ~w}~n', [BaseLabel, HypNum]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Special case for exists elimination
render_buss_tree(discharged_node(lex, WitNum, F, ExistTree, GoalTree)) :-
    render_buss_tree(ExistTree),
    render_buss_tree(GoalTree),
    format('\\RightLabel{\\scriptsize{$ \\exists E $ } ~w}~n', [WitNum]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Fallback
render_buss_tree(unknown_node(Just, _, F)) :-
    write('\\AxiomC{?'), write(Just), write('?}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% =========================================================================
% HELPER: RULE LABELS
% =========================================================================
format_rule_label(rcond, '$ \\to I $').
format_rule_label(l0cond, '$ \\to E $').
format_rule_label(ror, '$ \\lor I $').
format_rule_label(lor, '$ \\lor E $').
format_rule_label(land, '$ \\land E $').
format_rule_label(rand, '$ \\land I $').
format_rule_label(lbot, '$ \\bot E $').
format_rule_label(ip, '$ IP $').
format_rule_label(dne_m, '$ DNE_{m} $').
format_rule_label(ds, '$ DS $').
format_rule_label(lex, '$ \\exists E $').
format_rule_label(rex, '$ \\exists I $').
format_rule_label(lall, '$ \\forall E $').
format_rule_label(rall, '$ \\forall I $').
format_rule_label(ltoto, '$ \\to\\to E$').
format_rule_label(landto, '$ \\land\\to E$').
format_rule_label(lorto, '$ \\lor\\to E$').
format_rule_label(cq_c, ' $CQ_c $').
format_rule_label(cq_m, '$ CQ_m $').
format_rule_label(eq_refl, '$ = I $').
format_rule_label(eq_sym, ' Sym ').
format_rule_label(eq_trans, ' Trans ').
format_rule_label(eq_subst, '$ = E $').
format_rule_label(eq_cong, ' Cong ').
format_rule_label(eq_subst_eq, ' SubstEq ').
format_rule_label(X, X). % Fallback

% =========================================================================
% HELPER: WRAPPER FOR REWRITE
% =========================================================================
% Unified: always use write_formula_with_parens for consistent formatting
render_formula_for_buss(Formula) :-
    catch(
        (rewrite(Formula, 0, _, LatexFormula), write_formula_with_parens(LatexFormula)),
        _Error,
        (write('???'))
    ).


all_premisses_used(_, []) :- !.
all_premisses_used(Tree, [P|Ps]) :-
    tree_contains_formula(Tree, P),
    all_premisses_used(Tree, Ps).

% Helper: strip variable annotations
strip_annotations(![_-X]:Body, ![X]:StrippedBody) :-
    !, strip_annotations(Body, StrippedBody).
strip_annotations(?[_-X]:Body, ?[X]:StrippedBody) :-
    !, strip_annotations(Body, StrippedBody).
strip_annotations(A & B, SA & SB) :-
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A | B, SA | SB) :-
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A => B, SA => SB) :-
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A <=> B, SA <=> SB) :-
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(F, F).

% Match with annotation normalization
tree_contains_formula(premiss_node(F), P) :-
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(axiom_node(F), P) :-
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(hypothesis(_, F), P) :-
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(unary_node(_, _, SubTree), F) :-
    tree_contains_formula(SubTree, F).
tree_contains_formula(binary_node(_, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).
tree_contains_formula(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F) ; tree_contains_formula(TreeC, F)).
tree_contains_formula(discharged_node(_, _, _, SubTree), F) :-
    tree_contains_formula(SubTree, F).
tree_contains_formula(discharged_node(_, _, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).

% =========================================================================
% VACUOUS DISCHARGE DETECTION
% =========================================================================
% tree_contains_assumption(+Tree, +HypNum)
% Succeeds if assumption with number HypNum appears in Tree

tree_contains_assumption(assumption_node(_, HypNum), HypNum) :- !.
tree_contains_assumption(assumption_node(_, _), _) :- !, fail.

tree_contains_assumption(reiteration_node(_, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(unary_node(_, _, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(binary_node(_, _, TreeA, TreeB), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ; tree_contains_assumption(TreeB, HypNum)).

tree_contains_assumption(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ;
        tree_contains_assumption(TreeB, HypNum) ;
        tree_contains_assumption(TreeC, HypNum)).

tree_contains_assumption(discharged_node(_, _, _, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(discharged_node(_, _, _, TreeA, TreeB), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ; tree_contains_assumption(TreeB, HypNum)).

tree_contains_assumption(n_ary_premiss_node(_, Trees), HypNum) :-
    !, member(Tree, Trees), tree_contains_assumption(Tree, HypNum).

% Leaves that can't contain assumptions
tree_contains_assumption(axiom_node(_), _) :- !, fail.
tree_contains_assumption(premiss_node(_), _) :- !, fail.
tree_contains_assumption(unknown_node(_, _, _), _) :- !, fail.

%=========================================================================
%   END OF ND TREE STYLE PRINTER
%=========================================================================
% =========================================================================
% CLEAN FITCH STYLE - Dead line elimination
% =========================================================================
% Strategy: After fitch_line/4 facts are generated (silently),
% collect only the lines that are actually referenced,
% renumber them, update justification references, then render.
% =========================================================================
:- dynamic clean_line/4.   % clean_line(NewNum, Formula, NewJust, Scope)
:- dynamic renum/2.           % renum(OldNum, NewNum)

% =========================================================================
% MAIN ENTRY POINT
% =========================================================================
% render_clean_fitch/1: Generate a clean Fitch proof without dead lines.
%
% Strategy:
%   1. Call g4_to_fitch_theorem NORMALLY (it renders AND asserts fitch_line/4)
%      but capture its output to discard it
%   2. The fitch_line/4 facts are now correctly asserted (identical to server)
%   3. Clean: remove dead lines, renumber, re-render
%
% CRITICAL: We do NOT use copy_term here. The Proof term may have been
% partially instantiated by previous renderers (bussproofs, tree style).
% Instead, we let g4_to_fitch_theorem handle its own copy_term internally
% if needed, or we accept that it works on the same term.
% The key insight: g4_to_fitch_theorem asserts fitch_line/4 facts with
% correct Scope values AS A SIDE EFFECT of rendering. We capture and
% discard the rendered output, keeping only the asserted facts.

render_clean_fitch(Proof) :-
    retractall(clean_line(_, _, _, _)),
    retractall(renum(_, _)),

    % Step 1: Let g4_to_fitch_theorem assert fitch_line/4 facts correctly
    % Capture (and discard) its LaTeX output
    with_output_to(atom(_), (
        write('\\begin{fitch}'), nl,
        g4_to_fitch_theorem(Proof),
        write('\\end{fitch}'), nl
    )),

    % Step 2: Find the root line (highest line number = conclusion)
    findall(N, fitch_line(N, _, _, _), AllNums),
    max_list(AllNums, RootLine),

    % Step 3: Collect all lines reachable from root via justifications
    collect_used_lines(RootLine, UsedSet),
    sort(UsedSet, SortedUsed),

    % Step 4: Build renumbering map (old -> new, sequential from 1)
    build_renum_map(SortedUsed, 1),

    % Step 5: Assert clean lines with updated justifications
    forall(
        member(OldNum, SortedUsed),
        (
            fitch_line(OldNum, Formula, Just, Scope),
            renumber_just(Just, NewJust),
            renum(OldNum, NewNum),
            assertz(clean_line(NewNum, Formula, NewJust, Scope))
        )
    ),

    % Step 6: Render clean output
    render_clean_output.

% =========================================================================
% COLLECT USED LINES (recursive traversal from root)
% =========================================================================
% Starting from the root line, follow all justification references
% to collect the transitive closure of used lines.

collect_used_lines(RootLine, UsedSet) :-
    collect_used_acc([RootLine], [], UsedSet).

collect_used_acc([], Acc, Acc).
collect_used_acc([Line|Rest], Acc, Result) :-
    ( member(Line, Acc) ->
        % Already visited
        collect_used_acc(Rest, Acc, Result)
    ; fitch_line(Line, _, Just, _) ->
        % Add this line to accumulator, extract its references
        just_refs(Just, Refs),
        append(Refs, Rest, NewWork),
        collect_used_acc(NewWork, [Line|Acc], Result)
    ;
        % Line not found (shouldn't happen), skip
        collect_used_acc(Rest, Acc, Result)
    ).

% =========================================================================
% EXTRACT LINE REFERENCES FROM JUSTIFICATIONS
% =========================================================================
% For each justification type, return the list of line numbers it references.

% Leaves (no references)
just_refs(premise, []).
just_refs(premiss, []).
just_refs(assumption, []).
just_refs(axiom, []).

% Unary references
just_refs(reiteration(N), [N]).
just_refs(lbot(N), [N]).
just_refs(ror(N), [N]).
just_refs(land(N), [N]).
just_refs(land(N, _Which), [N]).
just_refs(ltoto(N), [N]).
just_refs(landto(N), [N]).
just_refs(lorto(N), [N]).
just_refs(lall(N), [N]).
just_refs(rall(N), [N]).
just_refs(rex(N), [N]).
just_refs(cq_c(N), [N]).
just_refs(cq_m(N), [N]).

% Binary references
just_refs(l0cond(N1, N2), [N1, N2]).
% rcond(HypLine, GoalLine): the GoalLine's justification will pull in
% what it needs transitively. We must also include HypLine (assumption).
just_refs(rcond(N1, N2), [N1, N2]).
just_refs(rand(N1, N2), [N1, N2]).
just_refs(ds(N1, N2), [N1, N2]).
just_refs(ip(N1, N2), [N1, N2]).

% Ternary+ references
just_refs(lex(ExistLine, WitLine, GoalLine), [ExistLine, WitLine, GoalLine]).

just_refs(lor(DisjLine, AssA, EndA, AssB, EndB),
          [DisjLine, AssA, EndA, AssB, EndB]).

% Fallback: try to extract numeric arguments
just_refs(Just, Refs) :-
    nonvar(Just),
    Just =.. [_|Args],
    include(integer, Args, Refs).
% Ultimate fallback: no references
just_refs(_, []).

% =========================================================================
% BUILD RENUMBERING MAP
% =========================================================================
build_renum_map([], _).
build_renum_map([Old|Rest], New) :-
    assertz(renum(Old, New)),
    New1 is New + 1,
    build_renum_map(Rest, New1).

% =========================================================================
% RENUMBER JUSTIFICATIONS
% =========================================================================
% Replace all old line numbers with new ones in justifications.

renumber_just(premise, premise).
renumber_just(premiss, premiss).
renumber_just(assumption, assumption).
renumber_just(axiom, axiom).

renumber_just(reiteration(N), reiteration(N1)) :- rn(N, N1).
renumber_just(lbot(N), lbot(N1)) :- rn(N, N1).
renumber_just(ror(N), ror(N1)) :- rn(N, N1).
renumber_just(land(N), land(N1)) :- rn(N, N1).
renumber_just(land(N, W), land(N1, W)) :- rn(N, N1).
renumber_just(ltoto(N), ltoto(N1)) :- rn(N, N1).
renumber_just(landto(N), landto(N1)) :- rn(N, N1).
renumber_just(lorto(N), lorto(N1)) :- rn(N, N1).
renumber_just(lall(N), lall(N1)) :- rn(N, N1).
renumber_just(rall(N), rall(N1)) :- rn(N, N1).
renumber_just(rex(N), rex(N1)) :- rn(N, N1).
renumber_just(cq_c(N), cq_c(N1)) :- rn(N, N1).
renumber_just(cq_m(N), cq_m(N1)) :- rn(N, N1).

renumber_just(l0cond(N1, N2), l0cond(M1, M2)) :- rn(N1, M1), rn(N2, M2).
renumber_just(rcond(N1, N2), rcond(M1, M2)) :- rn(N1, M1), rn(N2, M2).
renumber_just(rand(N1, N2), rand(M1, M2)) :- rn(N1, M1), rn(N2, M2).
renumber_just(ds(N1, N2), ds(M1, M2)) :- rn(N1, M1), rn(N2, M2).
renumber_just(ip(N1, N2), ip(M1, M2)) :- rn(N1, M1), rn(N2, M2).

renumber_just(lex(N1, N2, N3), lex(M1, M2, M3)) :- rn(N1, M1), rn(N2, M2), rn(N3, M3).
renumber_just(lor(N1, N2, N3, N4, N5), lor(M1, M2, M3, M4, M5)) :-
    rn(N1, M1), rn(N2, M2), rn(N3, M3), rn(N4, M4), rn(N5, M5).

% Fallback: keep as-is
renumber_just(X, X).

% Helper: renumber with fallback
rn(Old, New) :- renum(Old, New), !.
rn(X, X).  % fallback: keep unchanged if not in map

% =========================================================================
% RENDER CLEAN FITCH OUTPUT
% Uses the LaTeX lines captured during pass 1 (fitch_line_latex/2).
% For each live line, keeps the formula part (before &) from pass 1
% and only replaces the justification part (after &) with renumbered refs.
% =========================================================================
render_clean_output :-
    write('\\begin{fitch}'), nl,
    findall(N, clean_line(N, _, _, _), AllNums),
    sort(AllNums, Sorted),
    render_clean_lines(Sorted),
    write('\\end{fitch}'), nl.

render_clean_lines([]).
render_clean_lines([N|Rest]) :-
    clean_line(N, _, Just, _),
    renum(OldN, N),
    ( fitch_line_latex(OldN, LatexLine) ->
        atom_string(LatexLine, LatexStr),
        ( split_on_ampersand(LatexStr, FormulaPart, _) ->
            write(FormulaPart),
            write(' &  '),
            ( Just = assumption -> write('AS')
            ; Just = premise -> write('PR')
            ; Just = premiss -> write('PR')
            ; render_clean_just(Just)
            ),
            write('\\\\'), nl
        ;
            write(LatexLine)
        )
    ;
        write('% ERROR: missing fitch_line_latex for line '), write(OldN), nl
    ),
    render_clean_lines(Rest).

% Split a string on the first occurrence of ' & '
split_on_ampersand(Str, Before, After) :-
    sub_string(Str, Pos, 3, _, " & "),
    !,
    sub_string(Str, 0, Pos, _, Before),
    Pos3 is Pos + 3,
    sub_string(Str, Pos3, _, 0, After).

% =========================================================================
% RENDER JUSTIFICATIONS WITH NEW LINE NUMBERS
% =========================================================================
render_clean_just(reiteration(N)) :-
    format(' R ~w', [N]).
render_clean_just(l0cond(Maj, Min)) :-
    format(' $ \\to E $ ~w,~w', [Maj, Min]).
render_clean_just(lbot(N)) :-
    format(' $ \\bot E $ ~w', [N]).
render_clean_just(ror(N)) :-
    format(' $ \\lor I $ ~w', [N]).
render_clean_just(land(N)) :-
    format(' $ \\land E $ ~w', [N]).
render_clean_just(land(N, _)) :-
    format(' $ \\land E $ ~w', [N]).
render_clean_just(rand(N1, N2)) :-
    format(' $ \\land I $ ~w,~w', [N1, N2]).
render_clean_just(rcond(Hyp, Goal)) :-
    format(' $ \\to I $ ~w-~w', [Hyp, Goal]).
render_clean_just(ip(Hyp, Bot)) :-
    ( clean_line(Hyp, ((_ => #) => #), _, _) ->
        format(' DNE_m ~w-~w', [Hyp, Bot])
    ;
        format(' IP ~w-~w', [Hyp, Bot])
    ).
render_clean_just(ds(Disj, Neg)) :-
    format(' $ DS $ ~w,~w', [Disj, Neg]).
render_clean_just(lor(Disj, AssA, GoalA, AssB, GoalB)) :-
    format(' $ \\lor E $ ~w,~w-~w,~w-~w', [Disj, AssA, GoalA, AssB, GoalB]).
render_clean_just(ltoto(N)) :-
    format('$ \\to \\to E $ ~w', [N]).
render_clean_just(landto(N)) :-
    format('$ \\land \\to E $ ~w', [N]).
render_clean_just(lorto(N)) :-
    format('$ \\lor \\to E $ ~w', [N]).
render_clean_just(lall(N)) :-
    format(' $ \\forall E $ ~w', [N]).
render_clean_just(rall(N)) :-
    format(' $ \\forall I $ ~w', [N]).
render_clean_just(rex(N)) :-
    format(' $ \\exists I $ ~w', [N]).
render_clean_just(lex(Exist, Wit, Goal)) :-
    format(' $ \\exists E $ ~w,~w-~w', [Exist, Wit, Goal]).
render_clean_just(cq_c(N)) :-
    format(' $ CQ_{c} $ ~w', [N]).
render_clean_just(cq_m(N)) :-
    format(' $ CQ_{m} $ ~w', [N]).

% Fallback
render_clean_just(Just) :-
    format(' ~w', [Just]).

% =========================================================================
% END OF CLEAN FITCH MODULE
% =========================================================================
% =========================================================================
% TPTP FORMAT SUPPORT
% =========================================================================
% G4-mic uses lowercase-only syntax, while TPTP uses uppercase for variables.
% This module converts TPTP formulas to G4-mic syntax.

% Read and process a TPTP file
prove_tptp_file(Filename) :-
    open(Filename, read, Stream),
    read_tptp_formulas(Stream, Formulas),
    close(Stream),
    ( process_tptp_formulas(Formulas) -> true ; true ).

% Read all fof() declarations from file
read_tptp_formulas(Stream, Formulas) :-
    \+ at_end_of_stream(Stream),
    read(Stream, Term),
    !,
    (   Term = fof(_, _, _) ->
        Formulas = [Term|Rest],
        read_tptp_formulas(Stream, Rest)
    ;   % Skip non-fof terms (comments, etc.)
        read_tptp_formulas(Stream, Formulas)
    ).
read_tptp_formulas(_, []).

% Process list of TPTP formulas - collect axioms and combine with conjecture
process_tptp_formulas(Formulas) :-
    process_tptp_formulas(Formulas, []).

% process_tptp_formulas(Formulas, AccumulatedAxioms)
%
% No conjecture found: test satisfiability of the axiom set.
% SZS Unsatisfiable if axioms are inconsistent, SZS Satisfiable otherwise.
process_tptp_formulas([], Axioms) :-
    (   Axioms \= [] ->
        length(Axioms, NumAxioms),
        format('~nSatisfiability check: ~w axiom(s) without conjecture~n', [NumAxioms]),
        maplist(convert_axiom_formula, Axioms, G4micAxioms),
        combine_axioms(G4micAxioms, Combined),
        NegCombined = (Combined => #),
        ( prove_tptp_internal(NegCombined, no_conjecture) -> true ; true )
    ;   true
    ).

process_tptp_formulas([fof(Name, Role, Formula)|Rest], AccAxioms) :-
    (   Role = axiom ->
        % Accumulate axiom for later combination with conjecture
        process_tptp_formulas(Rest, [fof(Name, axiom, Formula)|AccAxioms])

    ;   Role = conjecture ->
        % Found conjecture - combine with accumulated axioms
        nl,
        format('===============================================================~n', []),
        (   AccAxioms = [] ->
            format('TPTP Problem: ~w (conjecture, no axioms)~n', [Name])
        ;   length(AccAxioms, NumAxioms),
            format('TPTP Problem: ~w (conjecture with ~w axiom(s))~n', [Name, NumAxioms]),
            % Display axiom names
            extract_axiom_names(AccAxioms, AxiomNames),
            format('  Axioms: ~w~n', [AxiomNames])
        ),
        format('===============================================================~n', []),
        nl,

        % Convert all formulas (axioms and conjecture)
        convert_tptp_formula(Formula, G4micConjecture),
        maplist(convert_axiom_formula, AccAxioms, G4micAxioms),

        % Combine: (axiom1 & axiom2 & ...) => conjecture
        (   G4micAxioms = [] ->
            % No axioms - just prove conjecture
            CombinedFormula = G4micConjecture
        ;   % Combine axioms with &
            combine_axioms(G4micAxioms, CombinedAxioms),
            CombinedFormula = (CombinedAxioms => G4micConjecture),
            length(G4micAxioms, NumAx),
            format('Combined formula: ~w axiom(s) => conjecture~n~n', [NumAx])
        ),

        % Prove the combined formula - SZS: Theorem / CounterSatisfiable
        ( prove_tptp_internal(CombinedFormula, has_conjecture) -> true ; true ),

        % Clear accumulated axioms and continue
        process_tptp_formulas(Rest, [])

    ;   % Unknown role - skip
        format('Skipping ~w with role ~w~n', [Name, Role]),
        process_tptp_formulas(Rest, AccAxioms)
    ).

% Convert a single TPTP formula to G4-mic syntax
convert_tptp_formula(Formula, G4micFormula) :-
    copy_term(Formula, FormulaCopy),
    numbervars(FormulaCopy, 0, _),
    with_output_to(string(FormulaStr), write_canonical(FormulaCopy)),
    string_chars(FormulaStr, Chars),
    maplist(char_downcase, Chars, LowerChars),
    string_chars(LowerStr, LowerChars),
    read_term_from_atom(LowerStr, G4micFormula_temp, []),
    simplify_var_names(G4micFormula_temp, G4micFormula_simplified),
    expand_multi_var_quantifiers(G4micFormula_simplified, G4micFormula).

% Convert an axiom (extract formula from fof wrapper)
convert_axiom_formula(fof(_, axiom, Formula), G4micFormula) :-
    convert_tptp_formula(Formula, G4micFormula).

% Combine multiple axioms with &
combine_axioms([A], A) :- !.
combine_axioms([A|Rest], (A & RestCombined)) :-
    combine_axioms(Rest, RestCombined).

% Extract axiom names from fof list
extract_axiom_names([], []).
extract_axiom_names([fof(Name, _, _)|Rest], [Name|Names]) :-
    extract_axiom_names(Rest, Names).

% Expand multi-variable quantifiers ONLY: ![v0,v1]: -> ![v0]:![v1]:
% G4-mic's prepare() handles the binding, we just need to unnest lists
expand_multi_var_quantifiers(!(Expr), Result) :-
    Expr = (VarList:Body),
    is_list(VarList),
    VarList = [_,_|_],  % At least 2 elements
    !,
    expand_multi_forall(VarList, Body, Result).

expand_multi_var_quantifiers(?(Expr), Result) :-
    Expr = (VarList:Body),
    is_list(VarList),
    VarList = [_,_|_],  % At least 2 elements
    !,
    expand_multi_exists(VarList, Body, Result).

expand_multi_var_quantifiers(A & B, NewA & NewB) :- !,
    expand_multi_var_quantifiers(A, NewA),
    expand_multi_var_quantifiers(B, NewB).

expand_multi_var_quantifiers(A | B, NewA | NewB) :- !,
    expand_multi_var_quantifiers(A, NewA),
    expand_multi_var_quantifiers(B, NewB).

expand_multi_var_quantifiers(A => B, NewA => NewB) :- !,
    expand_multi_var_quantifiers(A, NewA),
    expand_multi_var_quantifiers(B, NewB).

expand_multi_var_quantifiers(A <=> B, NewA <=> NewB) :- !,
    expand_multi_var_quantifiers(A, NewA),
    expand_multi_var_quantifiers(B, NewB).

expand_multi_var_quantifiers(~A, ~NewA) :- !,
    expand_multi_var_quantifiers(A, NewA).

expand_multi_var_quantifiers(Term, Term).

% Expand ![v0,v1,v2]: Body into ![v0]:![v1]:![v2]: Body
expand_multi_forall([Var], Body, ![Var]:NewBody) :- !,
    expand_multi_var_quantifiers(Body, NewBody).
expand_multi_forall([Var|Rest], Body, ![Var]:RestResult) :-
    expand_multi_forall(Rest, Body, RestResult).

% Expand ?[v0,v1,v2]: Body into ?[v0]:?[v1]:?[v2]: Body
expand_multi_exists([Var], Body, ?[Var]:NewBody) :- !,
    expand_multi_var_quantifiers(Body, NewBody).
expand_multi_exists([Var|Rest], Body, ?[Var]:RestResult) :-
    expand_multi_exists(Rest, Body, RestResult).

% Simplify $var(N) to vN throughout the formula
% G4-mic's prepare() will then bind these to Prolog variables
simplify_var_names(Term, Simple) :-
    (   Term = '$var'(N) ->
        xyz_name(N, Simple)  % Use x,y,z instead of v0,v1,v2
    ;   atomic(Term) ->
        Simple = Term
    ;   compound(Term) ->
        Term =.. [F|Args],
        maplist(simplify_var_names, Args, SimpleArgs),
        Simple =.. [F|SimpleArgs]
    ;   Simple = Term
    ).

% Helper to convert character to lowercase
char_downcase(C, L) :-
    (   char_type(C, upper(L)) -> true
    ;   L = C
    ).

% Removed: expand_quantifier_lists(!(VarTerm:Body), ...)
% This clause was matching before the list-handling clause and causing bugs

% Removed: expand_quantifier_lists(?(VarTerm:Body), ...)
% This clause was matching before the list-handling clause and causing bugs

% PRIMARY PATTERN - handles all cases including lists
% Expand multi-variable quantifiers: ![x,y]: -> ![x]:![y]:
% CRITICAL: ![a,b]:Body is parsed as !([a,b]:Body) due to operator precedence
expand_quantifier_lists(!(Expr), Result) :-
    Expr = (VarTerm:Body),
    !,
    (   is_list(VarTerm) ->
        % True list: [a,b,c] or [a]
        (   VarTerm = [_|_] ->
            (   VarTerm = [SingleVar] ->
                % Single element list - common from TPTP ![X]:
                format('DEBUG: Single var list [~w], recursing on body~n', [SingleVar]),
                expand_quantifier_lists(Body, NewBody),
                % Construct !(SingleVar:NewBody) explicitly
                NewExpr = (SingleVar:NewBody),
                Result =.. ['!', NewExpr]
            ;   % Multiple elements
                expand_forall_list(VarTerm, Body, Result)
            )
        ;   expand_quantifier_lists(Body, NewBody),
            Result = (![VarTerm]:NewBody)
        )
    ;   compound(VarTerm), functor(VarTerm, ',', 2) ->
        % Comma operator: a,b parsed as ','(a,b)
        comma_to_list(VarTerm, VarList),
        expand_forall_list(VarList, Body, Result)
    ;   % Single variable (not in list)
        expand_quantifier_lists(Body, NewBody),
        Result = (![VarTerm]:NewBody)
    ).

% Same for existential
expand_quantifier_lists(?(Expr), Result) :-
    Expr = (VarTerm:Body),
    !,
    (   is_list(VarTerm), VarTerm = [_|_] ->
        (   VarTerm = [SingleVar] ->
            % Single element list - common from TPTP ?[X]:
            expand_quantifier_lists(Body, NewBody),
            % Construct ?(SingleVar:NewBody) explicitly
            NewExpr = (SingleVar:NewBody),
            Result =.. ['?', NewExpr]
        ;   % Multiple elements
            expand_exists_list(VarTerm, Body, Result)
        )
    ;   compound(VarTerm), functor(VarTerm, ',', 2) ->
        comma_to_list(VarTerm, VarList),
        expand_exists_list(VarList, Body, Result)
    ;   expand_quantifier_lists(Body, NewBody),
        Result = (?[VarTerm]:NewBody)
    ).

% OLD PATTERN kept for backward compatibility
expand_quantifier_lists(![VarTerm]:Body, Result) :-
    (   is_list(VarTerm) ->
        % True list: [a,b,c]
        (   VarTerm = [_|_] ->
            expand_forall_list(VarTerm, Body, Result)
        ;   Result = (![VarTerm]:Body)
        )
    ;   compound(VarTerm), functor(VarTerm, ',', 2) ->
        % Comma operator: a,b parsed as ','(a,b)
        comma_to_list(VarTerm, VarList),
        expand_forall_list(VarList, Body, Result)
    ;   % Single variable
        !, expand_quantifier_lists(Body, NewBody),
        Result = (![VarTerm]:NewBody)
    ).

expand_quantifier_lists(?[VarList]:Body, Result) :-
    is_list(VarList), VarList = [_|_], !,
    expand_exists_list(VarList, Body, Result).

expand_quantifier_lists(![Var]:Body, ![Var]:NewBody) :- !,
    expand_quantifier_lists(Body, NewBody).

expand_quantifier_lists(?[Var]:Body, ?[Var]:NewBody) :- !,
    expand_quantifier_lists(Body, NewBody).

expand_quantifier_lists(A & B, NewA & NewB) :- !,
    expand_quantifier_lists(A, NewA),
    expand_quantifier_lists(B, NewB).

expand_quantifier_lists(A | B, NewA | NewB) :- !,
    expand_quantifier_lists(A, NewA),
    expand_quantifier_lists(B, NewB).

expand_quantifier_lists(A => B, NewA => NewB) :- !,
    expand_quantifier_lists(A, NewA),
    expand_quantifier_lists(B, NewB).

expand_quantifier_lists(A <=> B, NewA <=> NewB) :- !,
    expand_quantifier_lists(A, NewA),
    expand_quantifier_lists(B, NewB).

expand_quantifier_lists(~A, ~NewA) :- !,
    expand_quantifier_lists(A, NewA).

expand_quantifier_lists(A = B, A = B) :- !.

% Removed CATCH-ALL for debugging - it was blocking the generic clause below

expand_quantifier_lists(Term, NewTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(expand_quantifier_lists, Args, NewArgs),
    NewTerm =.. [F|NewArgs].

expand_quantifier_lists(Atom, Atom).

% Expand ![x,y,z]: Body into ![x]:![y]:![z]: Body
expand_forall_list([Var], Body, Result) :- !,
    expand_quantifier_lists(Body, NewBody),
    % Construct !(Var:NewBody) explicitly to avoid operator precedence issues
    Expr = (Var:NewBody),
    Result =.. ['!', Expr].
expand_forall_list([Var|Rest], Body, Result) :-
    expand_forall_list(Rest, Body, RestResult),
    % Construct !(Var:RestResult) explicitly
    Expr = (Var:RestResult),
    Result =.. ['!', Expr].

% Expand ?[x,y,z]: Body into ?[x]:?[y]:?[z]: Body
expand_exists_list([Var], Body, Result) :- !,
    expand_quantifier_lists(Body, NewBody),
    % Construct ?(Var:NewBody) explicitly to avoid operator precedence issues
    Expr = (Var:NewBody),
    Result =.. ['?', Expr].
expand_exists_list([Var|Rest], Body, Result) :-
    expand_exists_list(Rest, Body, RestResult),
    % Construct ?(Var:RestResult) explicitly
    Expr = (Var:RestResult),
    Result =.. ['?', Expr].

% Convert comma operator to list: ','(a,','(b,c)) -> [a,b,c]
comma_to_list((A,B), [A|Rest]) :-
    !,
    comma_to_list(B, Rest).
comma_to_list(A, [A]).
xyz_name(N, Name) :-
    Base is N mod 3,
    Suffix is N div 3,
    nth0(Base, [x, y, z], BaseName),
    (   Suffix = 0 ->
        Name = BaseName
    ;   atom_concat(BaseName, Suffix, Name)
    ).

% Convert TPTP formula to G4-mic using string conversion
% This is more reliable than trying to manipulate the term structure

% =========================================================================
% SZS STATUS MAPPING
% =========================================================================
% With conjecture:    proved => Theorem,       not proved => CounterSatisfiable
% Without conjecture: proved => Unsatisfiable, not proved => Satisfiable

szs_status(has_conjecture, proved,    theorem).
szs_status(has_conjecture, disproved, 'CounterSatisfiable').
szs_status(no_conjecture,  proved,    unsatisfiable).
szs_status(no_conjecture,  disproved, satisfiable).

% Backward-compatible wrapper (called from prove_tptp/1 and elsewhere)
prove_tptp_internal(Formula) :-
    prove_tptp_internal(Formula, has_conjecture).

% Direct TPTP formula entry (for testing)
prove_tptp(fof(Name, Role, Formula)) :-
    nl,
    format('===============================================================~n', []),
    format('TPTP: ~w (~w)~n', [Name, Role]),
    format('===============================================================~n', []),
    nl,
    convert_tptp_formula(Formula, G4micFormula),
    format('Converted to G4-mic: ~w~n~n', [G4micFormula]),
    % Skip validate_and_warn for TPTP - it gives false positives on ![x]: syntax
    prove_tptp_internal(G4micFormula, has_conjecture).

% Internal prove for TPTP (bypasses validate_and_warn)
% Case 1: equality/functions detected - delegate to nanoCoP
prove_tptp_internal(Formula, ProblemType) :-
    % Check if needs nanoCoP (equality/functions)
    g4mic_needs_nanocop(Formula),
    !,
    nl,
    write('[ Equality/functions detected -- routing to nanoCoP ]'), nl,
    nl,
    write('Calling nanoCoP...'), nl, nl,
    ( nanocop_proves(Formula) ->
      szs_status(ProblemType, proved, SZSStatus),
      format('% SZS status ~w~n', [SZSStatus]),
      write('Q.E.D.'), nl, nl
    ;
      szs_status(ProblemType, disproved, SZSStatus),
      format('% SZS status ~w~n', [SZSStatus]),
      fail
    ).

% Case 2a: no conjecture - test unsatisfiability, output proof if found
prove_tptp_internal(Formula, no_conjecture) :-
    !,
    ( catch(
          call_with_inference_limit(nanocop_decides(Formula), 2000000, _),
          _,
          fail
      ) ->
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
          fail
      ),
      statistics(walltime, [End|_]),
      Time is (End - Start) / 1000,
      nl,
      format('G4mic time: ~3f seconds~n', [Time]),
      nl,
      write('% SZS status Unsatisfiable'), nl,
      nl,
      output_proof_results(OutputProof, Logic, Formula)
    ;
      write('% SZS status Satisfiable'), nl
    ).

% Case 2b: has conjecture - full g4mic proof flow
prove_tptp_internal(Formula, has_conjecture) :-
    current_prolog_flag(occurs_check, OriginalFlag),
    ( catch(
          setup_call_cleanup(
              true,
              call_with_inference_limit(nanocop_decides(Formula), 2000000, _),
              set_prolog_flag(occurs_check, OriginalFlag)
          ),
          _,
          (set_prolog_flag(occurs_check, OriginalFlag), fail)
      ) ->
      true
    ;
    szs_disproved_status(Formula, DisprStatus2),
    format('% SZS status ~w~n', [DisprStatus2]), !, fail
    ),

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
    write('% SZS status Theorem'), nl,
    nl,
    output_proof_results(OutputProof, Logic, Formula),
    % Validation phase
    nl,
    write('--- Validation ---'), nl,
    nl,
    write('g4mic_decides:   '),
    ( catch(g4mic_decides(Formula), _, fail) ->
        write('true'), nl,
        G4micResult = valid
    ;
        write('false'), nl,
        G4micResult = invalid
    ),
    write('nanocop_decides: '),
    ( catch(time(nanocop_decides(Formula)), _, fail) ->
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
    nl.

% =========================================================================
% UTILITY: AUTO-SUGGESTION (optional feature)
% =========================================================================
%%% END OF g4mic PROVER

% Determine SZS status for a formula that failed to prove.
% If ~F is provable (i.e. F is a contradiction), status is 'Unsatisfiable'.
% Otherwise F is coherent but not valid: status is 'CounterSatisfiable'.
szs_disproved_status(Formula, Status) :-
    ( catch(
          call_with_inference_limit(nanocop_decides(~Formula), 2000000, _),
          _,
          fail
      ) ->
      Status = 'Unsatisfiable'
    ;
      Status = 'CounterSatisfiable'
    ).
