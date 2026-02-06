% =========================================================================
% OPERATOR DECLARATIONS - Unified for g4mic + nanocop + TPTP
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- [i_operators].
:- [ii_minimal_driver].  % To translate nanocop into g4mic and to  use nanocop as filter
:- [iii_prover].
:- [iv_printer_sc].
:- [v_common_nd].
:- [vi_flag_style].
:- [vii_tree_style].
:- [viii_latex].
:- [ix_detections].
:- [x_tptp].
% =======================================================================================================================
% NANOCOP WRAPPER - (nanocop as Filter: a formula that is invalid according to nanocop is not submitted to g4mic)
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

% Analyze and display nanoCoP refutation
nanocop_refutation_analysis(Formula) :-
    nl,
    write('❌ INVALID (nanoCoP).'), nl,

    % Build the matrix
    translate_formula(Formula, InternalFormula),
    Problem1 = (~InternalFormula),
    leancop_equal(Problem1, Problem2),

    % Try to prove (will fail)
    \+ prove2(Problem2, [cut,comp(7)], _Proof),

    % Display the matrix
    bmatrix(Problem2, [cut,comp(7)], Matrix),
    write(' === RAW MATRIX CONSTRUCTION ==='), nl,
    write('    '), portray_clause(Matrix), nl, nl,

    % Analyze open path (counter-model)
    extract_open_path(Matrix, OpenPath),
    write(' === RAW OPEN PATH ==='), nl,
    write('    '), portray_clause(OpenPath), nl, nl,

    % Display premises for refutation
    write(' 🎯 PREMISS FOR REFUTATION :'), nl, nl,
    extract_and_display_assignments(OpenPath),
    nl.

% Extract an open path from the matrix
extract_open_path(Matrix, OpenPath) :-
    findall(Lit, (member((_^_)^_: Literals, Matrix), member(Lit, Literals)), AllLits),
    include(is_negative_literal, AllLits, OpenPath).

is_negative_literal(- _).
is_negative_literal((_ => #)).

% Extract and display assignments
extract_and_display_assignments(OpenPath) :-
    findall(Atom=Value, literal_to_assignment(OpenPath, Atom, Value), Assignments),
    ( Assignments \= [] ->
        forall(member(A=V, Assignments),
               format('     ~w = ~w~n', [A, V]))
    ;
        write('     (no direct assignments found)'), nl
    ).

% Convert a literal to an assignment
literal_to_assignment([- A|_], A, '⊤') :- atomic(A), !.
literal_to_assignment([(A => #)|_], A, '⊤') :- atomic(A), !.
literal_to_assignment([_|Rest], Atom, Value) :-
    literal_to_assignment(Rest, Atom, Value).
% =========================================================================
% STARTUP BANNER
% =========================================================================
% Disable automatic SWI-Prolog banner
:- set_prolog_flag(verbose, silent).

%
:- initialization(show_banner).

show_banner :-
    current_prolog_flag(version_data, swi(Major, Minor, Patch, _)),
   format('Welcome to ~w (32 bits, version ~w.~w.~w)~n',
       ['\e]8;;https://www.swi-prolog.org\e\\SWI-Prolog\e]8;;\e\\',
        Major, Minor, Patch]),
    write('╔═══════════════════════════════════════════════════════════════════╗'), nl,
    write('║                                                                   ║'), nl,
    write('🎓🎓🎓                     𝐆𝟒+                                 🎓🎓🎓'), nl,
    write('🎓🎓🎓    A Unified Prover for Minimal, Intuitionistic and     🎓🎓🎓'), nl,
    write('🎓🎓🎓       Classical First-Order Logic (G4 + nanoCoP)        🎓🎓🎓'), nl,
    write('║                                                                   ║'), nl,
    write('╠═══════════════════════════════════════════════════════════════════╣'), nl,
    write('║                                                                   ║'), nl,
    write('⚠️⚠️   Your formula MUST follow the correct syntax (type help.)  ⚠️⚠️ '), nl,
    write('║                                                                   ║'), nl,
    write('╠═══════════════════════════════════════════════════════════════════╣'), nl,
    write('║                                                                   ║'), nl,
    write('║   📝  Usage:                                                      ║'), nl,
    write('║     • prove(Formula).          → proof in 3 styles + validation   ║'), nl,
    write('║     • decide(Formula)          → concise mode                     ║'), nl,
    write('║     • prove_tptp(fof(...)).    → TPTP format support              ║'), nl,
    write('║     • prove_tptp_file(File).   → process TPTP .p file             ║'), nl,
    write('║     • nanocop_proves(Formula)  → nanoCoP only - verbose mode      ║'), nl,
    write('║     • nanocop_decides(Formula) → nanoCoP only - concise mode      ║'), nl,
    write('║     • help.                    → show detailed help               ║'), nl,
    write('║     • examples.                → show formula examples            ║'), nl,
    write('║                                                                   ║'), nl,
    write('║   💡  Remember: End each request with a dot!                      ║'), nl,
    write('║                                                                   ║'), nl,
    write('╚═══════════════════════════════════════════════════════════════════╝'), nl,
    nl.

% =========================================================================
% ITERATION LIMITS CONFIGURATION  (DO NOT CHANGE THESE VALUES !)
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 4).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 3).
logic_iteration_limit(fol, 4).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% THEOREM vs SEQUENT DETECTION (simplified)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.
:- dynamic current_logic_level/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
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

% NEW: Automatic detection for sequents with premisses
prove(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
     %  VALIDATION: Verify premisses and conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent '), nl,
    nl,

    % Store premisses for display
    retractall(premiss_list(_)),
    % Prepare formulas BEFORE storing premisses
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    % Store PREPARED premisses (with ~z transformed to z => #)
    assertz(premiss_list(PrepG)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),

    % Detect classical pattern in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('              🔍 CLASSICAL PATTERN DETECTED                '), nl,
        write('                  → Using classical logic                  '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('   🔄 PHASE 1: Minimal → Intuitionistic → Classical        '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   ✅ Constructive proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   ✅ Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('   ⚠️  Constructive logic failed'), nl,
            write('┌─────────────────────────────────────────────────────────┐'), nl,
            write('              🎯 TRYING CLASSICAL LOGIC                    '), nl,
            write('└─────────────────────────────────────────────────────────┘'), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            !,  % Cut here to prevent backtracking
            write('    Proof found in CLASSICAL LOGIC '), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).


% =========================================================================
% BICONDITIONAL - Complete corrected section (grouped by proof style)
% =========================================================================

prove(Left <=> Right) :-
    % EQUALITY OR FUNCTIONS: ROUTE TO NANOCOP (EXCLUSIVE)
    g4mic_needs_nanocop(Left <=> Right),
    !,

    nl,
    write('╔═══════════════════════════════════════════════════════════╗'), nl,
    write('    🔍 EQUALITY/FUNCTIONS DETECTED → USING NANOCOP ENGINE    '), nl,
    write('╚═══════════════════════════════════════════════════════════╝'), nl,
    nl,

    validate_and_warn(Left <=> Right, _),

    write('🔄 Calling nanoCoP prover...'), nl, nl,

    % DIRECT CALL to nanocop_proves/1 - THAT'S ALL!
    nanocop_proves(Left <=> Right),

    write('═══════════════════════════════════════════════════════════════'), nl,
    write('✅ Q.E.D.  '), nl, nl,!.

%  ALTERNATIVE Clause - no equality/functions: g4mic

prove(Left <=> Right) :-
    \+ g4mic_needs_nanocop(Left <=> Right),  % Exclude equality and functions
    validate_and_warn(Left <=> Right, _ValidatedFormula),
    % Check if user meant sequent equivalence (<>) instead of biconditional (<=>)
    ( (is_list(Left) ; is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('   ⚠️  SYNTAX ERROR: <=> used with sequents                      '), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: prove('), write(Left <=> Right), write(')'), nl,
        nl,
        write('❌ WRONG:   <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: prove(p <=> q)'), nl,
        nl,
        write('✅ CORRECT: <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: decide([p] <> [q])'), nl,
        nl,
        write('Note: For sequent equivalence, use decide/1, not prove/1'), nl,
        nl,
        fail
    ;
        % ═══════════════════════════════════════════════════════════════
        % FILTRE NANOCOP (comme prove(Formula))
        % ═══════════════════════════════════════════════════════════════
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
        nl, !, fail
        ),

        % ═══════════════════════════════════════════════════════════════
        % PHASE 1 & 2: g4mic PROOF SEARCH (both directions)
        % ═══════════════════════════════════════════════════════════════
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
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('           ↔️  BICONDITIONAL:  Proving Both Directions           '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl, nl,

        % ═══════════════════════════════════════════════════════════════
        % SEQUENT CALCULUS (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('📐 Sequent Calculus Proofs'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - Sequent
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                ➡️   DIRECTION 1                                '), nl,
        write('           '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true ->
            output_logic_label(Logic1), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('✅ Q. E.D. '), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % Direction 2 - Sequent
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                    ⬅️   DIRECTION 2                            '), nl,
        write('               '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true ->
            output_logic_label(Logic2), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('✅ Q.E.D.'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % NATURAL DEDUCTION - TREE STYLE (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🌳 Natural Deduction - Tree Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - ND Tree
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                     ➡️   DIRECTION 1                            '), nl,
        write('                '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true ->
            render_nd_tree_proof(Proof1), nl, nl,
            write('✅ Q.E.D. '), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % Direction 2 - ND Tree
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                   ⬅️   DIRECTION 2                              '), nl,
        write('                 '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true ->
            render_nd_tree_proof(Proof2), nl, nl,
            write('✅ Q.E.D.'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % NATURAL DEDUCTION - FITCH STYLE (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🚩 Natural Deduction - Flag Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - Fitch
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                     ➡️   DIRECTION 1                           '), nl,
        write('                '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true ->
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof1),
            write('\\end{fitch}'), nl, nl,
            write('✅ Q. E.D.'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % Direction 2 - Fitch
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('              ⬅️   DIRECTION 2                                   '), nl,
        write('             '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true ->
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof2),
            write('\\end{fitch}'), nl, nl,
            write('✅ Q.E.D. '), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % SUMMARY
        % ═══════════════════════════════════════════════════════════════
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('                          📊 SUMMARY                             '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl,
        write('Direction 1 ('), write(Left => Right), write('): '),
        ( Direction1Valid = true ->
            write('✅ VALID in '), write(Logic1), write(' logic')
        ; write('⚠️  FAILED')
        ), nl,
        write('Direction 2 ('), write(Right => Left), write('): '),
        ( Direction2Valid = true ->
            write('✅ VALID in '), write(Logic2), write(' logic')
        ; write('⚠️  FAILED')
        ), nl, nl,

        % ═══════════════════════════════════════════════════════════════
        % PHASE 3: EXTERNAL VALIDATION (g4mic FIRST, THEN NANOCOP)
        % ═══════════════════════════════════════════════════════════════
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('                  🔍 PHASE 3: VALIDATION                         '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl,
        nl,

        % g4mic VALIDATION (PRIMARY PROVER)
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('🔍 g4mic_decides output'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( catch(g4mic_decides(Left <=> Right), _, fail) ->
            write('true.'), nl,
            G4micResult = valid
        ;
            write('false.'), nl,
            G4micResult = invalid
        ),
        nl,

        % NANOCOP VALIDATION (EXTERNAL VALIDATION)
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('🔍 nanocop_decides output'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( catch(time(nanocop_decides(Left <=> Right)), _, fail) ->
            write('true. '), nl,
            NanoCopResult = valid
        ;
            write('false.'), nl,
            NanoCopResult = invalid
        ),
        nl,

        % VALIDATION SUMMARY
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('📊 Validation Summary'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( G4micResult = valid, NanoCopResult = valid ->
            write('✅ Both provers agree: '), write('true'), nl
        ; G4micResult = invalid, NanoCopResult = invalid ->
            write('✅ Both provers agree: '), write('false'), nl
        ; G4micResult = valid, NanoCopResult = invalid ->
            write('⚠️  Disagreement: g4mic=true, nanocop=false'), nl
        ; G4micResult = invalid, NanoCopResult = valid ->
            write('⚠️  Disagreement: g4mic=false, nanocop=true'), nl
        ),
        nl, nl, !
    ).

% =========================================================================
% SEQUENT EQUIVALENCE (<>) - Complete corrected section (grouped by style)
% =========================================================================

prove([Left] <> [Right]) :- !,
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),

    % Test direction 1: [Left] > [Right]
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    ( catch(time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))), _, fail) ->
        Direction1Valid = true
    ;
        Direction1Valid = false, Proof1 = none, Logic1 = none
    ),

    % Test direction 2: [Right] > [Left]
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    ( catch(time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))), _, fail) ->
        Direction2Valid = true
    ;
        Direction2Valid = false, Proof2 = none, Logic2 = none
    ),

    nl,
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('             ↔️   EQUIVALENCE: Proving Both Directions          '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl, nl,

    % ═══════════════════════════════════════════════════════════════
    % SEQUENT CALCULUS (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('📐 Sequent Calculus Proofs'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - Sequent
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                    ➡️   DIRECTION 1                            '), nl,
    write('        '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true ->
        output_logic_label(Logic1), nl, nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof1, 0, _),
        write('\\end{prooftree}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % Direction 2 - Sequent
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                     ⬅️   DIRECTION 2                           '), nl,
    write('         '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true ->
        output_logic_label(Logic2), nl, nl,
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof2, 0, _),
        write('\\end{prooftree}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % NATURAL DEDUCTION - TREE STYLE (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🌳 Natural Deduction - Tree Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - ND Tree
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                      ➡️   DIRECTION 1                          '), nl,
    write('        '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true ->
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent([Left] > [Right])),
        retractall(premiss_list(_)),
        assertz(premiss_list([Left])),
        render_nd_tree_proof(Proof1), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % Direction 2 - ND Tree
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                          ⬅️   DIRECTION 2                      '), nl,
    write('            '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true ->
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent([Right] > [Left])),
        retractall(premiss_list(_)),
        assertz(premiss_list([Right])),
        render_nd_tree_proof(Proof2), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % NATURAL DEDUCTION - FITCH STYLE (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🚩 Natural Deduction - Flag Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - Fitch
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                      ➡️   DIRECTION 1                          '), nl,
    write('            '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true ->
        retractall(premiss_list(_)),
        assertz(premiss_list([Left])),
        write('\\begin{fitch}'), nl,
        g4_to_fitch_sequent(Proof1, [Left] > [Right]),
        write('\\end{fitch}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % Direction 2 - Fitch
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                    ⬅️   DIRECTION 2                            '), nl,
    write('         '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true ->
        retractall(premiss_list(_)),
        assertz(premiss_list([Right])),
        write('\\begin{fitch}'), nl,
        g4_to_fitch_sequent(Proof2, [Right] > [Left]),
        write('\\end{fitch}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % SUMMARY
    % ═══════════════════════════════════════════════════════════════
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('                       📊 SUMMARY                               '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl,
    write('Direction 1 ('), write(Left), write(' ⊢ '), write(Right), write('): '),
    ( Direction1Valid = true ->
        write('✅ VALID in '), write(Logic1), write(' logic')
    ; write('⚠️  FAILED')
    ), nl,
    write('Direction 2 ('), write(Right), write(' ⊢ '), write(Left), write('): '),
    ( Direction2Valid = true ->
        write('✅ VALID in '), write(Logic2), write(' logic')
    ; write('⚠️  FAILED')
    ), nl, nl, !.


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
    write('╔═══════════════════════════════════════════════════════════╗'), nl,
    write('    🔍 EQUALITY/FUNCTIONS DETECTED → USING NANOCOP ENGINE    '), nl,
    write('╚═══════════════════════════════════════════════════════════╝'), nl,
    nl,

    validate_and_warn(Formula, _),

    write('🔄 Calling nanoCoP prover...'), nl, nl,

    % DIRECT CALL to nanocop_proves/1 - THAT'S ALL!
    nanocop_proves(Formula),

    write('═══════════════════════════════════════════════════════════════'), nl,
    write('✅ Q.E.D.  '), nl, nl,!.

% ALTERNATIVE CLAUSE: No equality/functions → normal g4mic flow
prove(Formula) :-
    \+ g4mic_needs_nanocop(Formula),  % Exclude equality and functions
    validate_and_warn(Formula, _ValidatedFormula),
    % ═══════════════════════════════════════════════════════════════
    % NANOCOP FILTER (negative only)
    % ═══════════════════════════════════════════════════════════════
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
    nl, !, fail
    ),

    % ═══════════════════════════════════════════════════════════════
    % g4mic PROOF
    % ═══════════════════════════════════════════════════════════════
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  🎯 G4 PROOF FOR: '), write(Formula), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,

    retractall(premiss_list(_)),
    retractall(current_proof_sequent(_)),

    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),

    statistics(walltime, [Start|_]),

    ( provable_at_level([] > [F2], minimal, Proof) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('              ✅ MINIMAL LOGIC                            '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        Logic = minimal,
        OutputProof = Proof

    ; provable_at_level([] > [F2], constructive, Proof) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('              ✅ INTUITIONISTIC LOGIC                      '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        Logic = intuitionistic,
        OutputProof = Proof

    ; provable_at_level([] > [F2], classical, Proof) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('              ✅ CLASSICAL LOGIC                           '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        Logic = classical,
        OutputProof = Proof

    ;
        nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        write('⚠️  UNEXPECTED: g4mic failed but nanoCoP validated!'), nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        nl,
        write('This is likely a BUG in G4-mic.'), nl,
        write('Please help improve G4-mic by reporting this issue:'), nl,
        nl,
        write('  📧  Email: joseph@vidal-rosset.net'), nl,
        write('  📝  Include: the formula and this error message'), nl,
        nl,
        write('Thank you for your contribution!'), nl,
        nl,
        fail
    ),

    statistics(walltime, [End|_]),
    Time is (End - Start) / 1000,

    nl,
    format('⏱️  G4mic time: ~3f seconds~n', [Time]),
    nl,
    output_proof_results(OutputProof, Logic, Formula, theorem),
    !,


    % ═══════════════════════════════════════════════════════════════
    % PHASE 3: EXTERNAL VALIDATION (displayed)
    % ═══════════════════════════════════════════════════════════════
    nl,
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('                  🔍 PHASE 3: VALIDATION                         '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl,
    nl,

    % g4mic VALIDATION
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('🔍 g4mic_decides output'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( catch(g4mic_decides(Formula), _, fail) ->
        write('true.'), nl,
        G4micResult = valid
    ;
        write('false. '), nl,
        G4micResult = invalid
    ),
    nl,

    % NANOCOP VALIDATION (SILENCIEUX mais avec time/1)
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('🔍 nanocop_decides output'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( catch(time(nanocop_decides(Formula)), _, fail) ->
        write('true.'), nl,
        NanoCopResult = valid
    ;
        write('false.'), nl,
        NanoCopResult = invalid
    ),
    nl,

    % VALIDATION SUMMARY
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('📊 Validation Summary'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( G4micResult = valid, NanoCopResult = valid ->
        write('✅ Both provers agree: '), write('true'), nl
    ; G4micResult = invalid, NanoCopResult = invalid ->
        write('✅ Both provers agree: '), write('false'), nl
    ; G4micResult = valid, NanoCopResult = invalid ->
        nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        write('⚠️  CRITICAL DISAGREEMENT: g4mic=true, nanoCoP=false'), nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        nl,
        write('This is a SOUNDNESS BUG in G4-mic (false positive).'), nl,
        write('G4-mic proved an invalid formula!'), nl,
        nl,
        write('URGENT: Please report this issue immediately:'), nl,
        write('  📧  Email: joseph@vidal-rosset.net'), nl,
        write('  📝  Include: the formula and full output'), nl,
        nl
    ; G4micResult = invalid, NanoCopResult = valid ->
        nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        write('⚠️  DISAGREEMENT: g4mic=false, nanoCoP=true'), nl,
        write('═════════════════════════════════════════════════════════════'), nl,
        nl,
        write('This is a COMPLETENESS issue in G4-mic (false negative).'), nl,
        write('G4-mic failed to prove a valid formula.'), nl,
        nl,
        write('Please help improve G4-mic by reporting this:'), nl,
        write('  📧  Email: joseph@vidal-rosset.net'), nl,
        write('  📝  Include: the formula and validation output'), nl,
        nl
    ),
    nl, nl.
% =========================================================================
% HELPERS
% =========================================================================

% Prepare a list of formulas
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Compact display of a sequent
write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% FORMULA AND SEQUENT VALIDATION
% =========================================================================

% Validate a sequent (premisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Validate all premisses
    forall(member(Premiss, G), validate_and_warn(Premiss, _)),
    % Validate all conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    % Store logic level for use in proof rendering (e.g., DS optimization)
    retractall(current_logic_level(_)),
    assertz(current_logic_level(LogicType)),

    % Display appropriate label
    output_logic_label(LogicType),

    % ADDED: Display raw Prolog proof term
    nl, write('=== RAW PROLOG PROOF TERM ==='), nl,
    write('    '), portray_clause(Proof), nl, nl,
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),

    % Sequent Calculus
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('📐 Sequent Calculus Proof'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('✅ Q.E.D.'), nl, nl,

    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🌳 Natural Deduction - Tree Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
    render_nd_tree_proof(Proof), nl, nl,
    write('✅ Q.E.D.'), nl, nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🚩 Natural Deduction - Flag Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
    write('\\begin{fitch}'), nl,
    ( Mode = sequent ->
        g4_to_fitch_sequent(Proof, OriginalFormula)
    ;
        g4_to_fitch_theorem(Proof)
    ),
    write('\\end{fitch}'), nl, nl,
    write('✅ Q.E.D.'), nl, nl,
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

% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (Gamma > Delta),
    prepare_sequent_formulas(Gamma, Delta, PrepGamma, PrepDelta),
    ( member(SingleGoal, PrepDelta), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepGamma > PrepDelta, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepGamma > PrepDelta, intuitionistic, Proof) ->
        Logic = intuitionistic
    ;
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ).

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
    % Check if user meant sequent equivalence (<>) instead of biconditional (<=>)
    ( (is_list(Left) ; is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('║  ⚠️  SYNTAX ERROR: <=> used with sequents                     ║'), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: '), write(Left <=> Right), nl,
        nl,
        write('❌ WRONG:   <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: p <=> q'), nl,
        nl,
        write('✅ CORRECT: <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: [p] <> [q]'), nl,
        nl,
        write('Please use:  '), write([Left] <> [Right]), nl,
        nl,
        fail
    ;
        % Normal biconditional processing
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
        !
    ).

% g4mic_decides/1 for sequent equivalence (must come before Formula catch-all)
g4mic_decides([Left] <> [Right]) :- !,
    % Check if user meant biconditional (<=>) instead of sequent equivalence (<>)
    ( (\+ is_list(Left) ; \+ is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('║  ⚠️  SYNTAX ERROR: <> used with formulas                      ║'), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: '), write([Left] <> [Right]), nl,
        nl,
        write('❌ WRONG:   <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: [p] <> [q]'), nl,
        nl,
        write('✅ CORRECT: <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: p <=> q'), nl,
        nl,
        write('Please use:  '), write(Left <=> Right), nl,
        nl,
        fail
    ;
        % Normal sequent equivalence processing
        validate_sequent_formulas(Left, Right),

        % Test direction 1: Left > Right
        time(prove_sequent_silent(Left > Right, _Proof1, Logic1)),
        write('Direction 1 ('), write(Left), write(' > '), write(Right), write(') is valid in '),
        write(Logic1), write(' logic'), nl,

        % Test direction 2: Right > Left
        time(prove_sequent_silent(Right > Left, _Proof2, Logic2)),
        write('Direction 2 ('), write(Right), write(' > '), write(Left), write(') is valid in '),
        write(Logic2), write(' logic'), nl,
        !
    ).

% g4mic_decides/1 for sequents
g4mic_decides(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),

    % Check for classical patterns in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('🔍 Classical pattern detected → Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, _Proof)),
        write('Valid in classical logic'), nl
    ;
        % Normal progression: minimal → intuitionistic → classical
        ( time(provable_at_level(PrepG > PrepD, minimal, _Proof)) ->
            write('Valid in minimal logic'), nl
        ; time(provable_at_level(PrepG > PrepD, intuitionistic, _Proof)) ->
            write('Valid in intuitionistic logic'), nl
        ; time(provable_at_level(PrepG > PrepD, classical, _Proof)) ->
            write('Valid in classical logic'), nl
        ;
            write('Failed to prove'), nl, fail
        )
    ),
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
        write('🔍 Double negation detected → Trying constructive logic first'), nl,
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
        write('🔍 Classical pattern detected → Trying constructive logic first'), nl,
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
        % Normal progression: minimal → intuitionistic → classical
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
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P '), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P , Q |- P & Q '), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('    prove(p <> ~ ~ p).                 - Bi-implication of Double Negation (sequents)'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
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
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
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
