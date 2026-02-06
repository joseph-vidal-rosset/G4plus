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
    process_tptp_formulas(Formulas).

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
process_tptp_formulas([], Axioms) :-
    % If axioms remain at end without conjecture, report them
    (   Axioms \= [] ->
        length(Axioms, NumAxioms),
        format('~nWarning: ~w axiom(s) without conjecture at end of file~n', [NumAxioms])
    ;   true
    ).

process_tptp_formulas([fof(Name, Role, Formula)|Rest], AccAxioms) :-
    (   Role = axiom ->
        % Accumulate axiom for later combination with conjecture
        process_tptp_formulas(Rest, [fof(Name, axiom, Formula)|AccAxioms])

    ;   Role = conjecture ->
        % Found conjecture - combine with accumulated axioms
        nl,
        format('═══════════════════════════════════════════════════════════════~n', []),
        (   AccAxioms = [] ->
            format('TPTP Problem: ~w (conjecture, no axioms)~n', [Name])
        ;   length(AccAxioms, NumAxioms),
            format('TPTP Problem: ~w (conjecture with ~w axiom(s))~n', [Name, NumAxioms]),
            % Display axiom names
            extract_axiom_names(AccAxioms, AxiomNames),
            format('  Axioms: ~w~n', [AxiomNames])
        ),
        format('═══════════════════════════════════════════════════════════════~n', []),
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

        % Prove the combined formula
        prove_tptp_internal(CombinedFormula),

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

% Convert TPTP formula by replacing Prolog variables with generated atoms
% This preserves the variable/constant distinction that string conversion destroys
convert_tptp_vars(Formula, Converted) :-
    convert_tptp_vars(Formula, 0, Converted, _).

% For quantifiers, unify Prolog variables with generated atoms
convert_tptp_vars(!(VarTerm:Body), Counter, Result, NextCounter) :- !,
    % Handle both ![X]: and ![X,Y]:
    (   is_list(VarTerm) ->
        bind_vars_in_list(VarTerm, Counter, Counter1)
    ;   var(VarTerm) ->
        xyz_name(Counter, AtomName),
        VarTerm = AtomName,
        Counter1 is Counter + 1
    ;   Counter1 = Counter
    ),
    convert_tptp_vars(Body, Counter1, NewBody, NextCounter),
    Result = (!(VarTerm:NewBody)).

convert_tptp_vars(?(VarTerm:Body), Counter, Result, NextCounter) :- !,
    (   is_list(VarTerm) ->
        bind_vars_in_list(VarTerm, Counter, Counter1)
    ;   var(VarTerm) ->
        xyz_name(Counter, AtomName),
        VarTerm = AtomName,
        Counter1 is Counter + 1
    ;   Counter1 = Counter
    ),
    convert_tptp_vars(Body, Counter1, NewBody, NextCounter),
    Result = (?(VarTerm:NewBody)).

convert_tptp_vars(A & B, Counter, NewA & NewB, NextCounter) :- !,
    convert_tptp_vars(A, Counter, NewA, Counter1),
    convert_tptp_vars(B, Counter1, NewB, NextCounter).

convert_tptp_vars(A | B, Counter, NewA | NewB, NextCounter) :- !,
    convert_tptp_vars(A, Counter, NewA, Counter1),
    convert_tptp_vars(B, Counter1, NewB, NextCounter).

convert_tptp_vars(A => B, Counter, NewA => NewB, NextCounter) :- !,
    convert_tptp_vars(A, Counter, NewA, Counter1),
    convert_tptp_vars(B, Counter1, NewB, NextCounter).

convert_tptp_vars(A <=> B, Counter, NewA <=> NewB, NextCounter) :- !,
    convert_tptp_vars(A, Counter, NewA, Counter1),
    convert_tptp_vars(B, Counter1, NewB, NextCounter).

convert_tptp_vars(~A, Counter, ~NewA, NextCounter) :- !,
    convert_tptp_vars(A, Counter, NewA, NextCounter).

convert_tptp_vars(Term, Counter, Term, Counter).

% Bind each variable in a list to a generated atom
bind_vars_in_list([], Counter, Counter).
bind_vars_in_list([Var|Rest], Counter, NextCounter) :-
    (   var(Var) ->
        xyz_name(Counter, AtomName),
        Var = AtomName,
        Counter1 is Counter + 1
    ;   Counter1 = Counter
    ),
    bind_vars_in_list(Rest, Counter1, NextCounter).

% Expand multi-variable quantifiers ONLY: ![v0,v1]: → ![v0]:![v1]:
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
% Expand multi-variable quantifiers: ![x,y]: → ![x]:![y]:
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

% Convert comma operator to list: ','(a,','(b,c)) → [a,b,c]
comma_to_list((A,B), [A|Rest]) :-
    !,
    comma_to_list(B, Rest).
comma_to_list(A, [A]).

% Rename quantified variables in a formula to x, y, z, x0, y0, z0...
rename_quantified_vars(Formula, RenamedFormula) :-
    % Safety check: if Formula is an unbound variable, fail gracefully
    (   var(Formula) ->
        RenamedFormula = Formula
    ;   rename_quantified_vars(Formula, 0, RenamedFormula, _)
    ).

% Counter-based renaming

% Pattern 1: !(Var:Body) - produced by expand_forall_list
rename_quantified_vars(!(OldName:Body), Counter, Result, NextCounter) :-
    (atom(OldName) ; compound(OldName)), !,  % Accept both atoms and compounds like $var(0)
    format('DEBUG rename !(~w:...) with counter=~w~n', [OldName, Counter]),
    xyz_name(Counter, NewName),
    format('DEBUG newname=~w, substituting in: ~w~n', [NewName, Body]),
    substitute_in_formula(Body, OldName, NewName, SubstBody),
    format('DEBUG after subst: ~w~n', [SubstBody]),
    Counter1 is Counter + 1,
    rename_quantified_vars(SubstBody, Counter1, NewBody, NextCounter),
    % Construct !(NewName:NewBody) explicitly
    Expr = (NewName:NewBody),
    Result =.. ['!', Expr],
    format('DEBUG result: ~w~n', [Result]).

% Pattern 2: ?(Var:Body) - produced by expand_exists_list
rename_quantified_vars(?(OldName:Body), Counter, Result, NextCounter) :-
    (atom(OldName) ; compound(OldName)), !,  % Accept both atoms and compounds like $var(0)
    xyz_name(Counter, NewName),
    substitute_in_formula(Body, OldName, NewName, SubstBody),
    Counter1 is Counter + 1,
    rename_quantified_vars(SubstBody, Counter1, NewBody, NextCounter),
    % Construct ?(NewName:NewBody) explicitly
    Expr = (NewName:NewBody),
    Result =.. ['?', Expr].

% Pattern 3: ![Var]:Body - legacy pattern
rename_quantified_vars(![OldName]:Body, Counter, ![NewName]:NewBody, NextCounter) :- !,
    xyz_name(Counter, NewName),
    substitute_in_formula(Body, OldName, NewName, SubstBody),
    Counter1 is Counter + 1,
    rename_quantified_vars(SubstBody, Counter1, NewBody, NextCounter).

rename_quantified_vars(?[OldName]:Body, Counter, ?[NewName]:NewBody, NextCounter) :- !,
    xyz_name(Counter, NewName),
    substitute_in_formula(Body, OldName, NewName, SubstBody),
    Counter1 is Counter + 1,
    rename_quantified_vars(SubstBody, Counter1, NewBody, NextCounter).

rename_quantified_vars(A & B, Counter, NewA & NewB, NextCounter) :- !,
    rename_quantified_vars(A, Counter, NewA, Counter1),
    rename_quantified_vars(B, Counter1, NewB, NextCounter).

rename_quantified_vars(A | B, Counter, NewA | NewB, NextCounter) :- !,
    rename_quantified_vars(A, Counter, NewA, Counter1),
    rename_quantified_vars(B, Counter1, NewB, NextCounter).

rename_quantified_vars(A => B, Counter, NewA => NewB, NextCounter) :- !,
    rename_quantified_vars(A, Counter, NewA, Counter1),
    rename_quantified_vars(B, Counter1, NewB, NextCounter).

rename_quantified_vars(A <=> B, Counter, NewA <=> NewB, NextCounter) :- !,
    rename_quantified_vars(A, Counter, NewA, Counter1),
    rename_quantified_vars(B, Counter1, NewB, NextCounter).

rename_quantified_vars(~A, Counter, ~NewA, NextCounter) :- !,
    rename_quantified_vars(A, Counter, NewA, NextCounter).

% Equality - no renaming needed, just process both sides
rename_quantified_vars(A = B, Counter, NewA = NewB, Counter) :- !,
    rename_in_term(A, NewA),
    rename_in_term(B, NewB).

rename_quantified_vars(Term, Counter, NewTerm, Counter) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(rename_in_term, Args, NewArgs),
    NewTerm =.. [F|NewArgs].

rename_quantified_vars(Atom, Counter, Atom, Counter).

% Helper for compound terms (no renaming, just recursion)
rename_in_term(Term, Term) :-
    atomic(Term), !.
rename_in_term(Term, NewTerm) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(rename_in_term, Args, NewArgs),
    NewTerm =.. [F|NewArgs].

% Substitute all occurrences of OldName with NewName in formula
substitute_in_formula(Old, Old, New, New) :-
    atom(Old), !.

substitute_in_formula(Atom, _Old, _New, Atom) :-
    atomic(Atom), !.

substitute_in_formula(Term, Old, New, NewTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(substitute_in_args(Old, New), Args, NewArgs),
    NewTerm =.. [F|NewArgs].

substitute_in_args(Old, New, Arg, NewArg) :-
    substitute_in_formula(Arg, Old, New, NewArg).
% Generate x, y, z, x0, y0, z0, x1, y1, z1...
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


% Direct TPTP formula entry (for testing)
prove_tptp(fof(Name, Role, Formula)) :-
    nl,
    format('═══════════════════════════════════════════════════════════════~n', []),
    format('TPTP: ~w (~w)~n', [Name, Role]),
    format('═══════════════════════════════════════════════════════════════~n', []),
    nl,
    convert_tptp_formula(Formula, G4micFormula),
    format('Converted to G4-mic: ~w~n~n', [G4micFormula]),
    % Skip validate_and_warn for TPTP - it gives false positives on ![x]: syntax
    prove_tptp_internal(G4micFormula).

% Internal prove for TPTP (bypasses validate_and_warn)
prove_tptp_internal(Formula) :-
    % Check if needs nanoCoP (equality/functions)
    g4mic_needs_nanocop(Formula),
    !,
    nl,
    write('╔═══════════════════════════════════════════════════════════╗'), nl,
    write('   🔍 EQUALITY/FUNCTIONS DETECTED → USING NANOCOP ENGINE     '), nl,
    write('╚═══════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('🔄 Calling nanoCoP prover...'), nl, nl,
    nanocop_proves(Formula),
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('✅ Q.E.D.  '), nl, nl.

prove_tptp_internal(Formula) :-
    % Normal g4mic flow (same as prove/1 but without validate_and_warn)
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
    nl, !, fail
    ),

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

    % Validation phase
    nl,
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('                  🔍 PHASE 3: VALIDATION                         '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl,
    nl,

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
% UTILITY: AUTO-SUGGESTION (optional feature)
% =========================================================================
%%% END OF g4mic PROVER
