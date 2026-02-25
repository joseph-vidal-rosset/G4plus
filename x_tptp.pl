% =========================================================================
% TPTP FORMAT SUPPORT
% =========================================================================
% G4-mic uses lowercase-only syntax, while TPTP uses uppercase for variables.
% This module converts TPTP formulas to G4-mic syntax.

% Read and process a TPTP file
prove_tptp_file(Filename) :-
    file_directory_name(Filename, FileDir),
    open(Filename, read, Stream),
    read_tptp_formulas(Stream, FileDir, Formulas),
    close(Stream),
    ( process_tptp_formulas(Formulas) -> true ; true ).

% Read all fof() declarations from file, resolving include() directives.
% FileDir is the directory of the current file, used for relative include paths.
read_tptp_formulas(Stream, FileDir, Formulas) :-
    \+ at_end_of_stream(Stream),
    read(Stream, Term),
    !,
    (   Term = fof(_, _, _) ->
        Formulas = [Term|Rest],
        read_tptp_formulas(Stream, FileDir, Rest)
    ;   Term = include(RelPath) ->
        % Resolve include path: try relative to FileDir first, then $TPTP
        ( atom_concat(FileDir, '/', Prefix),
          atom_concat(Prefix, RelPath, AbsPath1),
          exists_file(AbsPath1)
        -> IncludePath = AbsPath1
        ; getenv('TPTP', TTPTBase),
          atom_concat(TTPTBase, '/', TPrefix),
          atom_concat(TPrefix, RelPath, AbsPath2),
          exists_file(AbsPath2)
        -> IncludePath = AbsPath2
        ;  format('% WARNING: Include file not found: ~w~n', [RelPath]),
           IncludePath = ''
        ),
        ( IncludePath \= '' ->
            file_directory_name(IncludePath, IncludeDir),
            open(IncludePath, read, IncStream),
            read_tptp_formulas(IncStream, IncludeDir, IncFormulas),
            close(IncStream),
            read_tptp_formulas(Stream, FileDir, RestFormulas),
            append(IncFormulas, RestFormulas, Formulas)
        ;
            read_tptp_formulas(Stream, FileDir, Formulas)
        )
    ;   % Skip other non-fof terms (comments, directives, etc.)
        read_tptp_formulas(Stream, FileDir, Formulas)
    ).
read_tptp_formulas(_, _, []).

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

szs_status(has_conjecture, proved,    'Theorem').
szs_status(has_conjecture, disproved, 'CounterSatisfiable').
szs_status(no_conjecture,  proved,    'Unsatisfiable').
szs_status(no_conjecture,  disproved, 'Satisfiable').

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
      output_proof_results(OutputProof, Logic, Formula),
      tptp_validation_phase(Formula, 'Unsatisfiable')
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
    tptp_validation_phase(Formula, 'Theorem').

% =========================================================================
% SHARED VALIDATION PHASE
% =========================================================================
% Called after every successful g4mic proof (prove/1 and prove_tptp_internal).
% SZSStatus is the SZS verdict already announced ('Theorem' or 'Unsatisfiable'),
% used to phrase the agreement message correctly.
% Runs g4mic_decides + nanocop_decides (with time/1) and summarises agreement.

tptp_validation_phase(Formula, SZSStatus) :-
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
        format('Both provers agree: ~w.~n', [SZSStatus])
    ; G4micResult = invalid, NanoCopResult = invalid ->
        write('Both provers agree: not provable.'), nl
    ; G4micResult = valid, NanoCopResult = invalid ->
        write('[!] SOUNDNESS BUG: g4mic=true, nanoCoP=false'), nl,
        write('    Please report to: joseph@vidal-rosset.net'), nl
    ; G4micResult = invalid, NanoCopResult = valid ->
        write('[!] COMPLETENESS ISSUE: g4mic=false, nanoCoP=true'), nl,
        write('    Please report to: joseph@vidal-rosset.net'), nl
    ),
    nl.

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

%%% END OF g4mic PROVER
