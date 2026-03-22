% =========================================================================
% FOF <-> G4+ FORMULA CONVERTERS
% =========================================================================
% fof_to_prove/1   : reads a .p file, outputs prove(Formula). command
% get_fof_problem/1: takes a G4+ formula, outputs fof(...) TPTP text

:-style_check(-singleton).

%% fof_to_prove(+Filename)
%  Reads a TPTP .p file and prints the equivalent prove/1 command(s).
%  Handles axioms + conjecture by combining them as (Ax1 & Ax2 & ...) => Conj.

fof_to_prove(Filename) :-
    catch(
        fof_to_prove_safe(Filename),
        Error,
        ( format('% Error reading file: ~w~n', [Error]) )
    ).

%% fof_to_prove_run(+Filename)
%  Like fof_to_prove/1, but directly executes prove/1 on each conjecture.
%  Used by the tinker.html button for one-click proof generation.

fof_to_prove_run(Filename) :-
    catch(
        fof_to_prove_run_safe(Filename),
        Error,
        ( format('% Error: ~w~n', [Error]) )
    ).

fof_to_prove_run_safe(Filename) :-
    file_directory_name(Filename, FileDir),
    open(Filename, read, Stream),
    read_tptp_formulas_limited(Stream, FileDir, Formulas, 100000, Truncated),
    close(Stream),
    ( Truncated = true ->
        format('% File too large (> 100000 formulae)~n')
    ;
        collect_all_axioms(Formulas, AllAxioms, Conjectures),
        ( Conjectures = [] ->
            ( AllAxioms = [] ->
                write('% No conjecture or axioms found in file.'), nl
            ;
                write('% No conjecture found. Axioms only.'), nl,
                maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
                combine_axioms(G4micAxioms, Combined),
                NegFormula = (Combined => #),
                format('% Running: prove(~w).~n~n', [NegFormula]),
                ( prove(NegFormula) -> true ; true )
            )
        ;
            maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
            forall(
                member(fof(Name, conjecture, Formula), Conjectures),
                ( convert_tptp_formula(Formula, G4micConj),
                  ( G4micAxioms = [] ->
                      CombinedFormula = G4micConj
                  ;
                      combine_axioms(G4micAxioms, CombinedAxioms),
                      CombinedFormula = (CombinedAxioms => G4micConj)
                  ),
                  format('~n% ~w~n', [Name]),
                  format('% Running: prove(~w).~n~n', [CombinedFormula]),
                  ( prove(CombinedFormula) -> true ; true )
                )
            )
        )
    ).

fof_to_prove_safe(Filename) :-
    file_directory_name(Filename, FileDir),
    open(Filename, read, Stream),
    read_tptp_formulas_limited(Stream, FileDir, Formulas, 100000, Truncated),
    close(Stream),
    ( Truncated = true ->
        format('% File too large (> 100000 formulae)~n')
    ;
        collect_all_axioms(Formulas, AllAxioms, Conjectures),
        ( Conjectures = [] ->
            ( AllAxioms = [] ->
                write('% No conjecture or axioms found in file.'), nl
            ;
                write('% No conjecture found. Axioms only (satisfiability check):'), nl,
                maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
                combine_axioms(G4micAxioms, Combined),
                format('prove(~w => #).~n', [Combined])
            )
        ;
            maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
            forall(
                member(fof(Name, conjecture, Formula), Conjectures),
                ( convert_tptp_formula(Formula, G4micConj),
                  ( G4micAxioms = [] ->
                      CombinedFormula = G4micConj
                  ;
                      combine_axioms(G4micAxioms, CombinedAxioms),
                      CombinedFormula = (CombinedAxioms => G4micConj)
                  ),
                  format('% ~w~n', [Name]),
                  format('prove(~w).~n~n', [CombinedFormula])
                )
            )
        )
    ).

%% get_fof_problem(+Formula)
%  Takes a G4+ formula and prints a valid TPTP fof() declaration.
%  Example: get_fof_problem(![x]: p(x) => p(a)).
%  Output:  fof(my_conjecture, conjecture, ![X]: (p(X) => p(a))).

get_fof_problem(Formula) :-
    collect_bound_vars(Formula, BoundVars),
    sort(BoundVars, BoundSet),
    write('fof(my_conjecture, conjecture, '),
    write_tptp_formula(Formula, BoundSet),
    write(').'),
    nl.

%% collect_bound_vars(+Formula, -Vars)
%  Collects all variable names bound by quantifiers in the formula.

collect_bound_vars(![X]:A, Vars) :- !,
    collect_bound_vars(A, RestVars),
    Vars = [X | RestVars].
collect_bound_vars(?[X]:A, Vars) :- !,
    collect_bound_vars(A, RestVars),
    Vars = [X | RestVars].
collect_bound_vars(all X:A, Vars) :- !,
    collect_bound_vars(A, RestVars),
    Vars = [X | RestVars].
collect_bound_vars(ex X:A, Vars) :- !,
    collect_bound_vars(A, RestVars),
    Vars = [X | RestVars].
collect_bound_vars(~A, Vars) :- !,
    collect_bound_vars(A, Vars).
collect_bound_vars(A & B, Vars) :- !,
    collect_bound_vars(A, V1),
    collect_bound_vars(B, V2),
    append(V1, V2, Vars).
collect_bound_vars(A | B, Vars) :- !,
    collect_bound_vars(A, V1),
    collect_bound_vars(B, V2),
    append(V1, V2, Vars).
collect_bound_vars(A => B, Vars) :- !,
    collect_bound_vars(A, V1),
    collect_bound_vars(B, V2),
    append(V1, V2, Vars).
collect_bound_vars(A <=> B, Vars) :- !,
    collect_bound_vars(A, V1),
    collect_bound_vars(B, V2),
    append(V1, V2, Vars).
collect_bound_vars(_, []).

%% write_tptp_formula(+Formula, +BoundVars)
%  Prints a G4+ formula in TPTP syntax.
%  BoundVars: list of atoms that are quantifier-bound variables
%  (these get uppercased in the output).

write_tptp_formula(#, _) :- !, write('$false').
write_tptp_formula(bot, _) :- !, write('$false').
write_tptp_formula(top, _) :- !, write('$true').

% Quantifiers: ![x]: -> ![X]:
write_tptp_formula(![X]:A, BV) :- !,
    upcase_atom(X, XU),
    write('(!['), write(XU), write(']: '),
    write_tptp_formula(A, BV),
    write(')').
write_tptp_formula(?[X]:A, BV) :- !,
    upcase_atom(X, XU),
    write('(?['), write(XU), write(']: '),
    write_tptp_formula(A, BV),
    write(')').
write_tptp_formula(all X:A, BV) :- !,
    upcase_atom(X, XU),
    write('(!['), write(XU), write(']: '),
    write_tptp_formula(A, BV),
    write(')').
write_tptp_formula(ex X:A, BV) :- !,
    upcase_atom(X, XU),
    write('(?['), write(XU), write(']: '),
    write_tptp_formula(A, BV),
    write(')').

% Negation
write_tptp_formula(~A, BV) :- !,
    write('~'),
    write_tptp_atom(A, BV).

% Binary connectives
write_tptp_formula(A & B, BV) :- !,
    write('('),
    write_tptp_formula(A, BV), write(' & '), write_tptp_formula(B, BV),
    write(')').
write_tptp_formula(A | B, BV) :- !,
    write('('),
    write_tptp_formula(A, BV), write(' | '), write_tptp_formula(B, BV),
    write(')').
write_tptp_formula(A => B, BV) :- !,
    write('('),
    write_tptp_formula(A, BV), write(' => '), write_tptp_formula(B, BV),
    write(')').
write_tptp_formula(A <=> B, BV) :- !,
    write('('),
    write_tptp_formula(A, BV), write(' <=> '), write_tptp_formula(B, BV),
    write(')').

% Equality
write_tptp_formula(A = B, BV) :- !,
    write('('),
    write_tptp_term(A, BV), write(' = '), write_tptp_term(B, BV),
    write(')').

% Compound predicate: p(x,y) -> p(X,Y) if x,y are bound vars
write_tptp_formula(Term, BV) :-
    compound(Term),
    Term =.. [F | Args],
    Args \= [],
    \+ memberchk(F, [~, &, '|', =>, <=>, !, ?, all, ex, '#']),
    !,
    write(F), write('('),
    write_tptp_args(Args, BV),
    write(')').

% Atom: uppercase if bound variable, otherwise keep as-is
write_tptp_formula(A, BV) :-
    atom(A), !,
    ( memberchk(A, BV) ->
        upcase_atom(A, AU), write(AU)
    ;
        write(A)
    ).

% Fallback
write_tptp_formula(X, _) :- write(X).

% Helper for terms (inside predicates/functions)
write_tptp_term(Term, BV) :-
    compound(Term),
    Term =.. [F | Args],
    Args \= [],
    !,
    write(F), write('('),
    write_tptp_args(Args, BV),
    write(')').
write_tptp_term(A, BV) :-
    atom(A), !,
    ( memberchk(A, BV) ->
        upcase_atom(A, AU), write(AU)
    ;
        write(A)
    ).
write_tptp_term(X, _) :- write(X).

% Helper for negation: add parens around complex subformulas
write_tptp_atom(A, BV) :-
    ( atom(A) ; A = #; compound(A), functor(A, F, _),
      \+ memberchk(F, [~, &, '|', =>, <=>, !, ?, all, ex]) ) ->
        write_tptp_formula(A, BV)
    ;
        write('('), write_tptp_formula(A, BV), write(')').

write_tptp_args([], _) :- !.
write_tptp_args([A], BV) :- !, write_tptp_term(A, BV).
write_tptp_args([A|Rest], BV) :-
    write_tptp_term(A, BV), write(', '),
    write_tptp_args(Rest, BV).

% =========================================================================
% TPTP FORMAT SUPPORT
% =========================================================================
% G4-mic uses lowercase-only syntax, while TPTP uses uppercase for variables.
% This module converts TPTP formulas to G4-mic syntax.

% Read and process a TPTP file
% prove_tptp_file/1 — main entry point.
% prove_tptp_file/2 — kept for backward compatibility (TimeoutSecs ignored,
%                     inference limit is used instead).
prove_tptp_file(Filename) :-
    prove_tptp_file(Filename, _Ignored).

prove_tptp_file(Filename, _TimeoutSecs) :-
    catch(
        prove_tptp_file_safe(Filename),
        Error,
        ( nl, format('% SZS status GaveUp (error: ~w)~n', [Error]) )
    ).

prove_tptp_file_safe(Filename) :-
    file_directory_name(Filename, FileDir),
    % Cap loading at 100 000 formulae — problems like CSR+5 have 540 000+
    % and loop forever on axiom loading alone.
    open(Filename, read, Stream),
    read_tptp_formulas_limited(Stream, FileDir, Formulas, 100000, Truncated),
    close(Stream),
    ( Truncated = true ->
        format('% WARNING: Problem has > 100000 formulae, too large for G4+~n'),
        format('% SZS status GaveUp~n')
    ;
        ( process_tptp_formulas(Formulas) -> true ; true )
    ).

% read_tptp_formulas_limited/5
% Like read_tptp_formulas/3 but stops after Max formulae.
% Truncated = true if limit was hit.
read_tptp_formulas_limited(Stream, FileDir, Formulas, Max, Truncated) :-
    read_tptp_formulas_acc(Stream, FileDir, Formulas, Max, 0, Truncated).

read_tptp_formulas_acc(Stream, _FileDir, [], _Max, _Count, false) :-
    at_end_of_stream(Stream), !.
read_tptp_formulas_acc(_Stream, _FileDir, [], _Max, Count, true) :-
    Count >= 100000, !.
read_tptp_formulas_acc(Stream, FileDir, Formulas, Max, Count, Truncated) :-
    \+ at_end_of_stream(Stream),
    read(Stream, Term), !,
    (   Term = fof(_, _, _) ->
        Count1 is Count + 1,
        ( Count1 >= Max ->
            Formulas = [Term], Truncated = true
        ;
            Formulas = [Term|Rest],
            read_tptp_formulas_acc(Stream, FileDir, Rest, Max, Count1, Truncated)
        )
    ;   Term = include(RelPath) ->
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
            Remaining is Max - Count,
            read_tptp_formulas_acc(IncStream, IncludeDir, IncFormulas, Remaining, 0, Trunc1),
            close(IncStream),
            length(IncFormulas, IncCount),
            Count2 is Count + IncCount,
            ( Trunc1 = true ->
                Formulas = IncFormulas, Truncated = true
            ;
                read_tptp_formulas_acc(Stream, FileDir, RestFormulas, Max, Count2, Truncated),
                append(IncFormulas, RestFormulas, Formulas)
            )
        ;
            read_tptp_formulas_acc(Stream, FileDir, Formulas, Max, Count, Truncated)
        )
    ;
        read_tptp_formulas_acc(Stream, FileDir, Formulas, Max, Count, Truncated)
    ).
read_tptp_formulas_acc(_, _, [], _, _, false).



% Process list of TPTP formulas - collect axioms and combine with conjecture
% Two-pass: first collect ALL axioms, then process conjecture.
% This handles files where the conjecture appears before some or all axioms.
process_tptp_formulas(Formulas) :-
    collect_all_axioms(Formulas, AllAxioms, Conjectures),
    ( Conjectures = [] ->
        % No conjecture: satisfiability check on axioms only
        ( AllAxioms \= [] ->
            length(AllAxioms, NumAxioms),
            format('~nSatisfiability check: ~w axiom(s) without conjecture~n', [NumAxioms]),
            maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
            combine_axioms(G4micAxioms, Combined),
            ( prove_tptp_internal(Combined, no_conjecture) -> true ; true )
        ; true
        )
    ;
        process_tptp_formulas_with_axioms(Conjectures, AllAxioms)
    ).

% Collect all axioms and conjectures from formula list (order-independent)
collect_all_axioms([], [], []).
collect_all_axioms([fof(Name, Role, Formula)|Rest], Axioms, Conjectures) :-
    collect_all_axioms(Rest, RestAxioms, RestConjectures),
    ( memberchk(Role, [axiom, hypothesis, lemma, definition, assumption]) ->
        Axioms = [fof(Name, axiom, Formula)|RestAxioms],
        Conjectures = RestConjectures
    ; Role = conjecture ->
        Axioms = RestAxioms,
        Conjectures = [fof(Name, conjecture, Formula)|RestConjectures]
    ;
        format('Skipping ~w with role ~w~n', [Name, Role]),
        Axioms = RestAxioms,
        Conjectures = RestConjectures
    ).

% Process conjectures with the full axiom set already collected
process_tptp_formulas_with_axioms([], _AllAxioms).
process_tptp_formulas_with_axioms([fof(Name, conjecture, Formula)|Rest], AllAxioms) :-
    nl,
    format('===============================================================~n', []),
    ( AllAxioms = [] ->
        format('TPTP Problem: ~w (conjecture, no axioms)~n', [Name])
    ;   length(AllAxioms, NumAxioms),
        format('TPTP Problem: ~w (conjecture with ~w axiom(s))~n', [Name, NumAxioms]),
        extract_axiom_names(AllAxioms, AxiomNames),
        format('  Axioms: ~w~n', [AxiomNames])
    ),
    format('===============================================================~n', []),
    nl,
    convert_tptp_formula(Formula, G4micConjecture),
    maplist(convert_axiom_formula, AllAxioms, G4micAxioms),
    ( G4micAxioms = [] ->
        CombinedFormula = G4micConjecture
    ;   combine_axioms(G4micAxioms, CombinedAxioms),
        CombinedFormula = (CombinedAxioms => G4micConjecture),
        length(G4micAxioms, NumAx),
        format('Combined formula: ~w axiom(s) => conjecture~n~n', [NumAx])
    ),
    ( prove_tptp_internal(CombinedFormula, has_conjecture) -> true ; true ),
    process_tptp_formulas_with_axioms(Rest, AllAxioms).



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
% Case 1: equality/functions detected - delegate to nanoCoP (oracle mode)
prove_tptp_internal(Formula, ProblemType) :-
    % Check if needs nanoCoP (equality/functions)
    g4mic_needs_nanocop(Formula),
    !,
    catch(
        (
            ( write('nanoCoP : '), nl,
              time(call_with_inference_limit(nanocop_decides(Formula), 2000000, InfResult_eq)),
              InfResult_eq \== inference_limit_exceeded ->
                szs_status(ProblemType, proved, SZSStatus),
                nl,
                format('% nanoCoP proof (equality/functions)~n', []),
                format('% nanoCoP proof is given at https://g4-mic.vidal-rosset.net/wasm/tinker via nanocop_proves(Your_Formula).~n', []),
                format('% SZS status ~w~n', [SZSStatus]),
                nl
            ;
                format('% SZS status GaveUp~n', []),
                fail
            )
        ),
        nanocop_gave_up,
        ( format('% SZS status GaveUp~n', []), fail )
    ).

% Case 2a: no conjecture - nanoCoP validates unsatisfiability, G4+ classifies logic level
% To check unsatisfiability of Formula, we prove its negation (Formula => #).
prove_tptp_internal(Formula, no_conjecture) :-
    !,
    NegFormula = (Formula => #),
    ( catch(
          (write('nanoCoP : '), nl,
           time(call_with_inference_limit(nanocop_decides(NegFormula), 2000000, InfResult_nc))),
          _,
          fail
      ),
      InfResult_nc \== inference_limit_exceeded  % Fail if inference limit was exceeded
    ->
      % nanoCoP validated: now determine the logic level (no proof term)
      ( write('g4mic : '), nl,
        time(g4mic_logic_level(NegFormula, Logic)) ->
          nl,
          format('% Logic level: valid in ~w logic.~n', [Logic]),
          format('% To get proofs (sequent calculus G4 and natural deduction), you can use G4+ at https://g4-mic.vidal-rosset.net/wasm/tinker~n'),
          format('% SZS status Unsatisfiable~n', []),
          nl
      ;
          % G4+ could not classify but nanoCoP validated: still Unsatisfiable
          nl,
          format('% To get proofs (sequent calculus G4 and natural deduction), you can use G4+ at https://g4-mic.vidal-rosset.net/wasm/tinker~n'),
          format('% SZS status Unsatisfiable~n', []),
          nl
      )
    ;
      % nanoCoP could not prove NegFormula within limits.
      % Never claim Satisfiable without proof.
      ( InfResult_nc == inference_limit_exceeded ->
          format('% SZS status GaveUp~n', [])
      ;
          % nanoCoP completed but failed: probe without cut for reliable status
          nanocop_probe(NegFormula, ProbeResult),
          ( ProbeResult = proved ->
              format('% SZS status Unsatisfiable~n', [])
          ; ProbeResult = depth_limited ->
              format('% SZS status GaveUp~n', [])
          ;
              % ProbeResult = exhausted: comp(7) found no proof of NegFormula,
              % but this does NOT establish that the axioms are genuinely
              % satisfiable — the proof may require multiplicity > 7.
              % Report GaveUp to avoid soundness errors.
              format('% SZS status GaveUp~n', [])
          )
      )
    ).

% Case 2b-special: conjecture that is structurally always false.
%
% Root cause covers two distinct errors (SYN916+1 and LCL679+1.001):
%
%   SYN916+1: conjecture = $false = ~(p0=>p0).
%     nanoCoP negates internally → ~~(p0=>p0) = p0=>p0, trivially provable
%     → spurious Theorem.
%
%   LCL679+1.001: conjecture = ~?[X]:~($false|$false).
%     After translate_operators → ~(ex _:~(~(p0=>p0);~(p0=>p0))).
%     nanoCoP negates → ex _:(p0=>p0) → clausification gives [[~p0,p0]]:
%     a tautological clause that nanoCoP preprocessing removes, leaving the
%     empty matrix → "trivially proved" → spurious Theorem.
%
% Fix: translate Formula to internal form and run simplify_g4mic_formula/2
% (constant-folding with ~(p0=>p0) ≡ ⊥).  If the result is false, return
% CounterSatisfiable without calling nanoCoP.
prove_tptp_internal(Formula, has_conjecture) :-
    translate_formula(Formula, InternalFormula),
    simplify_g4mic_formula(InternalFormula, false),
    !,
    format('% SZS status CounterSatisfiable~n', []).

% Case 2b: has conjecture - nanoCoP validates, G4+ classifies logic level
prove_tptp_internal(Formula, has_conjecture) :-
    current_prolog_flag(occurs_check, OriginalFlag),
    ( catch(
          setup_call_cleanup(
              true,
              (write('nanoCoP : '), nl,
               time(call_with_inference_limit(nanocop_decides(Formula), 2000000, InfResult_hc))),
              set_prolog_flag(occurs_check, OriginalFlag)
          ),
          _,
          (set_prolog_flag(occurs_check, OriginalFlag), fail)
      ),
      InfResult_hc \== inference_limit_exceeded  % Fail if inference limit was exceeded
    ->
      true
    ;
    % nanoCoP failed: distinguish "not a theorem" from "inference limit exceeded"
    ( InfResult_hc == inference_limit_exceeded ->
        format('% SZS status GaveUp~n', [])
    ;
        szs_disproved_status(Formula, DisprStatus),
        format('% SZS status ~w~n', [DisprStatus])
    ),
    !, fail
    ),

    % nanoCoP validated: now determine the logic level (no proof term)
    ( write('g4mic : '), nl,
      time(g4mic_logic_level(Formula, Logic)) ->
        nl,
        format('% Logic level: valid in ~w logic.~n', [Logic]),
        format('% To get proofs (sequent calculus G4 and natural deduction), you can use G4+ at https://g4-mic.vidal-rosset.net/wasm/tinker~n'),
        format('% SZS status Theorem~n', []),
        nl
    ;
        % G4+ could not classify but nanoCoP validated: still a Theorem
        nl,
        format('% To get proofs (sequent calculus G4 and natural deduction), you can use G4+ at https://g4-mic.vidal-rosset.net/wasm/tinker~n'),
        format('% SZS status Theorem~n', []),
        nl
    ).

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
% Uses nanocop_probe/2 (prove2 WITHOUT cut, with time+inference limits)
% for reliable depth-limit detection.
% With [cut,comp(7)], nanoCoP may prune branches and never hit the depth
% limit, so we probe without cut to get a trustworthy answer.
%
% nanocop_probe returns: proved | depth_limited | exhausted
%
% Logic:
%   1. Probe F without cut:
%      - proved       -> Theorem (cut-free search found proof that cut missed)
%      - depth_limited -> GaveUp (comp(7) insufficient, skip ~F test)
%      - exhausted    -> F genuinely not provable, proceed to test ~F
%   2. Probe ~F without cut:
%      - proved       -> Unsatisfiable (F is a contradiction)
%      - depth_limited -> GaveUp
%      - exhausted    -> CounterSatisfiable (both searches exhaustive)

szs_disproved_status(Formula, Status) :-
    nanocop_probe(Formula, ProbeF),
    ( ProbeF = depth_limited ->
        Status = 'GaveUp'
    ; ProbeF = proved ->
        Status = 'Theorem'
    ;
        % ProbeF = exhausted: F is genuinely not provable. Test ~F.
        nanocop_probe(~Formula, ProbeNegF),
        ( ProbeNegF = proved ->
            Status = 'Unsatisfiable'
        ; ProbeNegF = depth_limited ->
            Status = 'GaveUp'
        ;
            % Both searches exhausted.
            % Even for propositional formulas, nanocop_probe at comp(7) is
            % NOT a complete decision procedure: a proof may exist requiring
            % multiplicity > 7.  "exhausted" means only "no proof found within
            % the bound", NOT "formula is CounterSatisfiable".
            % The only safe conclusion is GaveUp.
            % (Structurally false formulas are caught earlier by
            %  simplify_g4mic_formula/2, before reaching this predicate.)
            Status = 'GaveUp'
        )
    ).

% =========================================================================
% FORMULA CLASSIFICATION HELPERS
% =========================================================================

% -------------------------------------------------------------------------
% simplify_g4mic_formula(+F, -Value)
%
% Evaluates the G4mic *internal* representation of a formula (i.e. after
% translate_operators has been applied) to one of: true | false | unknown.
%
% The evaluation treats ~(p0=>p0) as the canonical G4mic encoding of ⊥ and
% (~(p0=>p0) => ~(p0=>p0)) as ⊤.  Any atom or compound predicate that is
% neither of these constants evaluates to `unknown`.
%
% Properties:
%   - If Value = false  → formula is structurally always false (CounterSatisfiable).
%   - If Value = true   → formula is structurally always true  (Theorem).
%   - If Value = unknown → cannot determine; proceed with normal proof search.
%
% Logical correctness: all rules respect classical two-valued semantics.
% The catch-all clause (unknown) is conservative: it never produces a wrong
% true/false for formulas containing real predicate/function symbols.
% -------------------------------------------------------------------------

simplify_g4mic_formula(~(p0=>p0), false) :- !.                        % G4mic ⊥
simplify_g4mic_formula((~(p0=>p0) => ~(p0=>p0)), true) :- !.          % G4mic ⊤
simplify_g4mic_formula(~A, V) :- !,
    simplify_g4mic_formula(A, VA),
    simplify_g4mic_negate(VA, V).
simplify_g4mic_formula((A ; B), V) :- !,        % disjunction (nanoCoP internal)
    simplify_g4mic_formula(A, VA),
    simplify_g4mic_formula(B, VB),
    simplify_g4mic_or(VA, VB, V).
simplify_g4mic_formula((A , B), V) :- !,        % conjunction (nanoCoP internal)
    simplify_g4mic_formula(A, VA),
    simplify_g4mic_formula(B, VB),
    simplify_g4mic_and(VA, VB, V).
simplify_g4mic_formula((A => B), V) :- !,
    simplify_g4mic_formula(A, VA),
    simplify_g4mic_formula(B, VB),
    simplify_g4mic_implies(VA, VB, V).
simplify_g4mic_formula((A <=> B), V) :- !,
    simplify_g4mic_formula(A, VA),
    simplify_g4mic_formula(B, VB),
    simplify_g4mic_iff(VA, VB, V).
% Quantifiers: if body is a constant, quantifier folds (any non-empty domain).
simplify_g4mic_formula(ex _:A, V) :- !,
    simplify_g4mic_formula(A, VA),
    ( VA = false -> V = false ; VA = true -> V = true ; V = unknown ).
simplify_g4mic_formula(all _:A, V) :- !,
    simplify_g4mic_formula(A, VA),
    ( VA = false -> V = false ; VA = true -> V = true ; V = unknown ).
% Any other term (real predicate, variable, etc.) → unknown.
simplify_g4mic_formula(_, unknown).

simplify_g4mic_negate(true, false).
simplify_g4mic_negate(false, true).
simplify_g4mic_negate(unknown, unknown).

simplify_g4mic_or(true,    _,     true)    :- !.
simplify_g4mic_or(_,      true,   true)    :- !.
simplify_g4mic_or(false,  false,  false)   :- !.
simplify_g4mic_or(_,      _,      unknown).

simplify_g4mic_and(false,  _,     false)   :- !.
simplify_g4mic_and(_,      false,  false)  :- !.
simplify_g4mic_and(true,   true,   true)   :- !.
simplify_g4mic_and(_,      _,      unknown).

simplify_g4mic_implies(false, _,     true)   :- !.
simplify_g4mic_implies(_,     true,  true)   :- !.
simplify_g4mic_implies(true,  false, false)  :- !.
simplify_g4mic_implies(_,     _,     unknown).

simplify_g4mic_iff(true,  true,  true)   :- !.
simplify_g4mic_iff(false, false, true)   :- !.
simplify_g4mic_iff(true,  false, false)  :- !.
simplify_g4mic_iff(false, true,  false)  :- !.
simplify_g4mic_iff(_,     _,     unknown).

%%% END OF g4mic PROVER
