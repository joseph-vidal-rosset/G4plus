%% File: minimal_driver_equal.pl  -  Version: 7.3 FINAL (time seulement dans proves)

:-style_check(-singleton).

:-[nanocop20_swi].
:-[nanocop_proof].
:-[nanocop_tptp2].

% Activer le format d'explication complète d'Otten
:-retractall(proof(_)).
:-assert(proof(readable)).

:-dynamic g4mic_silent_mode/0.

% =========================================================================
% MAIN INTERFACE
% =========================================================================

nanocop_proves(Formula) :-
    % Forcer l'affichage
    retractall(g4mic_silent_mode),

    % Limite d'inférences avec LOGIQUE CORRECTE
    call_with_inference_limit(
        (
            % Détecter l'égalité AVANT traduction
            (nanocop_contains_equality(Formula) ->
                HasEquality = true
            ;
                HasEquality = false
            ),

            translate_formula(Formula, InternalFormula),

            % N'appeler leancop_equal QUE si égalité présente
            (HasEquality = true ->
                leancop_equal(InternalFormula, FormulaToProve)
            ;
                FormulaToProve = InternalFormula
            ),

            % IMPORTANT : PAS DE NÉGATION - prove2 gère la réfutation en interne
            ( time(prove2(FormulaToProve, [cut,comp(7)], Proof)) ->
              Result='Theorem'
            ;
              Result='Non-Theorem'
            ),
            bmatrix(FormulaToProve, [cut,comp(7)], Matrix),
            output_result(Formula, Matrix, Proof, Result),
            % VÉRIFIER le résultat
            Result='Theorem'
        ),
        2000000,
        InfResult
    ),
    % VÉRIFIER SI LIMITE ATTEINTE
    ( InfResult == inference_limit_exceeded ->
        nl,
        write('❌ INFERENCE LIMIT EXCEEDED (2,000,000 inferences)'), nl,
        write('   Formula too complex or invalid'), nl,
        nl,
        fail
    ;
        true
    ),!.

% =========================================================================
% nanocop_decides/1 :   Version SILENCIEUSE (avec stats)
% =========================================================================

nanocop_decides(Formula) :-
    assertz(g4mic_silent_mode),

    % Détecter l'égalité AVANT traduction
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    translate_formula(Formula, InternalFormula),

    % N'appeler leancop_equal QUE si égalité présente
    (HasEquality = true ->
        leancop_equal(InternalFormula, FormulaToProve)
    ;
        FormulaToProve = InternalFormula
    ),

    % IMPORTANT : PAS DE NÉGATION - prove2 gère la réfutation en interne
    prove2(FormulaToProve, [cut,comp(7)], _Proof),
    retractall(g4mic_silent_mode), !.

% =========================================================================
% EQUALITY DETECTION (copié de minimal_driver.pl)
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
        format('╔═══════════════════════════════════════════════════════════════╗~n'),
        format('                    NANOCOP THEOREM PROVER                       ~n'),
        format('╚═══════════════════════════════════════════════════════════════╝~n~n'),
        write('Formula:         '), write(Formula), nl,
        write('Result:    '), write(Result), nl, nl,
        ( var(Proof) ->
            write('No proof found.      '), nl
        ;
            write('═══════════════════════════════════════════════════════════'), nl,
            nanocop_proof(Matrix, Proof),
            write('═══════════════════════════════════════════════════════════'), nl
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

% Bottom/falsum: # is translated to ~(p0 => p0) which represents ⊥
translate_operators(F, (~(p0 => p0))) :-
    nonvar(F),
    (F == '#' ; F == f ; F == bot ; F == bottom ; F == falsum),
    !.

% Top/verum: t is translated to (p0 => p0) which represents ⊤
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
