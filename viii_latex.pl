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

render_hypo(Scope, Formula, Label, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    write(' \\fh '),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Label),
    write('\\\\'), nl.


% render_fitch_indent/1: Genere l'indentation Fitch (\\fa)

render_fitch_indent(0) :- !.

render_fitch_indent(N) :-
    N > 0,
    write('\\fa '),
    N1 is N - 1,
    render_fitch_indent(N1).

render_have(Scope, Formula, Just, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    % Always write \fa at level 0 (for sequents)
    ( Scope = 0 -> write('\\fa ') ; true ),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Just),
    write('\\\\'), nl.

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
    rewrite_name(K, Name).

% Converts f_sk(K,_) to a simple name like 'a', 'b', etc. (two arguments version)
rewrite(f_sk(K,_), J, J, Name) :-
    !,
    rewrite_name(K, Name).

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
    rewrite_name(J, V),
    K is J+1.

rewrite_term(f_sk(K), J, J, N) :-
    integer(K),
    !,
    rewrite_name(K, N).

rewrite_term(f_sk(K,_), J, J, N) :-
    !,
    rewrite_name(K, N).

% NEW: If the term is a simple atom (constant), DO NOT capitalize it
% Because it is an argument of a predicate/function
rewrite_term(X, J, J, X) :-
    atomic(X),
    !.

rewrite_term(X, J, K, Y) :-
    X =.. [F|L],
    rewrite_list(L, J, K, R),
    Y =.. [F|R].

% Generateur de noms elegants pour variables liées
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

% Support lambda calculus
lambda_has(V:_, W) :-
    V == W.

lambda_has(app(P,_,_,_), W) :-
    lambda_has(P, W).

lambda_has(app(_,Q,_,_), W) :-
    lambda_has(Q, W).

lambda_has(lam(V:_,_,_,_), W) :-
    V == W,
    !,
    fail.

lambda_has(lam(_,P,_,_), W) :-
    lambda_has(P, W).

lambda_has('C'(P,_,_), W) :-
    lambda_has(P, W).

%%%%%% Sequents

% Determine proof type (theorem or sequent)
% RENAMED to avoid conflict with proof_type/2 from driver
% This function analyzes the STRUCTURE of a G4 proof, not the syntax of a formula
% Generate Fitch commands according to type and position
fitch_prefix(sequent, LineNum, TotalPremisses, Prefix) :-
    (   LineNum =< TotalPremisses
    ->  (   LineNum = TotalPremisses
        ->  Prefix = '\\fj '  % Big flag for last premiss
        ;   Prefix = '\\fa '  % Normal line for premisses
        )
    ;   Prefix = '\\fa '      % Normal line after premisses
    ).

fitch_prefix(theorem, Depth, _, Prefix) :-
    (   Depth > 0
    ->  Prefix = '\\fa \\fh '  % Small flag for hypotheses
    ;   Prefix = '\\fa '       % Normal line at level 0
    ).

% =========================================================================
% RENDU LATEX BUSSPROOFS
% =========================================================================

% =========================================================================
% LaTeX FORMULA RENDERING
% =========================================================================

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
