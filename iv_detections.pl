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
    write('? Validation failed in strict mode. Formula rejected.'), nl,
    fail.

% Prompt user to continue
prompt_continue :-
    write('Continue despite warnings? (y/n): '),
    read(Response),
    (   Response = y -> true
    ;   Response = yes -> true
    ;   write('? Proof attempt cancelled.'), nl, fail
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
    format('?  ~d WARNING(S) DETECTED:~n', [N]),
    nl,
    maplist(print_warning, Warnings),
    nl,
    write('? TIPS:'), nl,
    write('   o Theorems:  prove(p => q).        % implication'), nl,
    write('   o Sequents:  prove([p] > [q]).     % turnstile ?'), nl,
    write('   o FOL:       use = for equality, <=> for biconditional'), nl,
    nl.

print_warning(warning(bicond_between_terms, A, B)) :-
    format('   ?  (~w <=> ~w): biconditional between terms detected.~n', [A, B]),
    format('      -> Did you mean (~w = ~w)?~n', [A, B]).

% NEW: Sequent syntax warnings
print_warning(warning(list_implication, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove([p, q] > [p & q]).  % CORRECT'), nl,
    write('               prove([p, q] => [p & q]). % WRONG'), nl.

print_warning(warning(list_implication_left, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(list_implication_right, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(atom_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove(p => q).       % CORRECT (implication)'), nl,
    write('               prove(p > q).        % WRONG'), nl,
    write('               prove([p] > [q]).    % CORRECT (sequent)'), nl.

print_warning(warning(formula_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
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
