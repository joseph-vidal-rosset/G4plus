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
% EQUALITY RULES
% =========================================================================

% Reflexivity : Seq = [t = t]

% Symmetry

% Simple transitivity

% Chained transitivity

% Congruence

% Substitution in equality

% Substitution (Leibniz)

% Substitution for logical equivalence
render_bussproofs(equiv_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$\\equiv$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
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

% filter_top_from_gamma/2: Remove top (⊤) from premisses list
filter_top_from_gamma([], []).
filter_top_from_gamma([H|T], Filtered) :-
    ( is_top_formula(H) ->
        filter_top_from_gamma(T, Filtered)
    ;
        filter_top_from_gamma(T, RestFiltered),
        Filtered = [H|RestFiltered]
    ).

% is_top_formula/1: Detect if a formula is top (⊤)
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
