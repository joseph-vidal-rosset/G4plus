% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE
% =========================================================================
:- dynamic fitch_line/4.
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
% R∨ (Intro Or)
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L∨ (Elim Or) - Ternary
build_tree_from_just(lor(DisjLine, HypA, HypB, GoalA, GoalB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !,
    build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(GoalA, FitchLines, TreeA),
    build_buss_tree(GoalB, FitchLines, TreeB).

% L∨-> (Left disjunction to conditional)
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Conjunction Rules --
% L∧ (Elim And)
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R∧ (Intro And)
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% L∧-> (Left conjunction to conditional)
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Falsum / Negation Rules --
% L⊥ (Bot Elim)
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
% L∃ (Exist Elim)
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines,
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree),
    build_buss_tree(GoalNum, FitchLines, GoalTree).

% R∃ (Exist Intro)
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% L∀ (Forall Elim) - Special case when UnivLine = 0 (not found in context)
build_tree_from_just(lall(0), _LineNum, Formula, _FitchLines, axiom_node(Formula)) :-
    !.

% L∀ (Forall Elim) - Normal case
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% R∀ (Forall Intro)
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
% For rcond (→I): check for vacuous discharge
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

% =========================================================================
%   END OF ND TREE STYLE PRINTER
% =========================================================================
