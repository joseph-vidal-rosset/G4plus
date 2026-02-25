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
