%% File: nanocop_proof.pl  -  Version: 1.1  -  Date: 12 April 2026
%%
%% Purpose: Presentation of connection proof found by nanoCoP
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Enhanced with i.e. annotations for readability
%% by J. Vidal-Rosset & Claude/Anthropic, April 2026
%%
%% Usage:   nanocop_proof(M,P). % where M is a non-clausal matrix,
%%                              %  P is the (non-clausal) connection
%%                              %  proof found by nanoCoP
%%
%% Copyright: (c) 2021 by Jens Otten
%% License:   GNU General Public License


:- assert(proof(leantptp)). % compact, connect, leantptp, readable
:- dynamic(ie_matrix/1).
:- dynamic(ie_varmap/1).


%%% output of nanoCoP proof

nanocop_proof(Mat,Proof) :-
    proof(compact) -> nanocop_compact_proof(Proof) ;
    proof(connect) -> nanocop_connect_proof(Mat,Proof) ;
    proof(readable) -> nanocop_readable_proof(Mat,Proof) ;
    nanocop_leantptp_proof(Mat,Proof).

%%% write compact proof

nanocop_compact_proof(Proof) :-
    write('------------------------------------------------------'),
    nl,
    write('Compact Proof:'), nl,
    write('--------------'), nl,
    write(Proof), nl,
    write('------------------------------------------------------'),
    nl.

%%% write connection proof

nanocop_connect_proof(Mat,Proof) :-
    write('------------------------------------------------------'),
    nl,
    write('Proof for the following non-clausal matrix:'), nl,
    calc_proof(Proof,Mat,Proof1),
    write_matrix(Mat),
    write('Connection Proof:'), nl,
    write('-----------------'), nl,
    write_connect_proof(Proof1),
    write('------------------------------------------------------'),
    nl.

%%% write lean TPTP proof

nanocop_leantptp_proof(Mat,Proof) :-
    write('%-----------------------------------------------------'),
    nl,
    calc_proof(Proof,Mat,Proof1),
    write_matrix_tptp(Mat),
    write_leantptp_proof(Proof1),
    write('%-----------------------------------------------------'),
    nl.

%%% write readable proof (enhanced with i.e. annotations)

nanocop_readable_proof(Mat,Proof) :-
    write('------------------------------------------------------'),
    nl,
    retractall(ie_matrix(_)),
    assert(ie_matrix(Mat)),
    ie_build_varmap(Mat, VarMap),
    retractall(ie_varmap(_)),
    assert(ie_varmap(VarMap)),
    write_explanations,
    write('Proof:'), nl,
    write('------'), nl,
    write('Translation into a non-clausal matrix:'), nl,
    write('    '), portray_clause(Mat), nl,
    write('i.e. a disjunction of clauses:'), nl,
    write('    '), ie_write_matrix(Mat), nl, nl,
    write_introduction,
    calc_proof(Proof,Mat,Proof1),
    write_readable_proof(Proof1), nl,
    write_ending,
    write('------------------------------------------------------'),
    nl.

%%% calculate nanoCoP proof

% calc_proof(Proof,Mat,Proof1) - calculates non-clausal proof Proof1
% of the form [ (Cla,Num,Sub) | [ Proof1, Proof2, ..., ProofN ] ] of
% matrix Mat from compact nanoCoP output Proof

calc_proof([(I^K)^V:Cla],Mat,[(ClaF,I^K,Sub)|Proof]) :-
    member_mat(I,Mat,0:[],(I^_)^W:Cla2),
    calc_cla(Cla,Cla2,Mat,[],[],Cla1,[VL,VS],Proof),
    flatten_cla(Cla1,0,ClaF),
    append(W,VL,VL1), append(V,VS,VS1), Sub=[VL1,VS1].

% calc_clause(Cla,ClaM,M,Path,Lem,Cla1,Sub,Proof) - returns Cla1
% of proof clause literals in Cla, collect variables from original
% clause ClaM, return Proof of subproofs and substition Sub; M is
% the original matrix, Path is the active path, Lem the lemmata

calc_cla([],_,_,_,_,[],[[],[]],[]).

calc_cla([J^_:(I^_)^V:Cla|ClaT],ClaM,M,Path,Lem,Cla1,Sub,Proof) :-
    !, member(J^_:Mat,ClaM), member((I^_)^W:ClaM1,Mat),
    calc_cla(Cla,ClaM1,M,Path,Lem,Cla2,[VL2,VS2],Proof2),
    calc_cla(ClaT,ClaM,M,Path,Lem,Cla3,[VL3,VS3],Proof3),
    ( Cla2=[] -> Cla1=Cla3 ; Cla1=[I:Cla2|Cla3] ),
    append(VL2,VL3,VL4), append(W,VL4,VL1),
    append(VS2,VS3,VS4), append(V,VS4,VS1),
    Sub=[VL1,VS1], append(Proof2,Proof3,Proof).

calc_cla([Lit,ClaPr|ClaT],ClaM,M,Path,Lem,[Lit|Cla1],Sub,Proof) :-
    length([_|Path],IP),  %(Lem=[I:J:_|_] -> J1 is J+1 ; J1=1),
    calc_cla(ClaT,ClaM,M,Path,[IP:Lit|Lem],Cla1,Sub,Proof2),
    ClaPr=IK^V:[NegLit|Cla],
    ( IK=r -> member(I:NegL,Path), NegL==NegLit, Num=r:I, W=[] ;
      IK=l -> member(I:LitL,Lem), LitL==Lit, Num=1:I, W=[] ;
      IK=I^_, Num=IK,  member_mat(I,M,0:[],(I^_)^W:Cla2) ),
    calc_cla(Cla,Cla2,M,[IP:Lit|Path],Lem,Cla3,[VL,VS],Proof3),
    append(W,VL,VL1), append(V,VS,VS1), Sub3=[VL1,VS1],
    flatten_cla(Cla3,0,ClaF), ClaNS=([NegLit|ClaF],Num,Sub3),
    Proof1=[[ClaNS|Proof3]], append(Proof1,Proof2,Proof).

% member_mat(I,Mat,Cla,Cla1) returns clause Cla1 number I in Mat

member_mat(I,[],J:Cla,Cla1) :- !, J\=0, member_mat(I,Cla,0:[],Cla1).
member_mat(I,Mat,_,(I^K)^V:Cla1) :- member((I^K)^V:Cla1,Mat), !.

member_mat(I,[X|M],I2:Cla2,Cla1) :-
    ( ( X=(J^_)^_:Cla ; X=J^_:Cla,atomic(J) ),I>J,J>I2 )
    -> member_mat(I,M,J:Cla,Cla1) ; member_mat(I,M,I2:Cla2,Cla1).

% flatten_cla(Cla,I,Cla1) returns flattend clause Cla1 of Cla

flatten_cla([],_,[]).
flatten_cla([I:C|T],_,C1) :- !, flatten_cla([C|T],I,C1).
flatten_cla([[X|C]|T],I,C1) :- !, flatten_cla([X|C],I,D),
                               flatten_cla(T,I,E), append(D,E,C1).
flatten_cla([Lit|T],0,[Lit|C1]) :- !, flatten_cla(T,0,C1).
flatten_cla([Lit|T],I,[I:Lit|C1]) :- flatten_cla(T,I,C1).

%%% write lean TPTP nanoCoP proof

write_leantptp_proof([(Cla,Num,Sub)|Proof]) :-
    write_leantptp_proof_step([],Cla,Num,Sub),
    write_leantptp_proof(Proof,[1]).

write_leantptp_proof([],_).

write_leantptp_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    write_leantptp_proof_step([I|J],Cla,Num,Sub),
    write_leantptp_proof(Proof,[1,I|J]), I1 is I+1,
    write_leantptp_proof(Proof2,[I1|J]).

write_leantptp_proof_step(I,Cla,Num,Sub) :-
    write('ncf(\''), append(I,[1],I1), write_step(I1),
    write('\',plain,'), writeq(Cla),
    ( Num=(R:N) -> append(_,[H|T],I1), N1 is N+1, length([H|T],N1),
      ( R=r -> write(',reduction(\''), write_step(T), write('\'') ;
               write(',lemmata(\''), write_lstep(T), write('\'') ) ;
      ( I=[] -> write(',start(') ; write(',extension(') ),
      write(Num)
    ),
    ( Sub=[[],_] -> write(')).') ;
                    write(',bind('), write(Sub), write('))).') ),
    nl.

%%% write connection nanoCoP proof

write_connect_proof([(Cla,Num,Sub)|Proof]) :-
    write_connect_proof_step([],Cla,Num,Sub),
    write_connect_proof(Proof,[1]).

write_connect_proof([],_).

write_connect_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    write_connect_proof_step([I|J],Cla,Num,Sub),
    write_connect_proof(Proof,[1,I|J]), I1 is I+1,
    write_connect_proof(Proof2,[I1|J]).

write_connect_proof_step(I,Cla,Num,Sub) :-
    append(I,[1],I1), write_step(I1), write('  '), write(Cla),
    ( Num=(R:N) -> append(_,[H|T],I1), N1 is N+1, length([H|T],N1),
      ( R=r -> write('   (reduction:'), write_step(T) ;
               write('   (lemmata:'), write_lstep(T) ) ;
      write('   ('), write(Num) ), write(')  '),
    ( Sub=[[],_] -> true ; write('substitution:'), write(Sub) ), nl.

%%% write readable nanoCoP proof

write_readable_proof([(Cla,Num,Sub)|Proof]) :-
    write_clause([],Cla,Num,Sub),
    write_readable_proof(Proof,[1]).

write_readable_proof([],_).

write_readable_proof([[(Cla,Num,Sub)|Proof]|Proof2],[I|J]) :-
    write_proof_step([I|J],Cla,Num,Sub),
    write_readable_proof(Proof,[1,I|J]), I1 is I+1,
    write_readable_proof(Proof2,[I1|J]).

%%% write nanoCoP proof step (enhanced: i.e. after Assume)

write_proof_step(I,[Lit|Cla],Num,Sub) :-
    write_assume(I,Lit),
    ie_write_assume_ie(I,Lit),
    ( Num=(R:N) -> append(_,[H|T],I), length([H|T],N),
      (R=r -> write_redu(I,[H|T]) ;
              write_fact(I,[R|T]),
              ie_write_fact_ie(I, Lit)) ;
      write_clause(I,Cla,Num,Sub) ).

write_assume(I,Lit) :-
    write_step(I),write('.'), write(' Assume '), (-NegLit=Lit;-Lit=NegLit) ->
    write(NegLit), write(' is '), write('false.'), nl.

%%% write_clause (enhanced: i.e. showing original clause content)

write_clause(I,Cla,Num,Sub) :-
    write_sp(I), write(' Then clause ('), write(Num), write(')'),
    write(' (i.e. ['),
    ie_write_original_clause(Num),
    write('])'),
    ( Sub=[[],[]] -> true ; write(' under the substitution '),
                            write(Sub),
                            ie_write_subst(Sub),
                            nl, write_sp(I) ),
    ( Cla=[] ->
        write(' is true.')
    ;
        write(' is false if at least one of the following is false.')
    ), nl.

write_redu(I,J) :-
    write_sp(I), write(' This is a contradiction to assumption '),
    write_step(J), write('.'), nl.

write_fact(I,_J) :-
    write_sp(I), write(' This assumption has been refuted above.'), nl.

%%% write matrix, write step number, write spaces

write_matrix(Mat) :- write(Mat), nl, nl.

write_matrix_tptp(Mat) :-
    writeq(ncf(matrix,plain,Mat,input)), write('.'), nl.

write_step([I]) :- write(I).
write_step([I,J|T]) :- write_step([J|T]), write('.'), write(I).

write_lstep([_]) :- !, write('x').
write_lstep([_|T]) :- write_step([T]), write('.x'). %lemma

write_sp([]).
write_sp([I]) :- atom(I), !, write(' ').
write_sp([I]) :- I<1.
write_sp([I]) :- I>=1, write(' '), I1 is I/10, write_sp([I1]).
write_sp([I,J|T]) :- write_sp([J|T]), write(' '), write_sp([I]).

%%% write standard proof explanations, introduction/ending of proof

write_explanations :-
 write('Explanations for the proof presented below:'), nl,
 write('- to solve unsatisfiable problems they are negated'), nl,
 write('- equality axioms are added if required'), nl,
 write('- terms and variables are represented by Prolog terms'), nl,
 write('  and Prolog variables, negation is represented by -'), nl,
 write('- clauses and (sub-)matrices have a unique label I^K:'), nl,
 write('  or I^K^[..]:, where I is a unique number/identifier'), nl,
 write('  and K identifies the instance of clause/matrix I'), nl,
 write('- I:Lit refers to literal Lit in clause number I'), nl,
 write('- in the matrix, I^[t1,..,tn] may represent the atom'), nl,
 write('  P_I(t1,..,tn) or the Skolem term f_I(t1,t2,..,tn)'), nl,
 write('- the substitution [[X1,..,Xn],[t1,..,tn]] represents'), nl,
 write('  the assignments X1:=t1, .., Xn:=tn'), nl, nl.

write_introduction :-
 write('We prove that the given matrix is valid, i.e. for'), nl,
 write('a given substitution it evaluates to true for all'), nl,
 write('interpretations. A matrix is true iff at least one'), nl,
 write('of its clauses is true; a clause is true iff all of'), nl,
 write('its elements (literals and submatrices) are true.'), nl,nl,
 write('The proof is by contradiction:'), nl,
 write('Assume there is an interpretation so that the given'), nl,
 write('matrix evaluates to false. Then in each clause there'), nl,
 write('has to be at least one element that is false.'), nl, nl.

write_ending :-
    write('Therefore, the given matrix is valid because'), nl,
 write('there is no interpretation that makes it false.'), nl,
 write('                                              Q.E.D.'), nl.

%% ===================================================================
%%  i.e. helpers: surgical annotations for readability
%%  Added by J. Vidal-Rosset & Claude/Anthropic, April 2026
%% ===================================================================

%%% ie_write_matrix(+Mat)
%%%   Translate the matrix into readable notation

ie_write_matrix(Mat) :-
    write('['),
    ie_write_mat_clauses(Mat),
    write(']').

ie_write_mat_clauses([]).
ie_write_mat_clauses([!|Rest]) :- !,
    ie_write_mat_clauses(Rest).
ie_write_mat_clauses([_IV:Clause]) :- !,
    ie_write_clause_lits(Clause).
ie_write_mat_clauses([_IV:Clause|Rest]) :-
    ie_write_clause_lits(Clause),
    write(' | '),
    ie_write_mat_clauses(Rest).

ie_write_clause_lits([]) :- write('()').
ie_write_clause_lits([E]) :- !, ie_write_lit_or_sub(E).
ie_write_clause_lits([E|Rest]) :-
    ie_write_lit_or_sub(E), write(' & '),
    ie_write_clause_lits(Rest).

ie_write_lit_or_sub(E) :-
    E =.. [':', _J, SubMat], is_list(SubMat), !,
    write('('),
    ie_write_mat_clauses(SubMat),
    write(')').
ie_write_lit_or_sub(E) :-
    E =.. [':', _J, Lit], !,
    ie_write_lit_or_sub(Lit).
ie_write_lit_or_sub(E) :-
    E =.. ['-', Atom], !,
    write('~ '), ie_write_term_clean(Atom).
ie_write_lit_or_sub(E) :-
    ie_write_term_clean(E).

%%% ie_write_term_clean(+Term)
%%%   Write a term with Skolem and variable renaming

ie_write_term_clean(T) :-
    var(T), !,
    ( ie_varmap(VM), member(T-Name, VM) -> write(Name) ; write(T) ).
ie_write_term_clean(T) :-
    nonvar(T), T =.. ['^', N, Args],
    integer(N), is_list(Args), !,
    atom_concat(sk, N, SkName),
    ( Args = [] -> write(SkName)
    ; write(SkName), write('('),
      ie_write_term_list(Args), write(')')
    ).
ie_write_term_clean(T) :-
    atomic(T), !, write(T).
ie_write_term_clean(T) :-
    T =.. [F|Args], Args \= [], !,
    write(F), write('('),
    ie_write_term_list(Args), write(')').
ie_write_term_clean(T) :- write(T).

ie_write_term_list([]).
ie_write_term_list([T]) :- !, ie_write_term_clean(T).
ie_write_term_list([T|Rest]) :-
    ie_write_term_clean(T), write(', '),
    ie_write_term_list(Rest).

%%% ie_write_original_clause(+Num)
%%%   Look up original clause content from stored matrix

ie_write_original_clause(Num) :-
    ( Num = (I^_K), integer(I),
      ie_matrix(Mat),
      ie_find_clause(I, Mat, OrigClause) ->
        ie_write_clause_lits(OrigClause)
    ; write('?')
    ).

ie_find_clause(I, Mat, Clause) :-
    is_list(Mat),
    member(Elem, Mat),
    ie_find_clause_in(I, Elem, Clause), !.

ie_find_clause_in(I, (I^_)^_:Clause, Clause) :- !.
ie_find_clause_in(I, _:SubMat, Clause) :-
    is_list(SubMat),
    ie_find_clause(I, SubMat, Clause).
ie_find_clause_in(I, _J:SubMat, Clause) :-
    is_list(SubMat),
    ie_find_clause(I, SubMat, Clause).

%%% ie_write_subst(+Sub)
%%%   After substitution, explain: i.e. Var1 := Term1, ...

ie_write_subst(Sub) :-
    ( Sub = [Vars, Terms],
      is_list(Vars), is_list(Terms),
      Vars \= [] ->
        nl, write('                    i.e. '),
        ie_write_bindings(Vars, Terms)
    ; true
    ).

ie_write_bindings([], []).
ie_write_bindings([V], [T]) :- !,
    ie_write_term_clean(V), write(' := '), ie_write_term_clean(T).
ie_write_bindings([V|Vs], [T|Ts]) :-
    ie_write_term_clean(V), write(' := '), ie_write_term_clean(T),
    write(', '),
    ie_write_bindings(Vs, Ts).
ie_write_bindings(_, _).

%%% ie_write_assume_ie(+I, +Lit)
%%%   After Otten's "Assume ... is false.", add i.e. line
%%%   only if the literal needs translation (has Skolem/vars)

ie_write_assume_ie(_I, Lit) :-
    ( ie_needs_translation(Lit) ->
        write_sp(_I),
        write('     i.e. Assume '),
        ie_write_assume_neglit(Lit),
        write(' is false.'), nl
    ; true
    ).

ie_write_assume_neglit(Lit) :-
    ( nonvar(Lit), Lit =.. ['-', Atom] ->
        ie_write_term_clean(Atom)
    ;
        write('~ '), ie_write_term_clean(Lit)
    ).

%%% ie_needs_translation(+Term)
%%%   True if term contains Prolog variables or Skolem terms

ie_needs_translation(T) :- var(T), !.
ie_needs_translation(T) :-
    nonvar(T), T =.. ['^', N, _], integer(N), !.
ie_needs_translation(T) :-
    nonvar(T), T =.. [_|Args],
    member(A, Args), ie_needs_translation(A), !.

%%% ie_build_varmap(+Mat, -VarMap)
%%%   Assign readable names to Prolog variables

ie_build_varmap(Mat, VarMap) :-
    term_variables(Mat, Vars),
    ie_name_vars(Vars,
        ['X','Y','Z','W','U','V','A','B','C','D',
         'X1','Y1','Z1','W1','U1','V1',
         'X2','Y2','Z2','W2','U2','V2'], VarMap).

ie_name_vars([], _, []).
ie_name_vars([Var|Vs], [Name|Names], [Var-Name|Map]) :-
    ie_name_vars(Vs, Names, Map).
ie_name_vars([Var|Vs], [], [Var-GenName|Map]) :-
    length(Vs, K), N is K + 1,
    atom_concat('V', N, GenName),
    ie_name_vars(Vs, [], Map).

%%% ie_write_fact_ie(+I, +Lit)
%%%   After "This assumption has been refuted above.",
%%%   add a line showing what was assumed false, in clean notation,
%%%   so the reader can search for it in the proof.

ie_write_fact_ie(I, Lit) :-
    ( ie_needs_translation(Lit) ->
        write_sp(I),
        write('     (see above: '),
        ie_write_assume_neglit(Lit),
        write(')'), nl
    ; true
    ).
