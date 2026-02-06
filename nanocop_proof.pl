%% File: nanocop_proof.pl  -  Version: 1.0  -  Date: 1 May 2021
%%
%% Purpose: Presentation of connection proof found by nanoCoP
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage:   nanocop_proof(M,P). % where M is a non-clausal matrix,
%%                              %  P is the (non-clausal) connection
%%                              %  proof found by nanoCoP
%%
%% Copyright: (c) 2021 by Jens Otten
%% License:   GNU General Public License


:- assert(proof(leantptp)). % compact, connect, leantptp, readable


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

%%% write readable proof

nanocop_readable_proof(Mat,Proof) :-
    write('------------------------------------------------------'),
    nl,
    write_explanations,
    write('Proof:'), nl,
    write('------'), nl,
    write('Translation into a non-clausal matrix:'), nl,
    write('    '), portray_clause(Mat), nl,nl,
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

%%% write nanoCoP proof step

write_proof_step(I,[Lit|Cla],Num,Sub) :-
    write_assume(I,Lit),
    ( Num=(R:N) -> append(_,[H|T],I), length([H|T],N),
      (R=r -> write_redu(I,[H|T]) ; write_fact(I,[R|T])) ;
      write_clause(I,Cla,Num,Sub) ).

write_assume(I,Lit) :-
    write_step(I),write('.'), write(' Assume '), (-NegLit=Lit;-Lit=NegLit) ->
    write(NegLit), write(' is '), write('false.'), nl.

write_clause(I,Cla,Num,Sub) :-
    write_sp(I), write(' Then clause ('), write(Num), write(')'),
    ( Sub=[[],[]] -> true ; write(' under the substitution '),
                            write(Sub), nl, write_sp(I) ),
    ( Cla=[] -> write(' is true.') ;
      write(' is false if at least one of the following is false:'),
      nl, write_sp(I), write(' '), write(Cla) ), nl.

write_redu(I,J) :-
    write_sp(I), write(' This is a contradiction to assumption '),
    write_step(J), write('.'), nl.

write_fact(I,J) :-
    write_sp(I), write(' This assumption has been refuted in '),
    write_lstep(J), write('.'), nl.

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
