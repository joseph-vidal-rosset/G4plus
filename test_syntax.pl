% Test simple de syntaxe
:- [o_driver].

test1 :-
    write('Test avec syntaxe normale:'), nl,
    prove(~ ~ ((a => b) | (b => a))).

test2 :-
    write('Test avec parenthèses:'), nl,
    prove((~ (~ ((a => b) | (b => a))))).

test3 :-
    write('Test modus ponens:'), nl,
    prove([p, p => q] > [q]).
