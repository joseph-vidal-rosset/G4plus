% =========================================================================
% OPERATOR DECLARATIONS - Unified for g4mic + nanoCop + TPTP
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
% -------------------------------------------------------------------------
% CORE LOGICAL OPERATORS (shared by all)
% -------------------------------------------------------------------------
:- op( 500, fy,  ~).              % negation
:- op(1000, xfy, &).              % conjunction
:- op(1100, xfy, '|').            % disjunction
:- op(1110, xfy, =>).             % implication
:- op(1130, xfy, <=>).            % biconditional (STANDARD: 1130)
:- op( 500, xfy, :).              % quantifier separator
% -------------------------------------------------------------------------
% QUANTIFIERS - Dual syntax (TPTP + internal)
% -------------------------------------------------------------------------
:- op( 500, fy,  !).              % universal (TPTP): ![X]:
:- op( 500, fy,  ?).              % existential (TPTP): ?[X]:
:- op( 500, fy,  all).            % universal (internal): all X:
:- op( 500, fy,  ex).             % existential (internal): ex X:
% -------------------------------------------------------------------------
% EXTENDED TPTP OPERATORS (from nanocop_tptp)
% -------------------------------------------------------------------------
:- op(1130, xfy, <~>).            % negated equivalence
:- op(1110, xfy, <=).             % reverse implication
:- op(1100, xfy, '~|').           % negated disjunction (NOR)
:- op(1000, xfy, ~&).             % negated conjunction (NAND)
% :- op( 400, xfx, =).              % equality
:- op( 300, xf,  !).              % negated equality (for !=)
:- op( 299, fx,  $).              % TPTP constants ($true/$false)
% =========================================================================
% g4mic specific
% =========================================================================
% Input syntax: sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% =========================================================================
% LATEX OPERATORS (formatted output)
% ATTENTION: Respect spaces exactly!
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % space for quantifiers
:- op(400, fx, ' \\bot ').      % falsity (#)
% LaTeX syntax: sequent turnstile
:- op(1150, xfx, ' \\vdash ').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% End of operators list
