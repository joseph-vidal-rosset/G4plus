# G4+ — development notes

Notes for anyone working on this codebase, human or AI assistant. They
record the conventions, the validation procedure, and the results of
past optimisation work, so that finished experiments are not repeated.

## What this project is

G4+ is a first-order theorem prover written in SWI-Prolog. It combines
two engines:

- **g4mic**: a sequent-calculus prover based on Roy Dyckhoff's G4
  calculi (contraction-free intuitionistic sequent calculus). It does
  not merely decide provability — it **classifies** a formula as valid
  in *minimal*, *intuitionistic*, or *classical* logic. This
  three-level classification is the purpose of the project.
- **nanoCoP** (Jens Otten, adapted): a classical non-clausal connection
  prover, used as a filter and as an independent cross-check.

Main file: `g4mic_nanocop.pl`.
Support files: `test_suite.pl`, `i_operators.pl`,
`nanocop20_swi_for_g4plus.pl`, `nanocop_proof.pl`, `nanocop_tptp2.pl`.

Formulas containing equality or function symbols are routed to nanoCoP
by `g4mic_needs_nanocop/1`. This is a deliberate design decision, not a
gap to be closed: axiomatised equality would flood Γ with universal
substitution axioms, and the classification into three logical levels
is not meaningful for such formulas in any case.

## Validation procedure

Passing 116/116 in the test suite is a necessary condition, not the
acceptance criterion. For any change meant to preserve behaviour, the
criterion is **byte-for-byte identity of the output** with a reference
log produced *before* the change.

Generate the reference log first:

```sh
swipl -q -g "consult(g4mic_nanocop), consult(test_suite), run_tests, halt." -t halt \
  | grep -v -E "seconds|Start:|Total execution" > ref.log
```

After each change, regenerate and `diff` against `ref.log`. The filter
removes timing lines only; any other difference is a regression until
shown otherwise.

Compare logs produced by the same SWI-Prolog version. SWI 9.x and 10.x
differ cosmetically in newline placement after `write/1`
(`nanocop_decides: true` on one line versus two); the logical content
is identical.

For any change touching the classification path, check additionally
that the verdicts of `g4mic_logic_level/2` are unchanged over the
registered tests (currently 37 minimal, 6 intuitionistic, 8 classical).

## Benchmarking

Measure CPU time, and **interleave the runs**: run variant A, then B,
then A again, and take medians over 5 to 7 rounds. Machine load drifts
over time, and that drift can exceed the size of the optimisation being
measured. Comparing a batch of A-runs against a later batch of B-runs
produces misleading numbers.

```prolog
statistics(cputime,T0), run_tests, statistics(cputime,T1), D is T1-T0
```

Wall-clock timings taken inside an Emacs inferior-Prolog buffer are
dominated by the cost of displaying the LaTeX output; use them only for
rough comparison against themselves.

## Current work: compartmentalising Γ

`select3_/4` is the dominant cost — roughly 38% of CPU, with 513k calls
and 89k redos for 139k successes. More than three quarters of the scans
of Γ fail. The cause is structural: Γ is a flat list, and each of the
eight left rules scans it independently looking for its own principal
connective.

Plan: hold Γ as compartments keyed by principal connective (atoms,
conjunctions, disjunctions, and the four L→ forms of G4). Each rule
then consults only its own compartment; an empty compartment means
immediate failure with no scan at all. Sorting is incremental — when L&
decomposes `A & B`, it inserts `A` and `B` into their compartments in
constant time, so the classification is never recomputed globally.

The classification should be computed in a **single** insertion
predicate. Beyond avoiding duplication, this turns the exhaustiveness
and mutual exclusivity of the cases into a property that can be stated
and checked, rather than an implicit assumption spread across the
pattern of each rule.

Δ remains a flat list: it is near-singleton in practice (`Delta = [A]`
in most rules), and only R∀ and R∃ `select` on it.

Known pitfall: `select/3` imposes one enumeration order on principal
formulas, and compartments impose another. If proofs diverge, that is a
choice to be made explicit and justified, not a discrepancy to be
worked around. Expected gain: 15-20%, not the full 38%.

Use a dedicated branch, and run the TPTP suite before deploying.

## Optimisations already applied

1. **`g4mic_ax`** — the atomicity guard was tested once per element of
   Γ, and `Delta = [B]` was checked last. Hoisted onto the succedent:
   if `B` is atomic, any `A` unifying with it is atomic too, so the
   guard on `B` alone is equivalent and costs one test per sequent
   instead of one per element. This accounted for 4.09M `\=/2` calls.
   About −15%.
2. **Guard hoists** — `Th > 0` moved before the `\+ member` scan in IP;
   the threshold test moved before `member`/`select` in L∀ and R∃.
   Neutral in time, but free.
3. **`atomic_formula`** — five `\=/2` tests replaced by a
   `connective/2` table indexed on the principal functor.
4. **`memberchk/2`** where the call is a pure test: L⊥ (ground
   arguments), under the `\+` of IP and L→→, and in the if-then-else
   conditions of L∨→, where once-semantics already applies. This
   substitution is **not** valid in L0→: the `minimal` + `B == #`
   branch can backtrack into `member/2`.
5. **Redundant re-search** — after `minimal` fails for all thresholds
   T=0..4, calling `provable_at_level(..., constructive, _)` repeats
   every one of those minimal attempts, since both use the same
   iteration limit. Replaced by `intuitionistic` in four places,
   including `g4mic_logic_level_internal/2` on the TPTP path. Up to
   −30% on hard classical formulas.

Cumulative effect: about −20% on the test suite. All five verified
byte-for-byte on SWI-Prolog 9.0.4 and 10.0.1.

## Approaches already tested and set aside

- **Reordering the inference rules.** Six permutations were measured
  (L⊥ moved early and late, R∀ and L∨→ repositioned): all within 2% of
  each other, which is within measurement noise. Rule order is not the
  lever here.
- **`set_prolog_flag(optimise, true)`.** No measurable gain. It inlines
  arithmetic and drops debugging information; the bottleneck is list
  traversal, which it does not touch.
- **Logtalk.** A microbenchmark of 3M calls gave 0.08s for a direct
  Prolog call against 0.70s for a Logtalk message send — an 8.7×
  overhead. Logtalk is an object layer that compiles *to* Prolog and
  offers encapsulation and protocols; it is not an optimising compiler.
- **QLF pre-compilation.** No effect on execution speed, since
  `consult` already compiles to WAM code. It does cut **process
  startup** by about 5× (0.122s to 0.026s), which is worth having on
  the TPTP path, where SystemOnTPTP spawns one process per problem, and
  in the WASM build, where load time is visible to the user. Regenerate
  it only once the current refactoring is finished, and note that a QLF
  file is tied to the SWI-Prolog version that produced it.

## Conventions

Comments and identifiers in English. Keep explanations concise and
technical: state what changed and why, rather than narrating routine
steps.
