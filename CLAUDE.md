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
6. **Compartmentalising Γ** — `select3_/4` was the dominant cost,
   roughly 38% of CPU, because Γ is a flat list and each of the eight
   left rules scanned it independently for its own principal
   connective. Γ is now held as eight lists (Atoms, Conj, Disj,
   ImplAtom, LandTo, LorTo, LtoTo, Quant) keyed by principal connective,
   threaded as eight separate arguments through `g4mic_proves`/`g4mic_ax`
   (not wrapped in a compound term — see below). Each left rule consults
   only its own bucket; an empty bucket means immediate failure with no
   scan. A single predicate, `gamma_insert/17`, does the classification,
   turning the six-shape partition (atomic, `&`, `|`, `=>`, `!`, `?`)
   into one checkable property instead of an assumption spread across
   every rule. `L0→` deliberately still scans across *all* antecedent
   shapes (ImplAtom, LandTo, LorTo, LtoTo, and the implication-shaped
   members of Quant, in that fixed order) before falling back to the
   shape-specific rules — it fires on any implication whose antecedent
   is already present in Γ, not just the textbook atomic case, and that
   existing behaviour is preserved. Δ stays a flat list, unchanged.
   Enumeration order across buckets does not reproduce the original
   flat-list order (an accepted divergence — can change which valid
   proof is found first and its rendered premise order, never
   provability or classification); this exposed one pre-existing bug in
   the ND-tree renderer's `landto` clause (a blind `select/3` with no
   check it had picked the formula actually consumed), fixed by the same
   set-difference technique `lorto` and `extract_new_formula` already
   used correctly. Proof-tree nodes carry the eight buckets plus Δ as
   their first nine arguments during search;
   `normalize_proof_gammas/2` is the one place that rebuilds the
   original flat-list `Gamma>Delta` sequent, once per completed proof
   (proportional to proof size, not search-tree size), so none of the
   LaTeX/ND-tree/Fitch rendering code had to change. −16.4% CPU (median
   of 7 interleaved rounds against the pre-refactor baseline),
   inferences down 39%. Branch `compartmentalise-gamma`.

Cumulative effect: about −20% on the test suite from items 1-5, plus
−16.4% from item 6. All verified byte-for-byte on SWI-Prolog 9.0.4 and
10.0.1, except item 6, whose validation criterion is documented above
(proof/premise-order divergence is accepted; provability and
classification are not) — see "Validation procedure" for what was
actually checked: 116/116 tests with byte-identical pass/fail and
SZS-status lines, identical classification via `g4mic_logic_level/2`
over all 45 hierarchy tests, and 50 TPTP problems (SYN category, rating
0.00) with zero discrepancies between pre- and post-refactor SZS
status.

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
- **Wrapping Γ's eight compartments in one `g/8` compound term.** The
  first working version of item 6 above did this — Γ as a single
  `g(Atoms,Conj,Disj,ImplAtom,LandTo,LorTo,LtoTo,Quant)` term, rebuilt
  wholesale on every insert/select. Correct (116/116), but slower than
  the flat-list baseline despite 25% fewer inferences: microbenchmark
  showed rebuilding the 9-word `g/8` term costs about 2× a plain list
  cons, since SWI allocates a fresh compound cell even when only one of
  the eight fields changes. Fixed by threading the eight buckets as
  separate arguments instead (7 args → 15 on `g4mic_proves`): unchanged
  buckets flow through as free variable references at zero cost, and
  only the touched bucket pays a cons. Do not reintroduce a Γ wrapper
  term on the search path.

## Conventions

Comments and identifiers in English. Keep explanations concise and
technical: state what changed and why, rather than narrating routine
steps.
