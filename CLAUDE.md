# G4+ — development notes

Notes for anyone working on this codebase, human or AI assistant. They
record the conventions, the validation procedure, and the results of
past optimisation work, so that finished experiments are not repeated.

## Language rule — no exceptions

**Every comment in every source file is written in English.** This holds
for all files, all languages, and all kinds of comment: block headers,
inline notes, `%` comments in Prolog, commented-out code kept for
reference, and commit messages. No French, no mixed-language comments.
Identifiers and predicate names are English too.

Conversation with the user may be in French; the files may not.

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

Passing 116/116 is a necessary condition, not the acceptance criterion.
For any change meant to preserve behaviour, the criterion is
**byte-for-byte identity of the output** with a reference log produced
*before* the change.

Generate the reference log first, and **never delete it**. If it is not
in the repository, regenerate it from the last known-good commit before
touching anything:

```sh
swipl -q -g "consult(g4mic_nanocop), consult(test_suite), run_tests, halt." -t halt \
  | grep -v -E "seconds|Start:|Total execution" > ref.log
```

After each change, regenerate and `diff` against `ref.log`. The filter
removes timing lines only; any other difference is a regression until
shown otherwise.

Byte-for-byte identity is not sufficient on its own, because a broken
renderer can fail silently. Check all five:

```sh
diff ref.log new.log                        # must be empty
grep -c 'missing referenced line' new.log   # must be 0
grep -c 'begin{prooftree}' new.log          # must be 182
grep -oE 'Passed: [0-9]+  Failed: [0-9]+  Errors: [0-9]+' new.log
grep -c 'Disagreement' new.log              # 1 = the banner text only
```

Logic-level classification must stay at 37 minimal / 6 intuitionistic /
8 classical. The reference log is 12696 lines after filtering.

Compare logs produced by the same SWI-Prolog version. SWI 9.x and 10.x
differ cosmetically in newline placement after `write/1`
(`nanocop_decides: true` on one line versus two); the logical content is
identical.

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

## Architecture of proof search — the flat-Γ invariant

Γ is held in two forms at once, and both are threaded through
`g4mic_proves/16` and `g4mic_ax/16`:

- **Eight buckets** (`At, Cj, Dj, I0, IA, IO, IT, Qt`), keyed by
  principal connective. Each rule consults only its own bucket, so a
  rule that cannot fire costs nothing instead of scanning all of Γ.
  This is what removed `select3_/4` as the dominant cost.
- **`Fl`**, the same members as one flat list in **insertion order**
  (most recent first). Proof nodes record `Fl`, so every proof term is
  built directly as the familiar `Fl>Delta` sequent.

`Fl` is not redundant. Everything downstream of search — the
bussproofs renderer, the ND-tree translator, `fitch_g4_proof/8` —
re-derives which formula each rule acted on by searching Γ, and that
re-derivation is sensitive to Γ's order. Bucket order is not insertion
order and cannot be made to reproduce it: buckets are LIFO
*individually*, but a global LIFO cannot be recovered from eight local
LIFOs plus a fixed concatenation order. Dropping `Fl` and flattening the
buckets instead silently breaks 19 natural-deduction trees across 8
tests (measured); no static bucket order fixes it (19, 12 and 27
failures for three orders tried, floor of 7 under hill-climbing).

Two invariants must hold together, and both are load-bearing:

1. **Every rule keeps `Fl` in step with the buckets.** A rule that
   removes a formula from a bucket must remove it from `Fl`
   (`selectchk/3`), and a rule that inserts must cons onto `Fl` in the
   same order the original flat-list code used — `[A, B | G1]` means A
   before B.
2. **`gamma_insert_list/17` inserts right-to-left**, so the head of its
   argument list ends up at the head of its bucket. Folding
   left-to-right reverses them, and every rule that selects from a
   bucket then picks a different principal formula from the one flat-Γ
   order dictates. This was a real bug; it broke DN Dummett and, in
   cascade, part of the rendering.

`gamma_remove/17` is the mirror of `gamma_insert/17`: it deletes a
formula from whichever bucket its principal connective assigns it to.
L0→ needs it, because L0→ enumerates candidates over `Fl` (to preserve
global order) and must then delete the chosen implication from the
buckets.

`normalize_proof_gammas/2` is now the identity, kept only so existing
call sites need no change.

Rules that select from a single bucket (L&, L∨, L∨→, L→→, L∃, L∀, CQ_m,
CQ_c) agree with flat-Γ order automatically: filtering a LIFO sequence
preserves relative order, so the head of `Cj` *is* the first conjunction
of Γ. Only L0→, which ranges over five buckets, had to be rewritten to
enumerate over `Fl`.

## Optimisations already applied

1. **`g4mic_ax`** — the atomicity guard was tested once per element of
   Γ, and `Delta = [B]` was checked last. Hoisted onto the succedent:
   if `B` is atomic, any `A` unifying with it is atomic too, so the
   guard on `B` alone is equivalent and costs one test per sequent
   instead of one per element. This accounted for 4.09M `\=/2` calls.
2. **Guard hoists** — `Th > 0` moved before the `\+ member` scan in IP;
   the threshold test moved before `member`/`select` in L∀ and R∃.
3. **`atomic_formula`** — five `\=/2` tests replaced by a
   `connective/2` table indexed on the principal functor.
4. **`memberchk/2`** where the call is a pure test. Not valid in L0→:
   the `minimal` + `B == #` branch can backtrack into `member/2`.
5. **Redundant re-search** — after `minimal` fails for all thresholds
   T=0..4, calling `provable_at_level(..., constructive, _)` repeats
   every one of those minimal attempts, since both use the same
   iteration limit. Replaced by `intuitionistic` in four places,
   including `g4mic_logic_level_internal/2` on the TPTP path.
6. **Γ compartments plus flat `Fl`** — see the section above.

Cumulative: −27.7% on the suite (1.957 s to 1.415 s), −56.9% on
Pelletier 25, −24.3% on Lepage, all verified byte-for-byte on
SWI-Prolog 10.0.1.

## Approaches already tested and set aside

- **Reordering the inference rules.** Six permutations measured: all
  within 2% of each other, inside measurement noise.
- **`set_prolog_flag(optimise, true)`.** No measurable gain. It inlines
  arithmetic and drops debugging information; the bottleneck is list
  traversal, which it does not touch.
- **Logtalk.** 3M calls: 0.08 s for a direct Prolog call against 0.70 s
  for a Logtalk message send — an 8.7× overhead. Logtalk is an object
  layer that compiles *to* Prolog, not an optimising compiler.
- **QLF pre-compilation.** No effect on execution speed, since
  `consult` already compiles to WAM code. It does cut **process
  startup** by about 5× (0.122 s to 0.026 s), which is worth having on
  the TPTP path, where SystemOnTPTP spawns one process per problem, and
  in the WASM build, where load time is visible to the user. A QLF file
  is tied to the SWI-Prolog version that produced it, so regenerating it
  belongs in the deployment script, not in a manual step.

## Open item

Making the ND translator read the principal formula from the proof term
instead of re-deriving it by searching Γ would remove the coupling that
makes `Fl` necessary, and would let `Fl` be dropped (`select3_/4` is
back at 18.1% because `Fl` is scanned by each rule that fires). It
touches every rule and its ND clause, and it does **not** preserve
byte-for-byte output, so it needs a fresh reference log inspected by
hand. Not urgent.

## Working practice

- Work on a dedicated branch. Run the TPTP suite before deploying.
- Commit a passing state **before** any cleanup, and do the cleanup in a
  separate commit. Mixing the two makes review impossible and hides
  which one caused a breakage.
- Never delete `ref.log` or the scripts that regenerate it.
- Keep explanations concise and technical: state what changed and why,
  rather than narrating routine steps.
