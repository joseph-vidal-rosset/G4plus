# Regression report — natural-deduction tree rendering after Γ compartmentalisation

Verified on SWI-Prolog 10.0.1, comparing the compartmentalised
`g4mic_nanocop.pl` against the pre-refactoring version.

## The refactoring works

| | before | after |
|---|---|---|
| test suite (median of 7, interleaved) | 1.974 s | **1.599 s** (−19.0%) |
| Pel_25 | 0.2187 s | 0.1435 s (−34.4%) |
| Lepage | 0.4771 s | 0.3730 s (−21.8%) |
| Pel_26 / Pel_27 | — | −14.5% / −14.6% |
| `select3_/4` share of CPU | 38.2% | **7.5%** |

116/116 pass, 0 disagreements with nanoCoP, and the logic-level
classification is unchanged (8 classical / 6 intuitionistic / 37
minimal). The compartment design is sound and the target was hit.

## The regression

**19 natural-deduction tree renderings are silently lost**, across 8
tests. Each emits:

```
% Warning: missing referenced line(s) or broken tree structure
```

| test | lost trees |
|---|---|
| 8. Universal distribution | 1 |
| 10. Existential elim | 1 |
| 12. Quantifier negation (bicond) | 1 |
| 13. Spinoza: nothing contingent | 1 |
| 14. Lepage p.202 ex.14*-g | 1 |
| 15. Bostock p.279 | 1 |
| 43. Universal instantiation | 1 |
| 46. Pelletier 17 | 12 |

The sequent-calculus proofs and the Fitch (flag-style) output still
render. Only the ND tree fails. All 8 tests involve quantifier rules.

## Root cause

The ND translator does not read from the proof term which formula each
rule acted on — it **re-derives it by searching Γ**, and that search is
sensitive to the order of Γ.

Three places are involved:

- `extract_new_formula/3` (~line 3293) takes the first member of the
  sub-premisses not present in the current premisses. "First" depends on
  list order.
- `fitch_g4_proof(lall(...))` (~line 4122) then looks for the universal
  that generates that formula with `member((![Z-X]:Body), Premisses)`.
- `fitch_g4_proof(l0cond(...))` (~line 3851) re-selects its principal
  implication with `select((Ant => Cons), Premisss, Remaining),
  member(Ant, Remaining)`.

This worked before only by coincidence: the translator's `select/3` and
the prover's `select/3` ran over the *same* flat Γ, so they enumerated
in the same order. `gamma_to_list/9` now flattens the buckets in a fixed
order (At, Cj, Dj, I0, IA, IO, IT, Qt — atoms always first), which is
not the insertion order the translator implicitly assumed.

Concrete instance, test 8 (`![x]:(p(x)=>q(x)) => (![x]:p(x) => ![x]:q(x))`).
The Fitch lines produced are:

```
  3: p(f_sk(1,[]))     [lall(2)]
  4: p(f_sk(1,[]))     [lall(2)]      <- should be p(f_sk)=>q(f_sk), from line 1
  5: q(f_sk(1,[]))     [l0cond(0,4)]  <- line 0 does not exist
```

Two L∀ steps are both attributed to instantiating `![x]:p(x)`; the
major premise of L0→ is then never derived, so `find_context_line/3`
yields 0 and `build_buss_tree/3` fails. Note that `find_context_line/3`
returning 0 rather than failing is a second, latent defect: it converts
a lookup failure into a dangling line reference.

## No static bucket order fixes it

`gamma_to_list/9` was tried with three flattening orders:

| order | ND failures |
|---|---|
| current (At, Cj, Dj, I0, IA, IO, IT, Qt) | 19 |
| implications first (I0, IA, IO, IT, Cj, Dj, At, Qt) | 12 |
| reversed | 27 |

All still pass 116/116. Reordering only moves the failures around: the
translator needs *insertion* order, which no fixed bucket order can
reproduce.

## Fix — two options

### Option B (retained): thread a flat, insertion-ordered Γ alongside the buckets

Keep the eight buckets for search, and thread one additional plain list
holding the same members in insertion order. That list is used *only*
when a proof node is built, so `normalize_proof_gammas/2` reads it
instead of calling `gamma_to_list/9`.

- Restores byte-for-byte identity with the pre-refactoring reference
  log — the strongest validation criterion available here.
- Touches no line of the ND translator, and no rule's logic.
- Cost: one insertion per rule that *succeeds*, replacing the eight
  scans of which seven used to fail. Most of the gain is kept —
  expect roughly −14 to −15% instead of −19%.

`gamma_to_list/9` becomes dead code once nothing calls it; remove it
rather than leaving a second, divergent notion of "Γ as a list" in the
file.

### Option A (later, optional): record the principal formula in the proof term

Record in each proof node which formula the rule acted on, instead of
re-deriving it:

- `lall` records the instantiated universal and the instance;
- `l0cond` records the implication it fired on;
- likewise for every rule whose ND clause calls `extract_new_formula/3`
  or re-selects from Γ.

The translator then reads that argument instead of guessing. This
removes the coupling permanently rather than restoring a coincidence,
and it is the change that would have prevented this class of bug in the
first place. It is also the more invasive one: it touches every rule and
its ND clause, and it does **not** restore byte-for-byte identity — Γ
stays in bucket order in the rendered output, so a new reference log has
to be generated and inspected by hand.

Do B first: it yields a validatable, deployable state immediately. A is
a robustness improvement that can follow, and it will be safer to
attempt once a trustworthy reference log exists again.

A third possibility — aligning the translator's enumeration with
`gamma_all_implications_select/12` — was considered and rejected: it is
not reliable for `lall`, where several universals can produce a matching
instance and the choice is genuinely unrecoverable by search.

## Also worth checking

`decide_silent/3` returns the **raw** proof term, with the eight bucket
arguments, because `normalize_proof_gammas/2` is applied downstream at
the two rendering call sites. Any external caller of `decide_silent/3`
that expects `Gamma > Delta` nodes now receives 9-argument compartment
terms. Either normalise inside `decide_silent/3` or document the change
at its definition.

## Note on the validation procedure

CLAUDE.md's byte-for-byte criterion was not met, and the design note in
the source anticipates this ("an accepted, documented divergence").
That note is right that provability and logic-level classification are
untouched — both verified here. But it claims the divergence affects
only "which valid proof is found first (and hence premise order in
rendered output)", and that is where it under-reads the consequence: in
this codebase the *rendering* depends on Γ order, so a change of order
does not merely reorder the output, it breaks part of it.

Whenever the byte-for-byte check is deliberately set aside, the
substitute must be an explicit check on each downstream consumer. Add
both of these to the validation routine, and to CLAUDE.md:

```sh
grep -c 'begin{prooftree}' run.log        # must match the reference count
grep -c 'missing referenced line' run.log # must be 0
```

Either one would have caught all 19 failures immediately.

## Acceptance criteria for the fix

1. `diff` against the pre-refactoring reference log is empty.
2. Zero occurrences of `missing referenced line`.
3. `begin{prooftree}` count equals the reference (182 on the current
   suite; the compartmentalised version produces 163).
4. 116/116, zero disagreements, classification 8/6/37 unchanged.
5. Timing measured with interleaved runs, medians over 5-7 rounds.
