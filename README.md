# The Three-Gap (Steinhaus) Theorem in Lean 4

A self-contained, machine-checked formalization of the **three-gap theorem**
(also called the three-distance theorem, or Steinhaus's conjecture) in
[Lean 4](https://leanprover.github.io/) on top of
[Mathlib](https://github.com/leanprover-community/mathlib4).

> **Theorem.** For every real number `a` and every `N ∈ ℕ`, the `N` points
> `{ i·a mod 1 : 0 ≤ i < N }` partition the half-open interval `[0,1)` into gaps
> taking **at most three distinct lengths**; and when exactly three lengths
> occur, the largest is the sum of the other two.

The two formalized statements live in [`ThreeGap.lean`](ThreeGap.lean):

| Statement | Lean declaration |
|---|---|
| At most three distinct gap lengths | `ThreeGap.three_gap_card_le_three` |
| The three lengths are `η⁺`, `η⁻`, `η⁺+η⁻` (largest = sum of the others) | `ThreeGap.three_gap_lengths_eq` |

Both are proved with **no `sorry`** and depend only on the three foundational
axioms `propext`, `Classical.choice`, `Quot.sound` that underlie Mathlib itself.

## What is distinctive

* **Uniform in the rotation number.** The same proof covers rational *and*
  irrational `a`, with no case split. The only previous formalization
  (Mayero's Coq development after van Ravenstein) is restricted to irrational
  `a`. To our knowledge this is the first formalization of the theorem in
  Lean 4.
* **First-return route.** The proof works in `[0,1)` via `Int.fract` (not
  `AddCircle`), through the two return times `η⁺`, `η⁻`. The hard "corner"
  case—that the longest gap is empty—is closed by a self-contained
  return-time/period argument that removes the irrationality restriction.

This is **not** a new mathematical proof of the theorem; elementary proofs valid
for all `a` are classical (e.g. Liang's 1979 rigid-gap argument). The
contribution is the machine-checked formalization. See the companion paper for
the full discussion of prior work.

## The paper

A companion article describing the formalization is in
[`paper/three_gap_theorem_lean.tex`](paper/three_gap_theorem_lean.tex):
*A Lean 4 Formalization of the Three-Gap (Steinhaus) Theorem, Uniform in the
Rotation Number.* Build it with `latexmk -pdf three_gap_theorem_lean.tex`.

## Building

Requires the [Lean 4 toolchain](https://leanprover-community.github.io/get_started.html)
(`elan`); the version is pinned in `lean-toolchain`.

```bash
# fetch the prebuilt Mathlib cache (recommended; avoids recompiling Mathlib)
lake exe cache get
# build the module
lake build
```

To inspect the trust base yourself, add to the end of `ThreeGap.lean`:

```lean
#print axioms ThreeGap.three_gap_card_le_three
-- 'ThreeGap.three_gap_card_le_three' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

and there is no `sorry` in the file:

```bash
grep -c 'sorry' ThreeGap.lean   # 1 match — the word inside a doc-comment only
```

## Companion work

The orbit `{ i·a mod 1 : i < N }` is, for rational `a = α/β`, exactly the
projected point set of a one-dimensional rational cut-and-project construction.
Its gap **sequence** and minimal period (under both the multiset and set
conventions) are studied in a companion project:
<https://github.com/dkunert/cut-and-project>.

## Provenance

The Lean formalization, the proof strategy, and a first draft of the companion
paper were produced by Anthropic's Claude (Claude Opus 4.8) through the
Claude Code agent, under the author's direction and coaching. The correctness
of the results rests not on this provenance but on the Lean 4 kernel: anyone can
rebuild the module and inspect the axiom list above.

## License

MIT — see [`LICENSE`](LICENSE). © 2026 Dirk Kunert.
