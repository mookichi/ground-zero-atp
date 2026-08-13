# HoTT Book Exercises

Solutions to selected exercises of the
[HoTT book](https://homotopytypetheory.org/book/) (*Homotopy Type Theory:
Univalent Foundations of Mathematics*, 1st ed.), formalized against this
library.  Each file solves the exercises of one book chapter in the `hott`
language.

These files serve two purposes:

* **Worked examples of the idioms in [`AIPROVER.md`](../../AIPROVER.md)** —
  the exercise proofs are ordinary `hott` code and exhibit the parser
  conventions, the equality/tactic toolkit, and the quotient-HIT patterns the
  guide describes.
* **Practice material** — the chapters import each other
  (`Chap1 → Chap3`, `Chap2 → Chap4 → Chap5`) so they are also a model of how to
  layer proofs incrementally.

## Chapter index

| File | Book chapter | Exercises | Declarations |
|---|---|---|---|
| [`Chap1.lean`](Chap1.lean) | Ch. 1 — Type theory | 1.1–1.16 | 55 `definition` |
| [`Chap2.lean`](Chap2.lean) | Ch. 2 — Homotopy type theory | 2.1–2.19 | 21 `definition`, 1 `theorem` |
| [`Chap3.lean`](Chap3.lean) | Ch. 3 — Sets and logic | 3.1–3.24 | 26 `definition`, 25 `lemma`, 18 `theorem` |
| [`Chap4.lean`](Chap4.lean) | Ch. 4 — Equivalences | 4.1–4.9 | 11 `definition`, 19 `lemma`, 13 `theorem` |
| [`Chap5.lean`](Chap5.lean) | Ch. 5 — Induction | 5.1–5.17 | 20 `definition`, 3 `lemma`, 1 `theorem` |
| [`Chap6.lean`](Chap6.lean) | Ch. 6 — Higher inductive types | 6.2, 6.5, 6.7–6.12\* | 15 `definition`, 12 `lemma`, 5 `theorem`, 1 `corollary` |

\* Ch. 6 exercises 6.1 (dependent-path concatenation + torus induction
principle), 6.3 (T² ≃ S¹ × S¹), 6.4 (dependent n-loops), 6.6 (the universe
containing S² is not a 2-type) and 6.13 (funext from ‖𝟚‖) are not
formalized here.  The rest are solved: 6.2/6.5 (suspension vs. spheres,
which is definitional in this library since `S (n+1) := Susp (S n)`),
6.7 (inverses in a monoid form a proposition), 6.8 (list monoid laws + the
free-monoid extension property), 6.9 (unnatural endomorphisms under LEM),
6.10 (interval implies funext, with the quasi-inverse verified), 6.11
(universal property of suspension) and 6.12 (ℤ ≃ ℕ + 𝟏 + ℕ).

Chapter contents at a glance: Ch. 1 covers functions, products, Σ-types and
path basics; Ch. 2 paths, equivalences, univalence and pullbacks; Ch. 3 sets,
propositions and truncation-style logic; Ch. 4 the equivalence machinery
(`adjointify`, `idtoeqv`, `transport`, function extensionality); Ch. 5
W-types and induction principles; Ch. 6 higher inductive types (circle,
suspension, interval, and the library's derived funext).

## Running

```sh
lake env lean GroundZero/Exercises/Chap1.lean
```

Each chapter compiles against the built library (`lake build` first).  The
files are included in the root [`GroundZero.lean`](../../GroundZero.lean)
import index, so they are part of the full `lake build` too.

## Writing new exercises

* Follow the existing layout: an `-- Exercise X.Y` comment above each solution
  (capitalization varies across the existing files), `hott definition` for
  construction, `hott lemma`/`hott theorem` for proofs.
* Reuse library machinery first (`GroundZero.Theorems`, `GroundZero.Types`,
  `GroundZero.HITs`) — the chapters above import only what they need and layer
  on top of each other.
* When you hit a parser or name-resolution trap, add it to
  [`AIPROVER.md`](../../AIPROVER.md) (parser gotchas G1–G5, name resolution
  N1–N4) — it is a living document maintained together with this index.

## See also

* [HoTT book](https://homotopytypetheory.org/book/) — the source text.
* External solution collections for cross-checking:
  * https://github.com/HoTT/Coq-HoTT/blob/master/contrib/HoTTBookExercises.v
  * https://github.com/HoTT/book/blob/master/exercise_solutions.tex
  * https://github.com/pcapriotti/hott-exercises
  * https://github.com/ezyang/HoTT-coqex
* [Root `README.md`](../../README.md) — library overview and the full
  documentation index.
