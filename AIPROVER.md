# Ground Zero: A Guide for Automated Theorem Provers

This document collects the practical knowledge an automated theorem prover (or an
AI-assisted proof engineer) needs to work effectively with the
[Ground Zero](https://github.com/rzrn/ground_zero) HoTT library for Lean 4.

It is written from hard-won experience: every section below is grounded in
errors that were actually hit, diagnosed, and fixed while developing proofs on
top of this library.  Reading this file first will save hours of iteration.

> **Maintenance convention.**  This is a *living* document.  Whenever a working
> session discovers a parser gotcha, a name-resolution trap, a reusable proof
> pattern, or a workflow detail, it must be added here (or the checklist
> updated).  Future sessions that work with this library should consult this
> file before writing proofs.  Keep the final checklist in sync with the body.

## Related resources

* [Root `README.md`](README.md) — project overview, the HIT-by-quotient design,
  and the dependency map.  The **Documentation** section there is the index
  into this file and the exercises.
* [`GroundZero/Exercises/README.md`](GroundZero/Exercises/README.md) — index of
  the HoTT-book exercise solutions (`Chap1.lean`–`Chap6.lean`), which are the
  best worked examples of the idioms below.
* [`THEOREM_TIERS.md`](THEOREM_TIERS.md) — a tiered catalog of the library's
  theorems: Tier 1 foundational core to try first, Tier 2 standard lemmas,
  Tier 3 HIT/type-construction theorems, Tier 4 domain applications, and an
  at-a-glance table of all axioms.  Complements Section 5 (which equality
  lemmas are the workhorses) with the full inventory.
* Reference implementations, cited throughout: `Coeq`, `Generalized`,
  `UnorderedTriple` (quotient HITs, Section 6); `GroundZero/Meta/Symm.lean`
  (symmetry typeclasses, Section 7); `PosDef.lean`, `KernelLearn.lean`
  (bilinear forms, `biFormSymI`).

---

## 1. First principles

* **The `hott` elaborator is a different language.**  Every `hott …` declaration
  is parsed and elaborated by `GroundZero/Meta/HottTheory.lean`, *not* by the
  stock Lean command.  The differences from plain Lean are the single largest
  source of wasted iterations (Section 3).
* **`=` is the hott identity type `GroundZero.Types.Id`, not core `Eq`.**
  `GroundZero.Types.Id` also provides `⬝` (path composition, `Id.trans`),
  `⁻¹` (path inverse, `Id.inv`), `ap`, and friends.
* **Every declaration is checked against HoTT consistency.**  The library ports
  the *large eliminator checker*: proving `p = q` for arbitrary paths `p q` by
  `cases` fails at declaration time.  Classical axioms (`Classical.choice` and
  friends) are prohibited; reasoning must stay constructive.  This is by design
  (see the root `README.md`).
* **`[GroundZero]` is an implicit instance parameter** injected into axioms.
  Most hott declarations carry it automatically; pure structural lemmas (e.g.
  class projections composed with `Id.trans`) may not need it.
* **Reuse before writing.**  The library already contains a great deal of
  machinery: `GroundZero.Algebra.rpow` (real powers), `ring.comm.mulComm`,
  finite sums, bilinear forms, `IsSymmetric`/`IsSymmInvariant` classes, and the
  `symm` tactic.  Search for it before reimplementing.

## 2. The `hott` language: declaration kinds and semantics

All of the following are parsed by the hott elaborator:

| Syntax | What it becomes | Transparency |
|---|---|---|
| `hott definition` / `hott lemma` / `hott theorem` / `hott corollary` / `hott remark` / `hott statement` | a regular Lean `def` (the kind name is a convention, not a semantic difference) | **transparent** — `unfold`/`dsimp` work, definitional equality goes through |
| `hott abbrev` | a `def` with `[reducible]` + `[inline]` attributes | transparent |
| `hott axiom X : T` (no body) | a real `axiom` with a `[GroundZero]` hypothesis | opaque |
| `hott axiom X := body` | a `def` marked `[hottAxiom]` (a "computable axiom") | **reducible** — the checker treats it as safe, and defeq *does* see through it (this is why `Quotient.elem x` reduces) |
| `hott opaque axiom X := body` | a Lean `opaque` marked `[hottAxiom]` | **truly opaque** — defeq does *not* see through it |
| `hott instance …` | an `instance` (auto-named) | transparent |
| `hott example …` | checked without modifying the environment | — |
| `hott check …` / `hott prohibit …` | HoTT-consistency utilities | — |

Consequences that matter in practice:

* Prove new theorems with `hott definition`/`hott lemma` (transparent) whenever
  possible — downstream `exact`/`unfold`/`rw` then work by definitional
  equality.
* Reserve `hott opaque axiom` for genuine β-rules that cannot be computation
  (`Quotient.recβrule`, `Quotient.indβrule`, `Quotient.line`).  Because they are
  opaque, statements *mentioning* them need the β-rule axioms to be usable;
  see the quotient recipe (Section 6).
* `hott axiom` *with* a body is a good middle ground: reducible, but exempt
  from the ordinary hott-checking restrictions where appropriate.

## 3. Parser gotchas (the top time-sinks)

These are the errors you will hit within minutes of writing hott code.  All
were observed in real sessions.

**G1. Typed lambdas must use `=>`, not `,`.**
```lean
-- ✗ fails: unexpected token ','
λ t : V × V × V, f t.1
-- ✓ works
λ t : V × V × V => f t.1
```
(The hott term parser wants `=>`; the comma form is rejected.)

**G2. Typed Π-binders must be parenthesized.**
```lean
-- ✗ fails: unexpected token ':'  (expected ',')
Π t : V × V × V, C (elem t)
-- ✓ works
Π (t : V × V × V), C (elem t)
```
Untyped binders are fine either way: `Π x y z, …` and `Π (x y z : V), …` both work.

**G3. `{ … }, { … }` focus blocks are rejected inside `begin`.**
```lean
-- ✗ fails: unexpected token ','; expected 'end'
begin
  { intro x; exact a },
  { intro y; exact b }
end
-- ✓ works: sequential ;-chains (each chain targets the next open goal)
begin
  intro x; exact a;
  intro y; exact b
end
```
The same applies to `fapply …;` followed by comma-separated blocks — chain with
`;` instead.  `with | ctor args => …` (see G4) is also fine.

**G4. `induction` on an indexed inductive auto-introduces constructor
arguments under inaccessible names (`x✝`).**  Rename them explicitly:
```lean
induction H using UnorderedTriple.rel.casesOn with
| swap12 x y z => exact inst.swap12 x y z
| swap23 x y z => exact inst.swap23 x y z
```
Without the `with` clause, `x y z` are in the context as `x✝` and cannot be
referenced by name.

**G5. `#failure`/`#success` take exactly two terms separated by `≡`.**
```lean
#success idfun₁ zero ≡ ez
#failure idfun₁ ≡ idfun₂
```
`≡` is a *literal* token of the command, not an infix.  `#failure` reports
when the two sides turn out to be definitionally equal; if the terms
themselves fail to elaborate, the command errors instead of "failing as
expected".  This command is finicky — test it in a scratch file before
relying on it.

## 4. Name resolution and namespaces

**N1. `Quotient.rec`/`Quotient.ind` resolve to *core* Lean's Setoid quotient
outside `namespace GroundZero.HITs`.**
```lean
open GroundZero.HITs
#check @Quotient.rec   -- Π {α} {s : Setoid α} …   ← core, NOT the hott one
#check @Quotient.elem  -- A → GroundZero.HITs.Quotient R   ← hott (no core rival)
```
Inside `namespace GroundZero.HITs` the hott `Quotient` (and its `rec`, `ind`,
`elem`, `line`, `recβrule`, `indβrule`) resolve correctly.  HIT files
(`GroundZero/HITs/*.lean`) therefore all live inside that namespace.  If you
need hott `Quotient` machinery outside it, use fully qualified names.

**N2. `R.τ` (and `@ring.comm.mulComm R.τ …`) fails to resolve inside
`namespace GroundZero.HITs`** even with `open GroundZero.Algebra`
(`Unknown constant GroundZero.HITs.R.τ`).  Workarounds: use the fully
qualified `GroundZero.Algebra.R.τ`, or put the ℝ-specific demo/lemma in a
namespace *outside* `GroundZero.HITs`.

**N3. Short-name resolution inside library namespaces can fail; fully qualify.**
Opening a namespace (`open GroundZero.Algebra`) makes names available at top
level and in most nested namespaces, but resolution is *not* guaranteed inside
deeply nested library namespaces — in particular `R.τ` fails inside
`namespace GroundZero.HITs` even with the `open` repeated inside the block.
The robust rule: when a short name fails to resolve, use the fully qualified
name (`GroundZero.Algebra.R.τ`) or move the code outside that namespace;
don't assume re-opening fixes it.

**N4. Tuples are nested pairs.**  `(x, y, z)` is `(x, (y, z))`; project with
`t.1`, `t.2.1`, `t.2.2`.

## 5. Equality, tactics, and rewriting

* `=` on hott `Id` supports `⬝` (`Id.trans`), `⁻¹` (`Id.inv`), and `ap`
  (`Id.ap`).  Basic propositional lemmas (`Id.assoc`, `Id.rid`, `Id.compInv`,
  `Equiv.mapFunctoriality`, `Equiv.transport`, …) are in
  `GroundZero.Types.Id` and `GroundZero.Types.Equiv`.
* **Core `rw` cannot rewrite hott `Id`-equalities** (measured on Lean 4.28):
  `MVarId.rewrite` accepts only native `Eq`/`Iff`/definitional equations and
  rejects hott `Id` lemmas with `Invalid rewrite argument`.  The proven
  workhorses are `unfold`/`dsimp`, `transitivity`, `exact`/`apply` chains, and
  — for the free-groupoid fragment — the `path_simp` tactic below.
* **`path_simp`** (in `GroundZero/Meta/Tactic.lean`, exposed globally)
  closes path-algebra goals automatically.  Level 1 (free-groupoid fragment):
  right-associates (`(p ⬝ q) ⬝ r ↦ p ⬝ (q ⬝ r)`), cancels `p ⬝ p⁻¹ ↦ idp a`
  and `p⁻¹ ⬝ p ↦ idp b` (even inside contexts, via `ap` congruence), drops
  `p ⬝ idp b ↦ p`, pushes inverses in (`(p ⬝ q)⁻¹ ↦ q⁻¹ ⬝ p⁻¹`), and applies
  `(p⁻¹)⁻¹ ↦ p` and `ap f p⁻¹ ↦ (ap f p)⁻¹`.  Level 2 (higher-order):
  `ap` naturality (`ap f (p ⬝ q) ↦ ap f p ⬝ ap f q` and reverse), the
  Eckmann–Hilton fragments on 2-paths (`ν ⬝ κ ↦ ν ⋆ κ ↦ ν ⋆′ κ ↦ κ ⬝ ν`, via
  `Whiskering.loop₁`/`compUniq`/`loop₂`/`comm`), and whiskering rewrites
  derived from *context* 2-path hypotheses (`rwhs`/`lwhs`: from `h : p = q`
  derive `p ⬝ r ↦ q ⬝ r` and `r ⬝ p ↦ r ⬝ q`).  It then closes the residual
  with `reflexivity`.  Examples (all axiom-free, `#print axioms` verified):
  `p ⬝ Id.inv p = idp a`, `(p ⬝ q) ⬝ Id.inv q = p`,
  `p ⬝ (Id.inv p ⬝ q) = q`, `Id.inv (p ⬝ q) ⬝ p = Id.inv q`,
  `{ν κ : loop = loop} : ν ⬝ κ = κ ⬝ ν` (Eckmann–Hilton on Ω(S¹), in
  `GroundZero/HITs/Circle.lean`).
  `path_simp` FAILS on non-path goals, so `first | path_simp | …` falls
  through cleanly.  It is implemented as a congruence rewrite engine
  (`Meta.isDefEq` matching + proof reconstruction via
  `Id.trans`/`Id.symm`/`Id.ap`), since core `rw` cannot handle hott `Id`;
  regression `hott example`s live at the end of `GroundZero/Types/Id.lean`
  (Section 8.7) and the S¹ demonstrations in `GroundZero/HITs/Circle.lean`.
  Note: the rule lemmas are referenced by *single-backtick* name literals —
  double-backtick names are resolved by the elaborator and fail to compile
  in modules that do not import `GroundZero.Types.Id`.  Matching quirks:
  the head-constant pre-check compares *canonical* names, so the reducible
  alias `Id.inv` (= `symm`) matches `symm`-headed patterns; the pre-check is
  what keeps `⬝`-patterns from firing on the whiskering defs (`horizontalComp₁`
  etc. unfold to `trans`-soups that would re-whisker forever).  On `S¹`,
  `tEH`/`tCancel` on `{ν κ : loop = loop}` depend only on `Quot.sound` (the
  HIT's own quotient axiom) — `path_simp` itself introduces no axioms.
* **Core Lean's `symm` tactic (the `[symm]` attribute machinery) is inert on
  hott `Id`-equalities.**  The library shadows `symm` for *function-level*
  symmetry (goals `k x y = k y x` with an `IsSymmetric k` instance) and keeps
  `symmetry` for relation-level goals.  `reflexivity` and `symmetry` are the
  hott-native tactics.
* `dsimp`/`unfold` see through `hott definition`s but not through
  `hott opaque axiom`s (Section 2).  When a goal mentions an opaque β-rule,
  the corresponding β-rule *lemma* must be applied explicitly.
* `:= by …` tactic blocks are supported inside hott declarations (used in the
  library, e.g. `hott corollary … := by apply coerceRefl`), and hott `begin`
  blocks support `fapply`, `existsi`, and `<;>` composition.
* `notation`/`infix` are plain Lean — usable inside hott files.

## 6. The quotient-HIT recipe (the Coeq pattern)

The library constructs HITs as quotients (`GroundZero/HITs/Quotient.lean`),
following `Coeq` (`GroundZero/HITs/Coequalizer.lean`) and `Generalized`
(`GroundZero/HITs/Generalized.lean`).  The canonical shape of a new quotient
HIT:

```lean
namespace GroundZero.HITs
universe u v

inductive MyHIT.rel (A : Type u) : B → B → Type u where
  | ctor (…) : rel A … …

hott definition MyHIT (A : Type u) := Quotient (MyHIT.rel A)

namespace MyHIT
  hott definition elem  {A} : B → MyHIT A := Quotient.elem
  hott definition resp  {A} … : elem … = elem … := Quotient.line (rel.ctor …)

  hott definition ind {A} {C : MyHIT A → Type v} (elemπ : …) (glueπ : …) : Π q, C q :=
  begin
    fapply Quotient.ind;
    intro t; exact elemπ t;
    intros u v H;
    induction H using MyHIT.rel.casesOn with
    | ctor x y z => exact glueπ x y z
  end

  attribute [induction_eliminator] ind

  hott definition indβrule … := @Quotient.indβrule _ (rel A) _ _ _ _ _ (rel.ctor …)

  hott definition rec {A} {B : Type v} (f : B → C) (ρ : …) : MyHIT A → C :=
  begin
    fapply ind;
    intro t; exact f t;
    intros …; exact pathoverOfEq (resp …) (ρ …)
  end

  hott definition recβrule … :=
  begin
    dsimp [rec];
    apply pathoverOfEqInj (resp …);
    transitivity; symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end
end MyHIT
end GroundZero.HITs
```

Notes:

* `rec` is built on `ind` with `pathoverOfEq` (never by calling the raw
  `Quotient.rec` axiom), and `recβrule` follows the fixed chain
  `pathoverOfEqInj` → `apdOverConstantFamily` → `indβrule` → `reflexivity`.
  Copy this verbatim and adapt names; it compiles.
* `elem x` is definitionally reducible (a body-carrying `hott axiom`), so
  `rec f ρ (elem x)` is defeq to `f x`; but `line g` is opaque, which is why
  `recβrule` must be an axiom.
* `Quotient.ind` and `Quotient.rec` (the hott ones) are only reachable inside
  `namespace GroundZero.HITs` (see N1).  If a lemma needs to be usable outside
  that namespace, keep the *public* API (rec/βrules) inside the `MyHIT`
  namespace, which is fine since they are plain hott definitions.

## 7. Symmetry as a first-class citizen (typeclasses)

The library promotes function-level symmetry to a typeclass, turning repeated
symmetric-proof boilerplate into instance resolution:

* `IsSymmetric k` (`GroundZero/Meta/Symm.lean`): `k x y = k y x` for a binary
  function.  Once an instance exists, `by symm` closes any `k x y = k y x`
  goal automatically.
* `IsSymmInvariant f`: ternary symmetry from the two generators
  `swap12 : f x y z = f y x z` and `swap23 : f x y z = f x z y`.  The other
  four Σ₃ permutations are derived (`IsSymmInvariant.cycle123/cycle132/reverse`).
* **`IsSymmInvariant` is exactly the resp condition of the quotient
  `UnorderedTriple V := V³ // Σ₃`** (`GroundZero/HITs/Unordered.lean`): the
  typeclass witnesses are handed to `UnorderedTriple.rec` as the resp proofs,
  giving `UnorderedTriple.prod3UP f : UnorderedTriple V → B` for free.
* Gram-matrix symmetry is derived once from an instance:
  `PosDef.biFormSymI` takes `[IsSymmetric K]` and yields
  `Σᵢⱼ (cᵢ dⱼ) K(xᵢ,xⱼ) = Σᵢⱼ (dᵢ cⱼ) K(xᵢ,xⱼ)` by typeclass synthesis.

Conventions: register the proof *once* as an instance, then let synthesis do
the work; instance binders `[inst : …]` are the library norm (cf. `[orfield T]`).
The `IsSymmetric` instance must hold the real proof — deriving it from itself
(`⟨kernelSym ε⟩` where `kernelSym` is `by symm`) creates a definitional cycle;
prove the instance from the *source* lemma instead.

## 8. Verification workflow

Follow this order — it catches most failures early and cheaply:

1. **Probe first.**  Prototype the new construction in `/tmp/probe.lean` with
   `import GroundZero`, iterate to a clean `lake env lean` exit code, *then*
   integrate into the library.
2. **Single-file compile.**  `lake env lean Path/To/File.lean`.
3. **Integration probe.**  From a separate file, `import` the module and
   `#check` every new symbol; exercise each with a `hott example`.
4. **Stale-olean trap.**  After editing a file, `lake env lean` alone may not
   refresh the olean in `.lake/build/lib/lean/…`; run
   `lake build <ModuleName>` (the module target, e.g. `lake build KernelLearn`
   or `lake build GroundZero`) before re-running probes that import it.
5. **Full build.**  `lake build` (or `make library`) must finish with all jobs
   green.  CI runs `lake build` on push.  When building a single module, use
   its *full* module name as the target (e.g. `lake build GroundZero.HITs.Unordered`
   — `lake build Unordered` does not resolve); `lake build GroundZero` and
   `lake build KernelLearn` are safe umbrella targets.
6. **Register new files.**  New modules are picked up by
   `lake script run updateIndex` (target `make index`) **only after `git add`**
   (untracked files are skipped).  The root `GroundZero.lean` is generated by
   this script — never edit it by hand.
7. **Self-tests.**  Keep `hott example`s in the library file so regressions are
   caught at build time; `#check`-style probes live in `/tmp` and are
   disposable.
8. **Review.**  After integration, have a second agent review the diff (API
   consistency with `Coeq`, proof reuse, naming, universe levels).

## 9. Quick-reference checklist

**Before writing hott code**
- [ ] Read the reference implementation of the same pattern (`Coeq`, `Generalized`,
      `UnorderedTriple`) — the library rewards imitation.
- [ ] Check whether the machinery you need already exists (`rpow`, `sum`,
      `biForm`, `IsSymmetric`, `by symm`, …).

**When hott code fails to parse**
- [ ] `λ x : T, …` → use `=>` (G1).
- [ ] `Π t : T, …` → parenthesize `Π (t : T), …` (G2).
- [ ] `{ … }, { … }` blocks → sequential `;`-chains (G3).
- [ ] Constructor args inaccessible → `induction … using … with | ctor a b c =>` (G4).

**When hott code fails to elaborate**
- [ ] `Quotient.rec`/`Quotient.ind` behaving like core `Quotient` → you are
      outside `namespace GroundZero.HITs` (N1).
- [ ] `R.τ` unknown inside `GroundZero.HITs` → qualify it or move the demo (N2).
- [ ] `unfold`/defeq not going through → the constant is an
      `hott opaque axiom`; use the explicit β-rule (Section 2, 6).
- [ ] `symm` does nothing → the goal is not `k x y = k y x` with an instance,
      or you are relying on core `[symm]`; use `symmetry`/manual proof (Section 5).
- [ ] Path algebra goal (`p ⬝ p⁻¹ = idp`, cancellations, `(p ⬝ q)⁻¹` …)
      → try `by path_simp` first; it closes free-groupoid goals axiom-free
      (Section 5).  For 2-path goals (`ν ⬝ κ = κ ⬝ ν` on `loop = loop`, or
      `h : p = q` whiskering) `path_simp`'s higher-order rules also apply.
- [ ] `rw` fails on a hott `Id` lemma → expected: core `rw` only handles
      `Eq`; use `path_simp`, `transitivity`, or `exact`/`apply` (Section 5).
- [ ] "unsolved goals" at `end` → you reintroduced `{ … }, { … }` (G3), or the
      `with |` clauses did not cover all constructors.

**Before integrating**
- [ ] Probe → single-file compile → integration probe → `lake build` (Section 8).
- [ ] `git add` new files *before* `lake script run updateIndex`.
- [ ] Keep the public API inside the module's namespace; keep examples generic.
- [ ] Run the code review pass and fix consistency issues.

---

## 10. Case study: the Gaussian-kernel axiom block (series reduction chart)

The positive-semidefiniteness of the Gaussian kernel (`gaussPsd` in
`PosDef.lean`) is proved by reducing all analytic content to a handful of
real-analysis axioms.  The trajectory below spans twenty states, 追記評価1–20:
追記評価1 is the initial completion of `gaussPsd` (it predates the evaluation
notes, which are documented as 追記評価2–6 in the comment blocks at the end of
`PosDef.lean`).  The later rounds tried to shrink the block, and the chart
records what worked and what provably cannot.  追記評価4, the limit-theory
part of 追記評価6, and 追記評価7 are *integrated*; 追記評価5's exp
redefinition is applied (its temporary `cauchyProduct` axiom was removed in
追記評価7).  An ATP working near
`infiniteSum`/`exp` should know which axioms are load-bearing and which are now
theorems.

| Round | Move | gaussPsd real-analysis axioms | Verdict |
|---|---|---|---|
| 追記評価1 | initial completion of `gaussPsd` | `{exp, expZero, expAdd, expSeries, infSumNonneg, infSumFinSwap}` (6) | 4-axiom exp block (`Reals.lean`: `exp`, `expZero`, `expAdd`, `expSeries`) + 2 series axioms (`PosDef.lean`: `infSumNonneg`, `infSumFinSwap`); `expSeries` links `exp` to `infiniteSum`. (Label introduced in this chart — it predates the 追記評価2–6 comment blocks. The counts are the documented *block*; see the 追記評価4 row for the measured per-proof dependency.) |
| 追記評価2 | derive the 2 series axioms from `sup` (Dedekind completeness) | unchanged (6) | `infSumNonneg`: only its `sup`-version `infSumNonnegSup` is derivable — the axiom itself is not (`infiniteSum` is an uninterpreted symbol). `infSumFinSwap`: **not derivable**; `sup` commutes only with monotone operations, not signed linear forms (`supNegDuality`, `negSupNotSwapClosed`). |
| 追記評価3 | pin the counterexample | unchanged (6) | `alt = (1,−1,0,…)`: `sup { sum n alt } = 1 ≠ 0` although the partial sums stabilize at 0. The Gaussian series is exactly this for `xy < 0`, so redefining `infiniteSum` via `sup` is ruled out (`alt.supNeEventual`, `seriesNegNotSwap`). |
| 追記評価4 | add the linearity axiom `infSumLin` | `{exp, expAdd, expSeries, infSumNonneg, infSumLin}` (5) | measured `#print axioms gaussPsd`: `expZero` is in the exp *block* but `gaussPsd` has never depended on it; `infSumFinSwap` becomes a **theorem** (via `sumSwapInf`) and `infSumLin` is the new axiom. Series core `{expSeries, infSumNonneg, infSumLin}` is the standard minimal form; a convergence-hypothesis version is impossible (Gaussian series is alternating for `xy < 0`, 追記評価3's `alt`). |
| 追記評価5 | redefine `exp` as its series | `{expZero, cauchyProduct, infSumNonneg, infSumLin}` (4) | `expSeries` becomes definitional (`rfl`); `expAdd` follows from `binomTaylor` + `cauchyProduct` (probe `/tmp/probe_cauchy.lean`). Count 6→4 if `binomTaylor` is proved (the probe kept it as an axiom, i.e. 6→5), but `cauchyProduct` quantifies over arbitrary sequences — a *generalization*, not a weakening. |
| 追記評価6 | minimal Cauchy/limit theory (ε-N `conv`) — **integrated** | `{exp, expAdd, expSeries, infSumNonneg, infSumLin}` (5) for now; final `{expZero, infSumNonneg, infSumIsLim, mertens}` (4) pending 追記評価5's exp redefinition | `conv`/`convAdd`/`absMul` introduce no new axioms (they rely on the existing `Classical.choice`, like the rest of the real theory); `infSumLinD` from `{infSumIsLim}` alone; `cauchyProductLim` from `{infSumIsLim, mertens}` (`#print axioms` verified). The unconditional `infSumLin` axiom stays — `infSumIsLim` only identifies `infiniteSum` with a *given* limit, so the reduction needs the exp redefinition + absolute-convergence hypotheses. |
| 追記評価7 | conv hypotheses (absolute convergence) — **applied: axiom deleted** (`BinomTaylor.lean`) | `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin, infSumNonneg}` (6) | `cauchyProduct` axiom **deleted from the library**: `expAddD`/`gaussPsdD` now derive the Gaussian PSD via the *theorem* `cauchyProductLim` + the exp-series convergence axioms `convExpD`/`convAbsExpD` (`#print axioms` measured). The conv facts are not derivable (`infSumIsLim` is one-way, no comparison/ratio test). Target `{infSumNonneg, infSumLin}` is **not reached** — the count rises 3→6, but the blanket universal axiom `cauchyProduct` is replaced by standard analysis axioms (limit identification, Mertens, exp-series convergence). Full reduction needs those 4 as theorems (full real analysis). |
| 追記評価8 | theoremization of `convExpD`/`convAbsExpD` — **evaluated: partial progress** (`BinomTaylor.lean`) | unchanged `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin, infSumNonneg}` (6) | The comparison-test foundations are proven axiom-free (`#print axioms` = `{R, R.dedekind, Quot.sound}` only): `mulLe` (multiplication monotonicity — the previously missing base lemma), `facGePowTwo` (`2ᵏ ≤ (k+1)!`, the factorial exponential bound), `rpowLeOne` (`0 ≤ r ≤ 1 → rⁿ ≤ 1`). Target `{infSumNonneg, infSumLin}` **not reached**: the remaining chain (inverse monotonicity, geometric-series closed form + bound, comparison → `majorized`, monotone convergence via `sup.exact`, and `infSumIsLim` identification) is provable in principle — unlike 追記評価2/3 there is **no structural blocker** (no counterexample) — but it is a full real-analysis development (~300–500 lines), beyond session scope. `convExpD`/`convAbsExpD` remain evaluation axioms. |
| 追記評価9 | theoremization of `expZeroD` — **applied: exp block fully removed** (`BinomTaylor.lean`) | unchanged `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin, infSumNonneg}` (6) | `expD 0 = 1` is now a **theorem**, not an axiom: `expPartialSumOne` (every partial sum of the `expD` series at `0` is `1`; axiom-free, `#print axioms` = `{R, R.dedekind, Quot.sound}` only) + `convExt` + `infSumIsLim` identify `infiniteSum (λ n, rdiv (rpow 0 n) (fac n)) = 1`. Measured `#print axioms expZeroD` = `{GroundZero, infSumIsLim, ...}` — the 4-axiom exp block `{exp, expZero, expAdd, expSeries}` now has **zero** presence in the expD chain (`gaussPsdD` never depended on `expZero`, re-measured). The only remaining exp-side axioms are the convergence facts `convExpD`/`convAbsExpD` (追記評価8). |
| 追記評価10 | absorb the `infSumLin` axiom — **applied: `infSumLin` fully removed from `gaussPsdD`** (`PosDef.lean`: conv-hypothesis Fubini; `BinomTaylor.lean`: swap) | `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}` (5) | `infSumFinSwap` is rebuilt as the conv-hypothesis theorem `infSumFinSwapConv` — with `convAddFin`, `infSumScaleConv`, `infSumAddConv`, `infSumZeroLim` (replaces the `infSumLin`-derived `infSumZero`), `sumSwapInfConv`, `convScaleSum` — all derived from `infSumLinD` (`{infSumIsLim}` only) plus the axiom-free ε-N machinery (`convAdd`/`convScale`/`convExt`/`convConst`, `#print axioms infSumFinSwapConv` = `{infSumIsLim, ...}`, **no `infSumLin`**). `gaussPsdD` discharges the row hypotheses `hK` from the already-present `convExpD` (`convExt` + `sum.ext` + `expSummand` + `expMidD` + `convEq`), so measured `#print axioms gaussPsdD` = `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}` — the linearity axiom `infSumLin` is absorbed, count 6→5. The unconditional `infSumLin` axiom itself stays in `PosDef.lean` (the exp-world `gaussPsd` still goes through `infSumFinSwap`); the D-world swap shows the axiom is replaceable by conv hypotheses. The exp-side convergence facts `convExpD`/`convAbsExpD` remain (追記評価8's comparison-test chain still pending).  Inventory of every remaining `infSumLin` dependent (PosDef 追記評価10 補遺): the 6 internal derived lemmas (`infSumAdd`/`infSumScale`/`infSumZero`/`sumSwapInf`/`infSumScale2`/`infSumFinSwap`, all with conv-twins), `gaussPsd` (exp-world; the import-cycle blocker was removed by 追記評価11/12, see below), and its transitive users `KernelLearn.gramNonneg`/`rbfPsd`; `KernelUniversal` and the BinomTaylor chain are `infSumLin`-free (measured). |
| 追記評価11 | move the expD infrastructure into `PosDef` — **applied: cycle resolved** (Stage D′ section of `PosDef.lean`) | unchanged (5) | `expD`/`expDSeries`/`convExpD`/`convAbsExpD` moved from `BinomTaylor.lean` to `PosDef.lean`; `BinomTaylor` keeps an `open PosDef` pointer. Measured `#print axioms gaussPsdD` stays `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}` (names gain the `PosDef.` prefix; `expD`/`expDSeries` themselves are axiom-free). |
| 追記評価12 | D-world `gaussPsdD` re-proved inside `PosDef` — **applied: removal path ②** (`PosDef.lean` 追記評価12 section) | unchanged (5) | The whole binomial-theorem chain (`nCr`…`binomTaylor`, axiom-free: `#print axioms` = `{R, R.dedekind, Quot.sound}`), `expAddD` (`{convExpD, convAbsExpD, infSumIsLim, mertens}`), and the D-world Gaussian machinery (`gaussKernelD`/`expTripleD`/`gaussDecompD`/`expMidD`/`gaussKernelDSeries`/`gaussPsdD`) are moved into `PosDef.lean` (namespace `PosDef`). `PosDef.gaussPsdD` is now the clean 5-axiom D-world version, importable by anything that imports `PosDef` (e.g. `KernelLearn`) — the `PosDef↔BinomTaylor` import cycle is fully gone, unblocking the `infSumLin` deletion (path ③④: switch `KernelLearn` to `gaussPsdD`, retire the exp-world `gaussPsd` + `infSumLin` + the 6 internal derived lemmas). The Nat lemma `subSelf` was renamed `nSubSelf` to avoid clashing with the existing ℝ version. |
| 追記評価13 | exercises for the unanswered chapters (Exercises) | — | Added Chap2/3/4/5/6 exercise tasks for the chapters with gaps, following the Chap1/2/3/4/5 solved-file convention. |
| 追記評価14 | remove `infSumLin` and the exp-world `gaussPsd` — **applied: removal paths ③④ complete** | `gaussPsdDE`: `{exp, expAdd, expSeries, infSumNonneg, convExpD, convAbsExpD, infSumIsLim, mertens}` (8) | `expEqExpD` (`exp a = expD a`, from `expSeries` + `expDSeries`, axiom-free) bridges the worlds; `gaussPsdDE` transports `gaussPsdD`'s PSD to the exp-world `gaussKernel` pointwise. `KernelLearn.gramNonneg`/`rbfPsd` switched to `gaussPsdDE`. The `infSumLin` axiom, its 6 derived lemmas (`infSumAdd`/`infSumScale`/`infSumZero`/`sumSwapInf`/`infSumScale2`/`infSumFinSwap`) and the exp-world `gaussPsd` (+ `expTriple`/`gaussDecomp`/`expMid`/`gaussKernelSeries`) are **deleted from the library** (measured: `#print axioms gaussPsdDE` shows no `infSumLin`; `expSummand`/`gaussKernel` kept — `expMidD`/`KernelLearn` use them). |
| 追記評価15 | remove `expSeries` from `gaussPsdDE` via conv hypotheses — **evaluated: impossible without an equivalent axiom** | unchanged (8) | `expEqExpD` (`exp = expD`) *is* the series decomposition of `exp`; `expZero`+`expAdd` alone underdetermine `exp` (`f(a+b)=f a·f b, f 0=1` admits any `cᵃ`), and `convExpD` never mentions `exp`. The only bridge is `expSeries`. An equivalent-form axiom `convExp` (partial sums converge to `exp a`) swaps in place: `convExp + infSumIsLim → expSeries` and `expSeries + convExpD + convEq → convExp` both proved (probe `/tmp/eval15_equiv.lean`, EXIT 0) — same count (8). D-world `gaussPsdD` stays clean at 5 axioms; dropping `expSeries` entirely requires either retiring the exp-world `gaussKernel` (KernelLearn RBF bridge stays exp-dependent) or redefining `exp := expD` in `Reals.lean`. |
| 追記評価16 | switch `KernelLearn.gram` to `gaussKernelD`, retire `gaussPsdDE` — **evaluated: gram-level PSD becomes exp-free (5); RBF bridge keeps `expSeries` (8 est.; measured 7 in 追記評価17)** | gram level 8 → 5; RBF bridge unchanged (8 est.; measured 7) | probe `/tmp/eval16_probe.lean` EXIT 0 (namespace `Eval16`): `gaussSymmD` (`IsSymmetric (gaussKernelD ε)` from `sqrSym` alone), `gramDNonneg` via `gaussPsdD` directly (**exp-free**, 5 axioms), `gramDSym` via `biFormSymI`. So `gaussPsdDE` (8 axioms incl. `exp`/`expSeries`/`infiniteSum`) becomes unnecessary for the gram chain and can be retired. **But** `gaussKernelEqD`/`rbfGaussEqD` (`RBF.gaussianRbf ε Rₘ c x = gaussKernelD ε c x` = `rbfGaussEq ⬝ gaussKernelEqD ⬝ gaussSymmD`) need `expEqExpD` → `expSeries`, so the RBF-named `gramRbfNonnegD`/`rbfPsd` stay at 8 axioms (estimated; measured 7 in 追記評価17 — `expAdd` not needed). Residual exp scope = only where `RBF.gaussianRbf` is compared to `gaussKernelD`; redefining the RBF in D-world terms would make the whole chain exp-free at the cost of duplicating the `RBF.lean` definition. **→ applied as 追記評価17**: `gramNonneg`/`gramSym` switched to `gaussKernelD` (gram-level PSD measured at 5 axioms via `gaussPsdD`, exp-free), `gaussSymmD` registered as a library instance, `gaussPsdDE` deleted from `PosDef.lean`. The `representer` paths remain exp-world (scope (C)). **→ 追記評価18 applied (C)**: RBF-named PSD now exp-free too. |
| 追記評価18 | apply 追記評価16 (C): redefine the RBF in D-world terms (`RBFD`) — **applied** | `gramRbfNonneg`/`rbfPsd`: 7 → **5** (exp-free, `gaussPsdD` direct); bridge/sym exp-free (infra only) | `RBF.lean`: `RBF.gaussKernelD` (radial, `expD`) + `RBF.gaussianRbfD` added (`import PosDef`, exp-world `gaussianRbf` duplicated). `KernelLearn`: `gaussianRbfD_eq_gaussKernelD` (absSqr+sqrSym, exp- and conv-free), `rbfGaussSymmD` instance; `gramRbf`/`gramRbfNonneg`/`rbfPsd`/`gramRbfSym` switched to `gaussianRbfD`; exp bridge `gaussKernelEqD`/`rbfGaussEqD` and exp instance `rbfGaussSymm` deleted (recorded); `PosDef.expEqExpD` kept as the exp↔D connection lemma (no remaining users). `#print axioms gramRbfNonneg` = `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}` (5, no `exp`/`expAdd`/`expSeries`); `rbfPsd` same; `gaussianRbfD_eq_gaussKernelD` exp-free. Residual exp = `RBF.lean`'s own exp-RBF theory + representer sections. Cost: exp/D RBF duplication. |
| 追記評価17 | apply 追記評価16 (A): switch `KernelLearn.gram` to `gaussKernelD`, delete `gaussPsdDE` — **applied** | `gramNonneg`: 8 → 5 (exp-free, `gaussPsdD` direct); RBF-named `gramRbfNonneg`/`rbfPsd`: 7 (5 + `exp` + `expSeries`, via bridge; `expAdd` not needed) → 5 in 追記評価18 (RBFD) | `KernelLearn`: `gaussSymmD` (`IsSymmetric (gaussKernelD ε)`, exp-free, registered instance), `gaussKernelEqD`, `rbfGaussEqD` (`RBF.gaussianRbf ε Rₘ c x = gaussKernelD ε c x`); `gram`/`gramNonneg`/`gramSym`/`gramRow`/`gramRowLin` switched to `gaussKernelD`; `gramRbfNonneg` rewritten via `rbfGaussEqD` bridge; `PosDef.gaussPsdDE` deleted (`expEqExpD` kept for the bridge); headers/eval comments updated. `#print axioms gramNonneg` = `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}` (5, no `exp`/`expAdd`/`expSeries`); `gramSym` exp-free. `representer`/dual-loss sections stay exp-world (scope (C)). |
| 追記評価19 | D-ify the representer system + `kernelCenter`; move orphaned exp-world kernel theory to `RBF.lean` — **applied** | representer system + `kernelCenter`: exp-free (`kernelCenter` via `BinomTaylor.expZeroD` — `infSumIsLim` only, no exp axiom); gram chain unchanged (5/0) | `KernelLearn`: `import BinomTaylor`; §4 (`representer`/`featureMap`/`representerAsFeatures`/`gaussEqShift`/`representerShiftInvariant`) switched to `gaussKernelD` (probe `/tmp/eval19_probe.lean` EXIT 0); `kernelCenter` rewritten via `expZeroD`; new `gaussianRbfDShiftInvariant`. Orphaned exp-world decls (`rbfGaussEq`, `gaussSymm`, `kernelSym`, `expPos`, `kernelPos`, `expMonotone`, `kernelLeOne` + bridge lemmas `absSqr`/`negSub`/`sqrSym`) moved to `RBF.lean` (exp theory's home; `KernelLearn` now uses `RBF.absSqr`/`RBF.sqrSym`). `#print axioms` measured: representer system exp-free (infra only); `gramNonneg`/`rbfPsd` unchanged (5). Residual exp scope = `RBF.lean` exp theory only. |
| 追記評価20 | switch `KernelUniversal` (universal kernel) to the D world (`gaussianRbfD`/`expD`) — **evaluated** | bump chain: `{exp, expAdd, expZero}` (3 axioms) → D world: `{convExpD, convAbsExpD, infSumIsLim, mertens}` (4 — a subset of the 5-axiom gram/RBF/representer foundation since 追記評価17-19; `infSumNonneg` not needed); `bumpSymmD` exp-free (infra only), `bumpCenterD` `infSumIsLim` only, `gaussianUniversalD` `stoneWeierstrassGaussD` only | probe `/tmp/eval20_probe.lean` EXIT 0 (namespace `Eval20`): mechanical translation `exp`→`PosDef.expD`, `expAdd`→`PosDef.expAddD`, `expZero`→`BinomTaylor.expZeroD`; new `expNonnegD` derived via `expAddD`+`halve`+`sqrNonneg` (same shape as `PosDef.expNonneg`); ring toolkit (`subSelf`/`midSquare`/`prodReorder`/`half`/`paral`) shared (exp-free). 12 bump-system declarations D-duplicated + `expNonnegD`. `#print axioms`: `bumpProductD`/`bumpSumMulClosedD` = 4 conv-family axioms (= `expAddD` deps: `{convExpD, convAbsExpD, infSumIsLim, mertens}`, no `infSumNonneg`); `gaussianUniversalD` = `stoneWeierstrassGaussD` + infra (exp-free). Residual axiom = `stoneWeierstrassGaussD` (the real-analysis residual, same as exp version). Exp versions become orphaned → RBF.lean consolidation or deletion is the follow-up. |

Takeaways for ATPs:

* **The swap rule is not a primitive.**  `infSumFinSwap` was first shown to be
  linearity in disguise (追記評価4: `infSumLin`), then derived outright from the
  ε-N limit theory (追記評価6: `infSumLinD`), and finally **deleted together with
  `infSumLin`** in 追記評価14 — the conv-hypothesis twins
  (`infSumFinSwapConv`/`sumSwapInfConv`) are the current standard.  State series
  lemmas in terms of `infSumIsLim` + conv hypotheses rather than adding swap or
  linearity axioms.
* **`sup`/`inf` cannot replace `infiniteSum` here.**  Order completeness
  commutes with monotone operations only; the alternating partial sums of the
  Gaussian series are a concrete obstruction (追記評価2–3).  Reuse
  `infSumNonneg` (and, before 追記評価14 removed it, `infSumLin`) instead.
* **Counts are not strength.**  追記評価5 lowered the count by generalizing
  (`cauchyProduct`, removed in 追記評価7 once the exp-series convergence axioms
  arrived); the honest metric is the analytic content captured.  The
  projected irreducible core is
  `{infSumNonneg, infSumIsLim, mertens}` plus the exp-series convergence facts
  `convExpD`/`convAbsExpD` — positivity, the limit axiom, Mertens
  (Cauchy-product limit) for the `expAdd` connection, and convergence for the
  series-to-`expD` identification.  追記評価9 theoremized `expZeroD`: no
  `expZero` axiom remains anywhere in the expD chain; 追記評価10 absorbed the
  linearity axiom `infSumLin` (conv-hypothesis Fubini) so measured `gaussPsdD`
  needs only `{convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}`.
  追記評価14 removed `infSumLin` itself: the exp-world `gaussPsd` is gone (its
  role was briefly taken by `gaussPsdDE`, which 追記評価17 in turn removed — the
  gram chain now runs directly on `gaussPsdD`, exp-free), so `infSumLin` no
  longer exists anywhere in the library.
  追記評価8 shows the
  remaining exp-side cost precisely: replacing `convExpD`/`convAbsExpD` with
  theorems needs the full comparison-test chain (inverse monotonicity,
  geometric-series bound, monotone convergence via `sup`), a full real-analysis
  development beyond session scope.

*Full details:* the 追記評価2–6 comment blocks and the 追記評価12 section in
`PosDef.lean` (D-world `gaussPsdD`, now with the binomial-theorem chain); the
追記評価7–10 evaluation records at the end of `BinomTaylor.lean` (conv-hypothesis
reduction, theoremization attempts); probes `/tmp/probe_cauchy.lean`
(exp redefinition) and `/tmp/probe_lim.lean` (ε-N limit theory).

## 11. Certified SMT-arithmetic export (oleansmt → Ground Zero)

[`oleansmt`](https://github.com/mookichi/smt-lean4-rs) is a certified
SMT-solver front-end.  Its arithmetic core proves the linear-arithmetic
contradictions of an SMT run in a small *nanoda* kernel, then re-exports those
proofs as ordinary Lean terms on top of Ground Zero's natural numbers.  The
key point for an ATP: Ground Zero's `≤` is **max-based** — `LE.le n m :=
max n m = m` — while nanoda's `le` is a *recursive* order (`le (succ n)
(succ m) ≡ le n m`, with `lt a b := le (succ a) b`).  The two agree
extensionally on `ℕ`, but the recursive `le` is not definitionally equal to
the max-based `≤`, so the export **re-derives** each nanoda inference from
preloaded Tier 1/2 theorems instead of transcribing it verbatim.

The wrap table below is the complete bridge.  Every row was verified by
compiling the generated file against this repository (`lake env lean`) — the
Lean kernel accepts all four contradiction shapes (strict cycle, mixed cycle,
single false literal, constant gap).

| nanoda rule (recursive `le`/`lt`) | Ground Zero reconstruction |
|---|---|
| `le_trans : a ≤ b → b ≤ c → a ≤ c` | `le.trans` |
| `lt_le_contra : a < b → b ≤ a → ⊥` | `le.neSucc a (le.trans h₁ h₂)` |
| `lt_lt_contra : a < b → b < a → ⊥` | `le.neSucc a (le.trans (le.trans h₁ (le.leSucc b)) h₂)` |
| `not_succ_le_zero : succ a ≤ 0 → ⊥` | `le.neSucc a (le.trans p (max.zeroLeft a))` |
| `le_inj : a+1 ≤ b+1 → a ≤ b` | `le.inj` = `ap Nat.pred` |
| constant gap `le c d` (`c > d`) | `le.neSucc d (le.trans (chain) h)` via a specialized `ArithGapContra` |

Notes for a prover reusing this strategy:

* `le_inj` is *reserved* in the nanoda kernel (a no-op there, since the
  recursive `le` strips a leading `succ` pair definitionally) but is emitted
  as `le.inj` in the Ground Zero target.
* For a constant gap `c > d`, `le c d` is **not** literally `𝟎` under the
  max-based encoding.  The exporter emits a specialized `ArithGapContra :
h : c ≤ d → 𝟎` whose body is `le.neSucc d (le.trans (up) h)`, where `up :
d+1 ≤ c` is built by a `le.trans`/`le.leSucc` chain from `max.refl (d+1)`.
* `rfl`/`idp` do **not** reduce a max-based `≤` (Lean's `max` is `if`-based,
  and `max n m = m` needs the case split), so every inequality in these proofs
  is a real `le.trans` chain, never a bare reflexivity.

---

*Last updated:* 2026-08-19 (§11 added: certified SMT-arithmetic export bridge
`oleansmt → Ground Zero`, with the nanoda→Ground Zero wrap table and the
max-based `≤` notes; Tier 2 gained `le.inj`.)  Previous updates:
2026-08-13 (`path_simp` extended with higher-order rules:
`ap`-naturality `apComp`, Eckmann–Hilton fragments
`loop₁`/`compUniq`/`loop₂`/`comm` on 2-paths, and whiskering rules
`rwhs`/`lwhs` derived from context 2-path hypotheses; S¹ demonstrations in
`GroundZero/HITs/Circle.lean`; Section 5 updated.  Regression suite in
`GroundZero/Types/Id.lean` extended with `apComp`/`ap2Comp`.)  Previous
updates: 2026-08-12 (`path_simp` integrated; Section 5 corrected: core `rw`
cannot rewrite hott `Id`; series axiom reduction chart 追記評価1–20; 追記評価14
and 17–19 applied).  When this session or a future one adds a lesson, append a
dated bullet here and update the relevant section and the checklist.
