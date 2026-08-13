import GroundZero.Meta.Tactic
import GroundZero.Types.Id

open Lean
open GroundZero.Types

universe u v

/-
  Function-level symmetry, as a first-class citizen.

  The relation-level classes (`Symmetric`, `Reflexive`, `Transitive`) in
  `Meta/Tactic.lean` treat symmetry of a *relation* `ρ : A → A → Sort v`.
  This file lifts the same idea to *functions* `k : A → A → B`:

    IsSymmetric k  ⇔  Π (x y : A), k x y = k y x

  Since `=` is the hott identity type `Id`, the field is literally a *path*
  — homotopy-theoretic symmetry, not a propositional one.

  Design notes
  * The class lives here (not in `Meta/Tactic.lean`) because its field must
    mention the hott equality `Id`, which lives in `Types/Id.lean`; importing
    `Types/Id.lean` from `Meta/Tactic.lean` would create an import cycle
    (`Id → Proto → Meta.Basic → Tactic`).
  * The `symm` tactic mirrors `applyOnBinRel` (the machinery behind the
    relation-level `symmetry` tactic) but at the function level: it decomposes
    a goal `k x y = k y x`, synthesises the `IsSymmetric k` instance and closes
    the goal with `inst.symm x y`.
  * Scope: the tactic handles *binary* functions. Symmetries of finite sums
    (`Σᵢⱼ (αᵢ·βⱼ)·K(xᵢ,xⱼ) = Σᵢⱼ (βᵢ·αⱼ)·K(xᵢ,xⱼ)`) are derived theorems built
    on top of `inst.symm`, e.g. `PosDef.biFormSymI`.

  This file also provides ternary symmetry `IsSymmInvariant`: a symmetric
  function of three arguments is invariant under all 6 permutations of Σ₃, but
  the class asks only for the two transposition generators σ₁ = (12), σ₂ = (23).
  The remaining permutations are derived (function composition is strict, so the
  braid coherence is automatic at the function level).
-/
class IsSymmetric {A : Type u} {B : Type v} (k : A → A → B) : Type (max u v) where
  symm : Π (x y : A), k x y = k y x

/-
  Ternary symmetry (Σ₃): invariance under the transposition generators.

  A fully symmetric ternary function f : A → A → A → B is invariant under all
  6 permutations of its arguments. The class requires only the two adjacent
  transpositions σ₁ = (12) and σ₂ = (23); for *functions* the braid coherence
  σ₁σ₂σ₁ = σ₂σ₁σ₂ is automatic (function composition is strict), so the
  remaining four permutations are derived in the `IsSymmInvariant` namespace
  below. (The braid 2-cell is data only for the *quotient* V³ // Σ₃, not for
  functions.)

  Generalisation to Σₙ: require invariance under the n−1 adjacent transpositions
  (i i+1); the resp conditions of the quotient `Vⁿ // Σₙ` are exactly such
  instances.
-/
class IsSymmInvariant {A : Type u} {B : Type v} (f : A → A → A → B) : Type (max u v) where
  swap12 : Π (x y z : A), f x y z = f y x z
  swap23 : Π (x y z : A), f x y z = f x z y

namespace IsSymmInvariant
  variable {A : Type u} {B : Type v} {f : A → A → A → B}

  -- Note: the derived lemmas use only the class projection and `Id.trans`, so
  -- they carry no implicit `[GroundZero]` binder — more general than typical
  -- hott lemmas (whose bodies use axioms).

  /-- (123) = σ₂∘σ₁: f x y z = f y z x -/
  hott lemma cycle123 [inst : IsSymmInvariant f] (x y z : A) : f x y z = f y z x :=
  inst.swap12 x y z ⬝ inst.swap23 y x z

  /-- (132) = σ₁∘σ₂: f x y z = f z x y -/
  hott lemma cycle132 [inst : IsSymmInvariant f] (x y z : A) : f x y z = f z x y :=
  inst.swap23 x y z ⬝ inst.swap12 x z y

  /-- σ₁σ₂σ₁ = σ₂σ₁σ₂: f x y z = f z y x（完全反転） -/
  hott lemma reverse [inst : IsSymmInvariant f] (x y z : A) : f x y z = f z y x :=
  inst.swap12 x y z ⬝ inst.swap23 y x z ⬝ inst.swap12 y z x
end IsSymmInvariant

namespace GroundZero.Meta.Tactic

/-- Close goals of the form `k x y = k y x` by typeclass search for `IsSymmetric k`.

  Note: this deliberately shadows the core `symm` tactic (the `[symm]`
  attribute machinery), which is inert on hott `Id`-equalities anyway. The
  library already avoids core tactic names (`reflexivity`, `symmetry`, ...);
  `symm` is used here for the *function-level* symmetry so that the relation-
  level name `symmetry` stays untouched. Goals that are not of the form
  `k x y = k y x` fail with an explicit error instead of silently misbehaving. -/
elab "symm" : tactic => do
  Elab.Tactic.liftMetaTactic (fun mvar => do
    let ty ← instantiateMVars (← mvar.getType)
    let ty ← Meta.whnf ty.consumeMData
    -- Structural check only (same `withApp` style as `applyOnBinRel`):
    -- the goal must be an equation, and its RHS must be definitionally equal to
    -- the LHS with the last two arguments swapped.
    ty.withApp λ e es => do
      unless es.size == 3 do
        throwError "goal is not an equation (k x y = k y x)"
      let lhs := es[1]!
      let rhs := es[2]!
      let fn := lhs.getAppFn
      let lhsArgs := lhs.getAppArgs
      let n := lhsArgs.size
      if n == 0 || n == 1 then
        throwError "goal is not of the form k x y = k y x"
      else
        pure ()
      let x := lhsArgs[n - 2]!
      let y := lhsArgs[n - 1]!
      -- Partial application with the first `n - 2` arguments kept
      -- (implicit instance arguments included).
      let kPartial := mkAppN fn (lhsArgs.take (n - 2))
      let cand := mkAppN kPartial #[y, x]
      if (← Meta.isDefEq rhs cand) then
        let inst ← Meta.synthInstance (← Meta.mkAppM ``IsSymmetric #[kPartial])
        -- Apply the projection with all parameters explicit (A given, B inferred).
        let A ← Meta.inferType x
        let prf ← Meta.mkAppOptM ``IsSymmetric.symm
          #[some A, none, some kPartial, some inst, some x, some y]
        discard (mvar.assign prf)
        pure []
      else
        throwError "right-hand side is not the left-hand side with arguments swapped")

end GroundZero.Meta.Tactic

/- Self-tests: the tactic closes the class field itself; the ternary class
   derives the full reversal from the two generators. -/
section
  variable {A : Type u} {B : Type v}

  example {k : A → A → B} [inst : IsSymmetric k] (x y : A) : k x y = k y x := by
    symm

  hott example {f : A → A → A → B} [inst : IsSymmInvariant f] (x y z : A) : f x y z = f z y x :=
    IsSymmInvariant.reverse x y z
end
