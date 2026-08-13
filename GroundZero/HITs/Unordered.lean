import GroundZero.Meta.Symm
import GroundZero.HITs.Quotient

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Types

/-
  Unordered triples: the third symmetric power V³ // Σ₃.

  The set of *unordered* triples of a type V is the quotient V³ // Σ₃ of the
  cartesian power by the symmetric group.  Instead of quotienting by all six
  permutations, we quotient by the two adjacent transposition *generators*
  σ₁ = (12), σ₂ = (23); the remaining permutations are then derivable in the
  quotient from the two generator paths (see `IsSymmInvariant` in
  `GroundZero/Meta/Symm.lean`).

  The point of this construction is to show that the typeclass

      IsSymmInvariant f   ⇔   Π x y z, f x y z = f y x z  ∧  f x y z = f x z y

  is exactly the *resp condition* of the quotient `UnorderedTriple V`:
  a function f : V → V → V → B lifts to a function `UnorderedTriple.prod3UP f`
  on the quotient (i.e. is well-defined on unordered triples) precisely when it
  is invariant under the two generators.  `prod3UP` is defined through the
  non-dependent eliminator `UnorderedTriple.rec` with the typeclass witnesses
  `inst.swap12`/`inst.swap23` as the resp condition; `prod3UPRespects12` and
  `prod3UPRespects23` say that the lift agrees with the witnesses along the
  generator paths (the rec β-rules, instantiated from `recβrule12`/`recβrule23`).

  Generalisation to Σₙ: quotient `Vⁿ` by the n−1 adjacent transpositions
  (i i+1); `IsSymmInvariant` generalises to invariance under those n−1
  generators.
-/

namespace GroundZero.HITs
universe u v

/-- Σ₃ の resp 関係: 隣接 transposition 生成子 σ₁=(12), σ₂=(23) -/
inductive UnorderedTriple.rel (V : Type u) : V × V × V → V × V × V → Type u where
  | swap12 (x y z : V) : rel V (x, y, z) (y, x, z)
  | swap23 (x y z : V) : rel V (x, y, z) (x, z, y)

/-- V の順序なし3つ組（3次対称冪）: V³ // Σ₃ -/
hott definition UnorderedTriple (V : Type u) := Quotient (UnorderedTriple.rel V)

namespace UnorderedTriple
  hott definition elem {V : Type u} : V × V × V → UnorderedTriple V := Quotient.elem

  hott definition resp12 {V : Type u} (x y z : V) :
    UnorderedTriple.elem (x, y, z) = UnorderedTriple.elem (y, x, z) :=
  begin
    dsimp [UnorderedTriple.elem];
    exact Quotient.line (UnorderedTriple.rel.swap12 x y z)
  end

  hott definition resp23 {V : Type u} (x y z : V) :
    UnorderedTriple.elem (x, y, z) = UnorderedTriple.elem (x, z, y) :=
  begin
    dsimp [UnorderedTriple.elem];
    exact Quotient.line (UnorderedTriple.rel.swap23 x y z)
  end

  /-- 依存消去子（Coeq.ind と同型）: resp 条件は IsSymmInvariant をバラした形 -/
  hott definition ind {V : Type u} {C : UnorderedTriple V → Type v}
      (elemπ : Π (t : V × V × V), C (elem t))
      (swap12π : Π (x y z : V), elemπ (x, y, z) =[resp12 x y z] elemπ (y, x, z))
      (swap23π : Π (x y z : V), elemπ (x, y, z) =[resp23 x y z] elemπ (x, z, y)) : Π q, C q :=
  begin
    fapply Quotient.ind;
    intro t; exact elemπ t;
    intros u v H;
    induction H using UnorderedTriple.rel.casesOn with
    | swap12 x y z => exact swap12π x y z
    | swap23 x y z => exact swap23π x y z
  end

  attribute [induction_eliminator] ind

  /-- ind の β 規則（σ₁ = (12) 方向） -/
  hott definition indβrule12 {V : Type u} {C : UnorderedTriple V → Type v}
      (elemπ : Π (t : V × V × V), C (elem t))
      (swap12π : Π (x y z : V), elemπ (x, y, z) =[resp12 x y z] elemπ (y, x, z))
      (swap23π : Π (x y z : V), elemπ (x, y, z) =[resp23 x y z] elemπ (x, z, y))
      (x y z : V) : apd (ind elemπ swap12π swap23π) (resp12 x y z) = swap12π x y z :=
  begin
    dsimp [ind, resp12];
    exact @Quotient.indβrule (V × V × V) (UnorderedTriple.rel V) _ _ _ _ _
      (UnorderedTriple.rel.swap12 x y z)
  end

  /-- ind の β 規則（σ₂ = (23) 方向） -/
  hott definition indβrule23 {V : Type u} {C : UnorderedTriple V → Type v}
      (elemπ : Π (t : V × V × V), C (elem t))
      (swap12π : Π (x y z : V), elemπ (x, y, z) =[resp12 x y z] elemπ (y, x, z))
      (swap23π : Π (x y z : V), elemπ (x, y, z) =[resp23 x y z] elemπ (x, z, y))
      (x y z : V) : apd (ind elemπ swap12π swap23π) (resp23 x y z) = swap23π x y z :=
  begin
    dsimp [ind, resp23];
    exact @Quotient.indβrule (V × V × V) (UnorderedTriple.rel V) _ _ _ _ _
      (UnorderedTriple.rel.swap23 x y z)
  end

  /-- 非依存消去子 -/
  hott definition rec {V : Type u} {B : Type v} (f : V × V × V → B)
      (ρ12 : Π (x y z : V), f (x, y, z) = f (y, x, z))
      (ρ23 : Π (x y z : V), f (x, y, z) = f (x, z, y)) : UnorderedTriple V → B :=
  begin
    fapply ind;
    intro t; exact f t;
    intros x y z; exact pathoverOfEq (resp12 x y z) (ρ12 x y z);
    intros x y z; exact pathoverOfEq (resp23 x y z) (ρ23 x y z)
  end

  /-- rec の β 規則（σ₁ = (12) 方向） -/
  hott definition recβrule12 {V : Type u} {B : Type v} (f : V × V × V → B)
      (ρ12 : Π (x y z : V), f (x, y, z) = f (y, x, z))
      (ρ23 : Π (x y z : V), f (x, y, z) = f (x, z, y)) (x y z : V) :
    ap (rec f ρ12 ρ23) (resp12 x y z) = ρ12 x y z :=
  begin
    dsimp [rec];
    apply pathoverOfEqInj (resp12 x y z);
    transitivity; symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule12; reflexivity
  end

  /-- rec の β 規則（σ₂ = (23) 方向） -/
  hott definition recβrule23 {V : Type u} {B : Type v} (f : V × V × V → B)
      (ρ12 : Π (x y z : V), f (x, y, z) = f (y, x, z))
      (ρ23 : Π (x y z : V), f (x, y, z) = f (x, z, y)) (x y z : V) :
    ap (rec f ρ12 ρ23) (resp23 x y z) = ρ23 x y z :=
  begin
    dsimp [rec];
    apply pathoverOfEqInj (resp23 x y z);
    transitivity; symmetry; apply apdOverConstantFamily;
    transitivity; apply indβrule23; reflexivity
  end

  /-- Σ₃ 対称関数 f の商 UnorderedTriple V への持ち上げ
      （IsSymmInvariant の witness がそのまま rec の resp 条件になる） -/
  hott definition prod3UP {V : Type u} {B : Type v} (f : V → V → V → B)
      [inst : IsSymmInvariant f] : UnorderedTriple V → B :=
  rec (λ t : V × V × V => f t.1 t.2.1 t.2.2) inst.swap12 inst.swap23

  hott corollary prod3UPRespects12 {V : Type u} {B : Type v} (f : V → V → V → B)
      [inst : IsSymmInvariant f] (x y z : V) :
    ap (prod3UP f) (resp12 x y z) = inst.swap12 x y z :=
  recβrule12 (λ t : V × V × V => f t.1 t.2.1 t.2.2) inst.swap12 inst.swap23 x y z

  hott corollary prod3UPRespects23 {V : Type u} {B : Type v} (f : V → V → V → B)
      [inst : IsSymmInvariant f] (x y z : V) :
    ap (prod3UP f) (resp23 x y z) = inst.swap23 x y z :=
  recβrule23 (λ t : V × V × V => f t.1 t.2.1 t.2.2) inst.swap12 inst.swap23 x y z

  /- Self-tests: 持ち上げが生成子を尊重する -/
  section
    variable {V : Type u} {B : Type v} (f : V → V → V → B) [inst : IsSymmInvariant f]

    hott example (x y z : V) : ap (prod3UP f) (resp12 x y z) = inst.swap12 x y z :=
      prod3UPRespects12 f x y z

    hott example (x y z : V) : ap (prod3UP f) (resp23 x y z) = inst.swap23 x y z :=
      prod3UPRespects23 f x y z

    /-- rec の利用例 -/
    hott example (g : V × V × V → B) (ρ12 : Π (x y z : V), g (x, y, z) = g (y, x, z))
        (ρ23 : Π (x y z : V), g (x, y, z) = g (x, z, y)) : UnorderedTriple V → B :=
      rec g ρ12 ρ23

    /-- 派生置換 (123) も商の経路として導出できる: elem(x,y,z) = elem(y,z,x) -/
    hott example (x y z : V) :
      UnorderedTriple.elem (x, y, z) = UnorderedTriple.elem (y, z, x) :=
    resp12 x y z ⬝ resp23 y x z
  end
end UnorderedTriple

end GroundZero.HITs
