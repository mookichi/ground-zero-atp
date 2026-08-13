import GroundZero.Algebra.Orgraph
import GroundZero.Theorems.Nat

open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.Proto
open GroundZero.Types
open GroundZero.HITs

namespace GroundZero.Algebra
  universe u

  axiom R : Overring.{0, 0}
  @[instance] axiom R.dedekind : dedekind R

  notation "ℝ" => Alg.carrier R

  hott instance R.orfield : orfield R := R.dedekind.{0}.toorfield
  hott instance R.hasInv : ring.hasInv R.τ := R.dedekind.{0}.tohasInv

  /-- Negation distributes over addition in the additive group: -(a + b) = -a + -b. -/
  hott definition negAdd (a b : ℝ) : -(a + b) = -a + -b :=
  @Group.invExplode R.τ⁺ a b ⬝ R.τ.addComm (-b) (-a)

  /-- Exponential function exp : ℝ → ℝ (added as an axiom; a power-series construction is not yet available). -/
  hott axiom exp : ℝ → ℝ

  /-- Normalization law: exp 0 = 1. -/
  hott axiom expZero : exp 0 = 1

  /-- Additivity law: exp (a + b) = exp a * exp b. -/
  hott axiom expAdd (a b : ℝ) : exp (a + b) = exp a * exp b

  hott def metric {α : Type u} (ρ : α → α → ℝ) :=
    (Π x y, ρ x y = 0 ↔ x = y)
  × (Π x y, ρ x y = ρ y x)
  × (Π x y z, R.ρ (ρ x z) (ρ x y + ρ y z))

  def Metric := Σ (α : 0-Type) (ρ : α.1 → α.1 → ℝ), metric ρ

  section
    variable (M : Metric)

    hott def Metric.carrier := M.1.1
    hott def Metric.hset : hset M.carrier :=
    zeroEqvSet.forward M.1.2

    hott def Metric.ρ : M.carrier → M.carrier → ℝ := M.2.1

    hott def Metric.refl (x : M.carrier) : M.ρ x x = 0 :=
    (M.2.2.1 x x).2 (idp x)

    hott def Metric.eqv (x y : M.carrier) : M.ρ x y = 0 → x = y :=
    (M.2.2.1 x y).1

    hott def Metric.symm (x y : M.carrier) : M.ρ x y = M.ρ y x :=
    M.2.2.2.1 x y

    hott def Metric.triangle (x y z : M.carrier) : R.ρ (M.ρ x z) (M.ρ x y + M.ρ y z) :=
    M.2.2.2.2 x y z
  end

  hott def Metric.pointed := Σ (M : Metric), M.carrier
  notation "Metric⁎" => Metric.pointed

  hott def N.incl : ℕ → ℝ :=
  @Nat.rec (λ _, ℝ) 0 (λ _ x, x + 1)

  hott def N.incl.add (n : ℕ) : Π m, N.incl (n + m) = N.incl n + N.incl m
  | Nat.zero   => Id.inv (R.τ⁺.mulOne _)
  | Nat.succ m => @ap ℝ ℝ _ _ (λ r, r + 1) (N.incl.add n m) ⬝ R.τ⁺.mulAssoc _ _ _

  hott def leAddOne (x : ℝ) : R.ρ x (x + 1) :=
  begin
    apply Equiv.transport (R.ρ · (x + 1)); apply R.τ⁺.mulOne;
    apply leOverAddLeft; apply oneGtZero
  end

  hott def zeroLeOne : R.ρ 0 1 :=
  begin apply Equiv.transport (R.ρ 0); apply R.τ⁺.oneMul; apply leAddOne end

  hott def N.incl.lt : Π (n m : ℕ), (n ≤ m : Type) → R.ρ (N.incl n) (N.incl m)
  | Nat.zero,   Nat.zero   => λ _, @reflexive.refl R.κ _ (N.incl 0)
  | Nat.zero,   Nat.succ m => λ _, @transitive.trans R.κ _ (N.incl 0) (N.incl m) (N.incl (m + 1)) (N.incl.lt 0 m (Nat.max.zeroLeft m)) (leAddOne (N.incl m))
  | Nat.succ n, Nat.zero   => λ p, explode (Nat.max.neZero p)
  | Nat.succ n, Nat.succ m => λ p, orfield.leOverAdd (N.incl n) (N.incl m) 1 (N.incl.lt n m (ap Nat.pred p))

  /-- Power tⁿ for n : ℕ: t⁰ = 1, tⁿ⁺¹ = tⁿ · t. -/
  hott def rpow (t : ℝ) (n : ℕ) : ℝ :=
  @Nat.rec (λ _, ℝ) 1 (λ _ r, r * t) n

  /-- Factorial n! as a real number: 0! = 1, (n+1)! = n! · (n+1). -/
  hott def fac (n : ℕ) : ℝ :=
  @Nat.rec (λ _, ℝ) 1 (λ m r, r * N.incl (Nat.succ m)) n

  /--
    Formal infinite sum of a sequence (axiom; a full theory of series and
    limits is not yet available, so we axiomatize the symbol itself).
  -/
  hott axiom infiniteSum : (ℕ → ℝ) → ℝ

  /-- The infinite sum respects pointwise equality of sequences. -/
  hott axiom infiniteSum.ext (f g : ℕ → ℝ) : (Π n, f n = g n) → infiniteSum f = infiniteSum g

  /-- Division of real numbers: a / b = a · b⁻¹. -/
  hott def rdiv (a b : ℝ) : ℝ :=
  R.τ.ψ a (@ring.hasInv.inv R.τ _ b)

  /--
    Taylor series expansion of exp: exp t = Σₙ tⁿ/n! (axiom).
    Together with expZero and expAdd this pins down exp as the exponential.
  -/
  hott axiom expSeries (t : ℝ) : exp t = infiniteSum (λ n, rdiv (rpow t n) (fac n))

  hott def R.complete (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) :
    Σ M, exact (@Majorant R.κ φ) M :=
  ((Equiv.propEquiv (@supremumUniqueness R.κ _ φ)).left
    (@complete.sup R.κ R.dedekind.tocomplete φ H G))

  hott def R.cocomplete (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) :
    Σ m, coexact (@Minorant R.κ φ) m :=
  ((Equiv.propEquiv (@infimumUniqueness R.κ _ φ)).left
    (@cocomplete.inf R.κ (orfieldCocompleteIfComplete R.dedekind.tocomplete) φ H G))

  hott def sup (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) : ℝ :=
  (R.complete φ H G).1

  hott def sup.lawful (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) :
    Π x, x ∈ φ → R.ρ x (sup φ H G) :=
  (R.complete φ H G).2.1

  hott def sup.exact (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ)
    (x : ℝ) (p : Π y, y ∈ φ → R.ρ y x) : R.ρ (sup φ H G) x :=
  begin apply (R.complete φ H G).2.2; apply p end

  hott def inf (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) : ℝ :=
  (R.cocomplete φ H G).1

  hott def inf.lawful (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ) :
    Π x, x ∈ φ → R.ρ (inf φ H G) x :=
  (R.cocomplete φ H G).2.1

  hott def inf.exact (φ : R.subset) (H : φ.inh) (G : @minorized R.κ φ)
    (x : ℝ) (p : Π y, y ∈ φ → R.ρ x y) : R.ρ x (inf φ H G) :=
  begin apply (R.cocomplete φ H G).2.2; apply p end

  hott def sup.eqv {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (p : φ = ψ) : sup φ H₁ G₁ = sup ψ H₂ G₂ :=
  begin induction p; apply Equiv.bimap <;> apply Merely.uniq end

  hott def sup.le {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (y : ℝ) (p : y ∈ ψ)
    (r : Π x, x ∈ φ → R.ρ x y) : R.ρ (sup φ H₁ G₁) (sup ψ H₂ G₂) :=
  begin
    apply sup.exact; intros x q; apply @transitive.trans R.κ _;
    apply r; exact q; apply sup.lawful; exact p
  end

  hott def sup.sep {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (r : Π x y, x ∈ φ → y ∈ ψ → R.ρ x y) :
      R.ρ (sup φ H₁ G₁) (sup ψ H₂ G₂) :=
  begin
    apply Merely.rec _ _ H₂; apply R.κ.prop; intro ⟨y, p⟩;
    apply sup.le; apply p; intros x q; apply r <;> assumption
  end

  hott def sup.ssubset {φ ψ : R.subset} {H₁ : φ.inh} {H₂ : ψ.inh}
    {G₁ : @majorized R.κ φ} {G₂ : @majorized R.κ ψ} (r : φ ⊆ ψ) : R.ρ (sup φ H₁ G₁) (sup ψ H₂ G₂) :=
  begin apply sup.exact; intros y p; apply sup.lawful; apply r; assumption end

  hott def R.closed (a b : ℝ) : Ens ℝ :=
  ⟨λ x, R.ρ a x × R.ρ x b, λ x, begin apply productProp <;> apply R.κ.prop end⟩

  hott def R.notNotTotal (x y : ℝ) : R.ρ x y → x > y → 𝟎 :=
  begin intros p q; apply q.1; apply @antisymmetric.asymm R.κ; exact q.2; exact p end

  hott def R.totalIsProp (x y : ℝ) : prop (R.ρ x y + (x > y)) :=
  begin
    intros p q; match p, q with
    | Sum.inl p₁,      Sum.inl q₁      => { apply ap; apply R.κ.prop }
    | Sum.inl p₁,      Sum.inr q₂      => { apply explode; apply R.notNotTotal x y <;> assumption }
    | Sum.inr p₂,      Sum.inl q₁      => { apply explode; apply R.notNotTotal x y <;> assumption }
    | Sum.inr (p, p'), Sum.inr (q, q') => { apply ap; apply Product.prod; apply notIsProp; apply R.κ.prop }
  end

  hott def R.total (x y : ℝ) : R.ρ x y + (x > y) :=
  begin
    apply (Theorems.Equiv.propEquiv _).left;
    apply Merely.lift _ (@connected.total R.κ _ x y);
    { intro H; induction H; left; assumption;
      match @Classical.lem _ (x = y) (R.hset _ _) with
      | Sum.inl p₁ => _ | Sum.inr p₂ => _;
      left; induction p₁; apply @reflexive.refl R.κ;
      right; apply Prod.mk; intro r; apply p₂;
      exact Id.symm r; assumption };
    { apply R.totalIsProp }
  end

  hott def abs (x : ℝ) : ℝ :=
  Coproduct.elim (λ _, x) (λ _, -x) (R.total 0 x)

  hott def abs.pos {x : ℝ} (p : R.ρ 0 x) : abs x = x :=
  begin
    change Coproduct.elim _ _ _ = _; induction R.total 0 x;
    reflexivity; apply explode;
    apply R.notNotTotal 0 x <;> assumption
  end

  hott def R.zeroEqMinusZero {x : ℝ} (p : x = 0) : x = -x :=
  begin
    transitivity; exact p; symmetry;
    transitivity; apply ap; exact p;
    symmetry; apply @Group.unitInv R.τ⁺
  end

  hott def abs.neg {x : ℝ} (p : R.ρ x 0) : abs x = -x :=
  begin
    change Coproduct.elim _ _ _ = _; induction R.total 0 x;
    change x = -x; apply R.zeroEqMinusZero;
    apply @antisymmetric.asymm R.κ <;> assumption; reflexivity
  end

  hott def R.zeroLeImplZeroGeMinus {x : ℝ} (p : R.ρ 0 x) : R.ρ (-x) 0 :=
  begin
    apply Equiv.transport (λ y, R.ρ (-x) y); symmetry;
    apply @Group.unitInv R.τ⁺; apply minusInvSign; exact p
  end

  hott def R.zeroLeMinusImplZeroGe {x : ℝ} (p : R.ρ 0 (-x)) : R.ρ x 0 :=
  begin
    apply Equiv.transport (R.ρ · 0); apply @Group.invInv R.τ⁺;
    apply R.zeroLeImplZeroGeMinus; assumption
  end

  hott def R.zeroGeMinusImplZeroLe {x : ℝ} (p : R.ρ (-x) 0) : R.ρ 0 x :=
  begin
    apply invMinusSign; apply Equiv.transport (R.ρ (-x));
    apply @Group.unitInv R.τ⁺; exact p
  end

  hott def R.zeroGeImplZeroLeMinus {x : ℝ} (p : R.ρ x 0) : R.ρ 0 (-x) :=
  begin
    apply R.zeroGeMinusImplZeroLe; apply Equiv.transport (R.ρ · 0);
    symmetry; apply @Group.invInv R.τ⁺; assumption
  end

  hott def abs.even (x : ℝ) : abs x = abs (-x) :=
  begin
    match R.total 0 x with
    | Sum.inl p => {
      transitivity; apply abs.pos p; symmetry;
      transitivity; apply abs.neg;
      apply R.zeroLeImplZeroGeMinus p;
      apply @Group.invInv R.τ⁺
    }
    | Sum.inr q => {
      transitivity; apply abs.neg q.2; symmetry;apply abs.pos;
      apply R.zeroGeImplZeroLeMinus q.2
    }
  end

  hott def abs.ge (x : ℝ) : R.ρ x (abs x) :=
  begin
    match R.total 0 x with
    | Sum.inl p => {
      apply Equiv.transport (R.ρ x); symmetry;
      apply abs.pos p; apply @reflexive.refl R.κ
    }
    | Sum.inr q => {
      apply Equiv.transport (R.ρ x); symmetry;
      apply abs.neg q.2; apply @transitive.trans R.κ;
      apply q.2; apply R.zeroGeImplZeroLeMinus q.2
    }
  end

  hott def abs.le (x : ℝ) : R.ρ (-(abs x)) x :=
  begin
    match R.total 0 x with
    | Sum.inl p => {
      apply Equiv.transport (R.ρ · x); symmetry;
      apply ap; apply abs.pos p; apply @transitive.trans R.κ;
      apply R.zeroLeImplZeroGeMinus p; assumption
    }
    | Sum.inr q => {
      apply Equiv.transport (R.ρ · x); symmetry;
      transitivity; apply ap; apply abs.neg q.2;
      apply @Group.invInv R.τ⁺; apply @reflexive.refl R.κ
    }
  end

  hott def abs.leIfMinusLeAndLe (x y : ℝ) (r₁ : R.ρ (-x) y) (r₂ : R.ρ y x) : R.ρ (abs y) x :=
  begin
    match R.total 0 y with
    | Sum.inl p => {
      apply Equiv.transport (R.ρ · x); symmetry;
      apply abs.pos p; assumption
    }
    | Sum.inr q => {
      apply Equiv.transport (R.ρ · x); symmetry;
      apply abs.neg q.2; apply invMinusSign;
      apply Equiv.transport (R.ρ (-x)); symmetry;
      apply @Group.invInv R.τ⁺; assumption
    }
  end

  hott def abs.geZero (x : ℝ) : R.ρ 0 (abs x) :=
  begin
    match R.total 0 x with
    | Sum.inl p => {
      apply Equiv.transport (R.ρ 0);
      symmetry; apply abs.pos p; assumption
    }
    | Sum.inr q => {
      apply Equiv.transport (R.ρ 0); symmetry; apply abs.neg q.2;
      apply R.zeroGeImplZeroLeMinus; exact q.2
    }
  end

  hott def abs.leIfAbsLe (x y : ℝ) (r : R.ρ (abs y) x) : R.ρ y x :=
  begin apply @transitive.trans R.κ; apply abs.ge; assumption end

  hott def abs.geIfAbsLe (x y : ℝ) (r : R.ρ (abs y) x) : R.ρ (-x) y :=
  begin
    apply geIfMinusLe; apply @transitive.trans R.κ;
    apply geIfMinusLe; apply abs.le; assumption
  end

  hott def abs.zero : abs 0 = 0 :=
  begin apply abs.pos; apply @reflexive.refl R.κ end

  hott def R.leIfEq {x y : ℝ} (p : x = y) : R.ρ x y :=
  begin induction p; apply @reflexive.refl R.κ end

  hott def R.geIfEq {x y : ℝ} (p : x = y) : R.ρ y x :=
  begin induction p; apply @reflexive.refl R.κ end

  hott def abs.zeroIf (x : ℝ) (p : abs x = 0) : x = 0 :=
  begin
    apply @antisymmetric.asymm R.κ; apply Equiv.transport (R.ρ x); exact p; apply abs.ge;
    { apply Equiv.transport (R.ρ · x); symmetry; apply @Group.unitInv R.τ⁺;
      apply @transitive.trans R.κ; apply minusInvSign;
      apply R.leIfEq p; apply abs.le }
  end

  hott def doubleGeZeroImplGeZero {x : ℝ} : R.ρ 0 (x + x) → R.ρ 0 x :=
  begin
    intro p; induction R.total 0 x;
    { case inl q₁ => apply q₁ };
    { case inr q₂ =>
      apply explode; apply (strictIneqAdd R q₂ q₂).1;
      apply @antisymmetric.asymm R.κ; apply ineqAdd <;> exact q₂.2;
      apply Equiv.transport (R.ρ · (x + x)); symmetry; apply R.τ⁺.mulOne; exact p }
  end

  hott def tendsto {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x₀ L, ∀ (ε : ℝ), 0 < ε → ∥Σ (δ : ℝ), (0 < δ) × (Π x, 0 < M₁.ρ x x₀ → M₁.ρ x x₀ < δ → M₂.ρ (f x) L < ε)∥

  hott def continuous {M₁ M₂ : Metric} (f : M₁.carrier → M₂.carrier) :=
  λ x, tendsto f x (f x)

  hott def continuous.pointed (M₁ M₂ : Metric⁎) := @continuous M₁.1 M₂.1
  notation "continuous⁎" => continuous.pointed

  hott def absolute (G : Group) (φ : G.carrier → ℝ) :=
    (Π x, φ x = 0 ↔ x = G.e)
  × (Π x, φ x = φ (G.ι x))
  × (Π x y, R.ρ (φ (G.φ x y)) (φ x + φ y))

  hott def Absolute (G : Group) :=
  Σ (φ : G.carrier → ℝ), absolute G φ

  hott def Absolute.geZero {G : Group} (A : Absolute G) : Π x, R.ρ 0 (A.1 x) :=
  begin
    intro x; apply doubleGeZeroImplGeZero; apply Equiv.transport (R.ρ · _);
    apply (A.2.1 (G.φ x (G.ι x))).right; apply Group.mulRightInv;
    apply Equiv.transport (λ w, R.ρ (A.1 (G.φ x (G.ι x))) (A.1 x + w));
    symmetry; apply (A.2.2.1 x); apply A.2.2.2
  end

  hott def Absolute.zeroIf {G : Group}
    (A : Absolute G) : Π x, R.ρ (A.1 x) 0 → A.1 x = 0 :=
  begin intros x p; apply @antisymmetric.asymm R.κ; exact p; apply Absolute.geZero end

  hott def Absolute.metric (G : Group) (A : Absolute G) :=
  λ x y, A.1 (G.φ x (G.ι y))

  hott def Absolute.metrizable (G : Group) (A : Absolute G) : Algebra.metric (Absolute.metric G A) :=
  begin
    apply (_, (_, _));
    { intros x y; apply Prod.mk <;> intro p;
      { apply Group.eqOfRdivEq;
        apply (A.2.1 (G.φ x (G.ι y))).left; apply p };
      { apply (A.2.1 (G.φ x (G.ι y))).right;
        induction p; apply Group.mulRightInv } };
    { intros x y; transitivity; apply A.2.2.1 (G.φ x (G.ι y));
      apply ap A.1; transitivity; apply Group.invExplode;
      apply ap (λ z, G.φ z (G.ι x)); apply Group.invInv };
    { intros x y z; apply Equiv.transport (R.ρ · _);
      apply ap A.1; apply Group.chainRdiv x y z; apply A.2.2.2 }
  end

  hott def Absolute.space (G : Group) (A : Absolute G) : Metric :=
  ⟨G.1.1, ⟨Absolute.metric G A, Absolute.metrizable G A⟩⟩

  hott def Absolute.mulInv (G : Group) (A : Absolute G)
    (x y : G.carrier) : R.ρ (abs (A.1 x - A.1 y)) (A.1 (G.φ x y)) :=
  begin
    apply abs.leIfMinusLeAndLe;
    { apply geIfMinusLe; apply Equiv.transport (λ w, R.ρ w _);
      symmetry; apply @Group.mulInvInv R.τ⁺; apply subLeIfAddGeRev;
      apply Equiv.transport (λ w, R.ρ (A.1 y) (w + A.1 (G.φ x y))); symmetry; apply A.2.2.1;
      apply Equiv.transport (R.ρ · _); apply ap A.1; symmetry; apply Group.revCancelLeft x y; apply A.2.2.2 };
    { apply subLeIfAddGe; apply Equiv.transport (λ w, R.ρ (A.1 x) (A.1 (G.φ x y) + w));
      symmetry; apply A.2.2.1; apply Equiv.transport (R.ρ · _);
      apply ap A.1; symmetry; apply Group.cancelRight x y; apply A.2.2.2 }
  end

  hott def triangle (x y : ℝ) : R.ρ (abs (x + y)) (abs x + abs y) :=
  begin
    apply abs.leIfMinusLeAndLe;
    { apply Equiv.transport (R.ρ · (x + y)); symmetry; transitivity;
      apply @Group.invExplode R.τ⁺; apply R.τ.addComm;
      apply ineqAdd <;> apply abs.le };
    { apply ineqAdd <;> apply abs.ge }
  end

  hott def R.absolute : absolute R.τ⁺ abs :=
  begin
    apply (_, (_, _)); intro; apply Prod.mk; apply abs.zeroIf;
    { intro p; transitivity; exact ap abs p; apply abs.zero };
    apply abs.even; apply triangle
  end

  hott def R.metrizable : metric (λ x y, abs (x - y)) :=
  Absolute.metrizable.{0} R.τ⁺ ⟨abs, R.absolute⟩

  hott def Rₘ : Metric :=
  ⟨R.1, ⟨λ (x y : ℝ), abs (x - y), R.metrizable⟩⟩

  hott def triangleSub (x y z : ℝ) : R.ρ (abs (x - z)) (abs (x - y) + abs (y - z)) :=
  Rₘ.triangle x y z

  hott def R.revTriangleIneq (x y : ℝ) : R.ρ (abs (abs x - abs y)) (abs (x + y)) :=
  Absolute.mulInv R.τ⁺ ⟨abs, R.absolute⟩ x y

  hott def R.pointed : Metric⁎ := ⟨Rₘ, R.τ⁺.e⟩
  notation "R⁎" => R.pointed

  hott def R.singleton : ℝ → Ens ℝ :=
  Ens.singleton R.hset

  hott def R.singlInh : Π x, (R.singleton x).inh :=
  Ens.singletonInh R.hset

  hott def R.singlMajorized (x : ℝ) : @majorized R.κ (R.singleton x) :=
  begin apply Merely.elem; existsi x; intros y p; induction p; apply @reflexive.refl R.κ end

  hott def sup.singleton (x : ℝ) :
    sup (R.singleton x) (R.singlInh x) (R.singlMajorized x) = x :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply sup.exact; intros y p; induction p; apply @reflexive.refl R.κ };
    { apply sup.lawful; change _ = _; reflexivity }
  end

  hott def Absolute.continuous (G : Group)
    (A : Absolute G) : Π m, @continuous (Absolute.space G A) Rₘ A.1 m :=
  begin
    intros x ε H; apply Merely.elem; existsi ε; apply Prod.mk; exact H;
    intros y G₁ G₂; apply Equiv.transport (λ w, abs (A.1 y - w) < ε);
    symmetry; apply A.2.2.1; apply strictIneqTransLeft;
    apply Absolute.mulInv; exact G₂
  end

  hott def Metric.positive (M : Metric) (x y : M.carrier) : R.ρ 0 (M.ρ x y) :=
  begin
    apply doubleGeZeroImplGeZero; apply Equiv.transport (λ z, R.ρ z (M.ρ x y + M.ρ x y));
    apply M.refl x; apply Equiv.transport (λ z, R.ρ (M.ρ x x) (M.ρ x y + z));
    apply M.symm; apply M.triangle
  end

  hott def Metric.eqIfLeZero (M : Metric) {x y : M.carrier} : R.ρ (M.ρ x y) 0 → x = y :=
  begin intro p; apply M.eqv; apply @antisymmetric.asymm R.κ; exact p; apply M.positive end

  hott def Closed (a b : ℝ) := (R.closed a b).subtype

  hott def I := Closed 0 1
  notation "𝕀" => I

  hott def I.zero : I :=
  ⟨0, (@reflexive.refl R.κ _ _, zeroLeOne)⟩

  hott def I.one : I :=
  ⟨1, (zeroLeOne, @reflexive.refl R.κ _ _)⟩

  hott instance : OfNat I Nat.zero := ⟨I.zero⟩
  hott instance : OfNat I (Nat.succ Nat.zero) := ⟨I.one⟩

  hott def I.neg : 𝕀 → 𝕀 :=
  λ ⟨i, p, q⟩, begin
    existsi (1 - i); apply Prod.mk; apply subGeZeroIfLe; exact q;
    apply subLeIfAddGe; apply Equiv.transport (R.ρ · _);
    apply R.τ⁺.mulOne; apply leOverAddLeft; exact p
  end
end GroundZero.Algebra
