import GroundZero.Theorems.Univalence
import GroundZero.Types.Nat

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto

namespace GroundZero
namespace Theorems

namespace Nat
  universe u

  hott lemma codeIsProp : Π n m, prop (Nat.code n m)
  | Nat.zero,   Nat.zero   => unitIsProp
  | Nat.succ n, Nat.zero   => emptyIsProp
  | Nat.zero,   Nat.succ m => emptyIsProp
  | Nat.succ n, Nat.succ m => codeIsProp n m

  hott theorem natIsSet' : hset ℕ :=
  λ n m, propRespectsEquiv (Nat.recognize n m).symm (codeIsProp n m)

  hott corollary succInj {n m : ℕ} : Nat.succ n = Nat.succ m → n = m :=
  Nat.decode ∘ Nat.encode

  hott definition natDecEq : Π (m n : ℕ), dec (m = n)
  | Nat.zero,   Nat.zero   => Sum.inl (idp 0)
  | Nat.succ m, Nat.zero   => Sum.inr succNeqZero
  | Nat.zero,   Nat.succ n => Sum.inr (succNeqZero ∘ Id.inv)
  | Nat.succ m, Nat.succ n =>
    match natDecEq m n with
    | Sum.inl p => Sum.inl (ap Nat.succ p)
    | Sum.inr φ => Sum.inr (φ ∘ succInj)

  hott theorem natIsSet : hset ℕ := Hedberg natDecEq

  hott theorem zeroPlus : Π (i : ℕ), 0 + i = i
  | Nat.zero   => idp 0
  | Nat.succ i => ap Nat.succ (zeroPlus i)

  hott lemma succPlus (i : ℕ) : Π j, Nat.succ i + j = Nat.succ (i + j)
  | Nat.zero   => idp _
  | Nat.succ j => ap Nat.succ (succPlus i j)

  hott theorem comm : Π (i j : ℕ), i + j = j + i
  | Nat.zero,   j => zeroPlus j
  | Nat.succ i, j => succPlus i j ⬝ ap Nat.succ (comm i j)

  hott theorem assoc (i j : ℕ) : Π k, (i + j) + k = i + (j + k)
  | Nat.zero   => idp (i + j)
  | Nat.succ k => ap Nat.succ (assoc i j k)

  hott theorem zeroMul : Π (i : ℕ), 0 * i = 0
  | Nat.zero   => idp 0
  | Nat.succ i => zeroMul i

  hott theorem oneMul : Π (i : ℕ), 1 * i = i
  | Nat.zero   => idp 0
  | Nat.succ i => ap Nat.succ (oneMul i)

  hott corollary mulOne (i : ℕ) : i * 1 = i := zeroPlus i

  hott theorem distribLeft (i : ℕ) : Π (j n : ℕ), n * (i + j) = n * i + n * j
  | Nat.zero,   n => idp _
  | Nat.succ j, n => ap (λ m, m + n) (distribLeft i j n) ⬝ assoc _ _ _

  hott lemma mulSucc (i : ℕ) : Π j, Nat.succ i * j = i * j + j
  | Nat.zero   => idp _
  | Nat.succ j => ap Nat.succ (ap (λ k, k + i) (mulSucc i j) ⬝ assoc _ _ _
                                ⬝ (assoc _ _ _ ⬝ ap _ (comm _ _))⁻¹)

  hott theorem mulComm (i : ℕ) : Π j, i * j = j * i
  | Nat.zero   => (zeroMul _)⁻¹
  | Nat.succ j => distribLeft j 1 i ⬝ (mulSucc j i ⬝ bimap Nat.add (mulComm i j)⁻¹ (mulOne i)⁻¹)⁻¹

  hott lemma succMul (i j : ℕ) : i * Nat.succ j = i * j + i :=
  mulComm _ _ ⬝ mulSucc _ _ ⬝ Id.ap (Nat.add · _) (mulComm _ _)

  hott corollary mulZero (i : ℕ) : i * 0 = 0 := mulComm i 0 ⬝ zeroMul i

  hott theorem mulAssoc (i j : ℕ) : Π k, (i * j) * k = i * (j * k)
  | Nat.zero   => mulZero (i * j) ⬝ (ap (λ m, i * m) (mulZero j) ⬝ mulZero i)⁻¹
  | Nat.succ k => succMul (i * j) k ⬝ ap (λ m, m + (i * j)) (mulAssoc i j k) ⬝
                  (distribLeft (j * k) j i)⁻¹ ⬝ (ap (λ m, i * m) (succMul j k))⁻¹

  hott corollary distribRight (i j n : ℕ) : (i + j) * n = i * n + j * n :=
  mulComm (i + j) n ⬝ distribLeft _ _ _ ⬝ bimap Nat.add (mulComm _ _) (mulComm _ _)

  hott proposition oneNeqNPlusTwo (n : ℕ) : ¬(1 = n + 2) :=
  λ p, succNeqZero (ap Nat.pred p)⁻¹

  hott definition isEven (n : ℕ) := Σ m, n = m * 2
  hott definition isOdd  (n : ℕ) := Σ m, n = m * 2 + 1

  hott lemma plusOnePlus {i j : ℕ} : i + 1 + j = (i + j) + 1 :=
  calc i + 1 + j = i + (1 + j) : assoc _ _ _,
                 = i + (j + 1) : ap (Nat.add i) (comm 1 j),
                 = (i + j) + 1 : idp _

  hott lemma assocTetra {i j k l : ℕ} : i + (j + k) + l = (i + j) + (k + l) := calc
    (i + (j + k)) + l = i + ((j + k) + l) : assoc _ _ _,
                      = i + (j + (k + l)) : ap _ (assoc _ _ _),
                      = (i + j) + (k + l) : (assoc _ _ _)⁻¹

  hott lemma plusDiag (n : ℕ) : n * 2 = n + n :=
  ap (λ m, m + n) (zeroPlus _)

  hott definition max : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => m + 1
  | Nat.zero,   Nat.succ n => n + 1
  | Nat.succ m, Nat.succ n => max m n + 1

  hott lemma max.comm : Π (m n : ℕ), max m n = max n m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => ap Nat.succ (max.comm _ _)

  hott definition min : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => 0
  | Nat.zero,   Nat.succ n => 0
  | Nat.succ m, Nat.succ n => min m n + 1

  hott lemma min.comm : Π (m n : ℕ), min m n = min n m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => ap Nat.succ (min.comm _ _)

  hott lemma max.refl : Π n, max n n = n
  | Nat.zero   => idp 0
  | Nat.succ n => ap Nat.succ (max.refl n)

  hott lemma min.refl : Π n, min n n = n
  | Nat.zero   => idp 0
  | Nat.succ n => ap Nat.succ (min.refl n)

  hott definition le (n m : ℕ) := max n m = m
  infix:55 (priority := high) " ≤ " => le

  hott definition ge (n m : ℕ) := m ≤ n
  infix:55 (priority := high) " ≥ " => ge

  hott lemma max.zeroLeft (n : ℕ) : max 0 n = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma max.zeroRight (n : ℕ) : max n 0 = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma min.zeroLeft (n : ℕ) : min 0 n = 0 :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma min.zeroRight (n : ℕ) : min n 0 = 0 :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma max.neZero {n : ℕ} : ¬(max (n + 1) 0 = 0) := succNeqZero

  hott lemma max.zero : Π n, max n 0 = 0 → n = 0
  | Nat.zero,   _ => idp _
  | Nat.succ n, p => explode (max.neZero p)

  hott corollary le.prop (n m : ℕ) : prop (n ≤ m) := natIsSet _ _

  hott lemma max.assoc : Π n m k, max n (max m k) = max (max n m) k
  | Nat.zero,   Nat.zero,   Nat.zero   => idp _
  | Nat.zero,   Nat.zero,   Nat.succ k => idp _
  | Nat.zero,   Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m, Nat.succ k => max.zeroLeft _
  | Nat.succ n, Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero,   Nat.succ k => idp _
  | Nat.succ n, Nat.succ m, Nat.zero   => idp _
  | Nat.succ n, Nat.succ m, Nat.succ k => ap Nat.succ (max.assoc _ _ _)

  hott lemma min.assoc : Π n m k, min n (min m k) = min (min n m) k
  | Nat.zero,   Nat.zero,   Nat.zero   => idp _
  | Nat.zero,   Nat.zero,   Nat.succ k => idp _
  | Nat.zero,   Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m, Nat.succ k => min.zeroLeft _
  | Nat.succ n, Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero,   Nat.succ k => idp _
  | Nat.succ n, Nat.succ m, Nat.zero   => idp _
  | Nat.succ n, Nat.succ m, Nat.succ k => ap Nat.succ (min.assoc _ _ _)

  hott theorem le.trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k :=
  begin
    intros p q; change _ = _; transitivity;
    apply ap; exact q⁻¹; transitivity; apply max.assoc;
    transitivity; apply ap (max · k); exact p; exact q
  end

  hott instance : Transitive le := ⟨@le.trans⟩

  hott corollary le.inj (n m : ℕ) : n + 1 ≤ m + 1 → n ≤ m := ap Nat.pred
  hott corollary le.map (n m : ℕ) : n ≤ m → n + 1 ≤ m + 1 := ap Nat.succ

  hott theorem le.addr (n m : ℕ) : Π k, n ≤ m → n + k ≤ m + k
  | Nat.zero,   h => h
  | Nat.succ k, h => le.map (n + k) (m + k) (le.addr n m k h)

  hott theorem le.addl (n m k : ℕ) (h : n ≤ m) : k + n ≤ k + m :=
  transport (_ ≤ ·) (Nat.comm m k) (transport (· ≤ _) (Nat.comm n k) (le.addr n m k h))

  hott lemma le.succ : Π (n : ℕ), n ≤ n + 1
  | Nat.zero   => idp _
  | Nat.succ n => ap Nat.succ (le.succ n)

  hott definition le.step : Π (n m : ℕ), n ≤ m → n ≤ m + 1
  | Nat.zero,   m, _ => idp _
  | Nat.succ n, m, p => le.trans p (le.succ _)

  hott lemma minMax : Π (m n : ℕ), max m n = n → min m n = m
  | Nat.zero,   Nat.zero,   p => idp _
  | Nat.succ m, Nat.zero,   p => explode (max.neZero p)
  | Nat.zero,   Nat.succ n, p => idp _
  | Nat.succ m, Nat.succ n, p => ap Nat.succ (minMax m n (ap Nat.pred p))

  hott corollary le.max (n m : ℕ) : n ≤ max n m :=
  begin
    change _ = _; transitivity; apply max.assoc;
    apply ap (Nat.max · m); apply max.refl
  end

  hott corollary le.maxRev (n m : ℕ) : n ≤ Nat.max m n :=
  transport (le n) (max.comm n m) (le.max n m)

  hott lemma le.min : Π (n m : ℕ), le (min n m) m
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => idp _
  | Nat.zero,   Nat.succ m => idp _
  | Nat.succ n, Nat.succ m => ap Nat.succ (le.min n m)

  hott lemma le.minRev (n m : ℕ) : Nat.min m n ≤ m :=
  @transport ℕ (· ≤ m) (Nat.min n m) (Nat.min m n) (min.comm n m) (le.min n m)

  hott theorem le.asymm {n m : ℕ} (p : n ≤ m) (q : m ≤ n) : n = m :=
  q⁻¹ ⬝ max.comm _ _ ⬝ p

  hott lemma le.dec : Π (m n : ℕ), (m ≤ n) + (n + 1 ≤ m)
  | Nat.zero,   Nat.zero   => Sum.inl (idp _)
  | Nat.succ m, Nat.zero   => Sum.inr (ap Nat.succ (max.zeroLeft m))
  | Nat.zero,   Nat.succ n => Sum.inl (idp _)
  | Nat.succ m, Nat.succ n => Coproduct.elim (Sum.inl ∘ ap Nat.succ) (Sum.inr ∘ ap Nat.succ) (le.dec m n)

  hott lemma le.neSucc : Π (n : ℕ), ¬(n + 1 ≤ n)
  | Nat.zero   => max.neZero
  | Nat.succ n => λ p, le.neSucc n (le.inj _ _ p)

  hott lemma le.empty (m n : ℕ) : m ≤ n → ¬(n + 1 ≤ m) :=
  begin intros p q; apply le.neSucc n; transitivity; exact q; exact p end

  hott lemma le.ofNotLe (m n : ℕ) (H : ¬(n + 1 ≤ m)) : m ≤ n :=
  match le.dec m n with | Sum.inl r₁ => r₁ | Sum.inr r₂ => explode (H r₂)

  hott lemma le.neqSucc {n m : ℕ} (p : n ≠ m + 1) (q : n ≤ m + 1) : n ≤ m :=
  match le.dec n m with
  | Sum.inl r₁ => r₁
  | Sum.inr r₂ => explode (p (le.asymm q r₂))

  hott lemma le.leSucc : Π (n : ℕ), n ≤ n + 1
  | Nat.zero   => idp _
  | Nat.succ n => ap Nat.succ (le.leSucc n)

  hott definition le.elim (ρ : ℕ → ℕ → Type u) (τ : Π n m k, ρ n m → ρ m k → ρ n k)
    (reflρ : Π n, ρ n n) (succρ : Π n, ρ n (n + 1)) {n : ℕ} : Π {m : ℕ}, n ≤ m → ρ n m
  | Nat.zero, p   => transport (ρ · 0) (max.zero _ p)⁻¹ (reflρ _)
  | Nat.succ m, p =>
    match natDecEq n (m + 1) with
    | Sum.inl q₁ => transport (ρ n) q₁ (reflρ _)
    | Sum.inr q₂ => τ n m _ (@le.elim ρ τ reflρ succρ n m (le.neqSucc q₂ p)) (succρ _)

  hott definition dist : ℕ → ℕ → ℕ
  | Nat.zero,   Nat.zero   => 0
  | Nat.succ m, Nat.zero   => Nat.succ m
  | Nat.zero,   Nat.succ n => Nat.succ n
  | Nat.succ m, Nat.succ n => dist m n

  hott lemma dist.refl : Π (n : ℕ), dist n n = 0
  | Nat.zero   => idp 0
  | Nat.succ n => dist.refl n

  hott lemma dist.identity : Π (n m : ℕ) (p : dist n m = 0), n = m
  | Nat.zero,   Nat.zero,   _ => idp 0
  | Nat.succ m, Nat.zero,   p => p
  | Nat.zero,   Nat.succ n, p => p⁻¹
  | Nat.succ m, Nat.succ n, p => ap Nat.succ (dist.identity m n p)

  hott lemma dist.symm : Π (n m : ℕ), dist n m = dist m n
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ m, Nat.zero   => idp _
  | Nat.zero,   Nat.succ n => idp _
  | Nat.succ m, Nat.succ n => dist.symm m n

  hott lemma dist.zeroLeft (n : ℕ) : dist n 0 = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma dist.zeroRight (n : ℕ) : dist 0 n = n :=
  begin induction n using Nat.casesOn <;> reflexivity end

  hott lemma dist.succLeft : Π (n m : ℕ), dist (n + 1) m ≤ dist n m + 1
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => transport (· ≤ m + 2) (dist.zeroRight m)⁻¹ (le.trans (le.leSucc _) (le.leSucc _))
  | Nat.succ n, Nat.succ m => dist.succLeft n m

  hott lemma max.leAdd : Π (n m : ℕ), le (max n m) (n + m)
  | Nat.zero,   Nat.zero   => idp _
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => transport (m + 1 ≤ ·) (zeroPlus _)⁻¹ (max.refl _)
  | Nat.succ n, Nat.succ m => le.trans (le.map (max n m) (n + m) (max.leAdd n m))
    (begin
      apply transport (n + m + 1 ≤ ·); symmetry; transitivity;
      apply Nat.assoc n 1; transitivity; transitivity; apply ap;
      symmetry; apply Nat.assoc 1 m 1; symmetry; apply Nat.assoc;
      apply ap (λ k, n + k + 1); apply Nat.comm; apply le.leSucc
    end)

  -- ℕ-specific property
  hott theorem dist.max : Π (n m : ℕ), dist n m ≤ max n m
  | Nat.zero,   Nat.zero   => idp 0
  | Nat.succ n, Nat.zero   => max.refl _
  | Nat.zero,   Nat.succ m => max.refl _
  | Nat.succ n, Nat.succ m => le.trans (dist.max n m) (le.leSucc _)

  hott corollary dist.le (n m : ℕ) : le (dist n m) (n + m) :=
  le.trans (dist.max n m) (max.leAdd n m)

  hott lemma dist.translation (n m : ℕ) : Π k, dist n m = dist (n + k) (m + k)
  | Nat.zero   => idp _
  | Nat.succ k => dist.translation n m k

  namespace Example
    hott axiom explode {P : Sort 0} : False → P := @False.rec (λ _, P)

    hott axiom Leibnitz {A : Type u} (a : A) (P : Π (b : A), Eq a b → Sort 0)
      (ref : P a rfl) (b : A) (H : Eq a b) : P b H :=
    @Eq.rec A a P ref b H

    hott axiom left  {P Q : Sort 0} : P ∧ Q → P := λ ⟨p, _⟩, p
    hott axiom right {P Q : Sort 0} : P ∧ Q → Q := λ ⟨_, q⟩, q

    hott lemma stdLeOf : Π {n m : ℕ}, le n m → LE.le n m
    | n, Nat.zero,   H => @Id.casesOn ℕ n (λ m _, LE.le n m) 0 ((max.zeroRight n)⁻¹ ⬝ H) (Nat.le_refl n)
    | n, Nat.succ m, H =>
      match natDecEq n (m + 1) with
      | Sum.inl q₁ => @Id.casesOn ℕ n (λ m _, LE.le n m) (m + 1) q₁ (Nat.le_refl n)
      | Sum.inr q₂ => Nat.le_step (@stdLeOf n m (le.neqSucc q₂ H))

    hott theorem stdLeTrans {n m k : ℕ} (H : LE.le n m) : LE.le m k → LE.le n k :=
    @Nat.le.rec m (λ k _, LE.le n k) H (λ _ G, Nat.le_step G) k

    hott lemma stdLePred : Π (n : ℕ), LE.le (Nat.pred n) n
    | Nat.zero   => Nat.le_refl 0
    | Nat.succ n => Nat.le_succ n

    hott lemma stdLeZero : Π (n : ℕ), LE.le 0 n
    | Nat.zero   => Nat.le_refl 0
    | Nat.succ n => Nat.le_step (stdLeZero n)

    hott lemma stdPredLePred {n m : ℕ} : LE.le n m → LE.le (Nat.pred n) (Nat.pred m) :=
    @Nat.le.rec n (λ m _, LE.le (Nat.pred n) (Nat.pred m)) (Nat.le_refl _) (λ H _, stdLeTrans (stdLePred n) H) m

    hott theorem stdNoLeOneZero : Not (LE.le 1 0) :=
    @Nat.le.rec 1 (λ | Nat.zero, _ => False | Nat.succ _, _ => True) True.intro (λ _ _, True.intro) 0

    hott theorem stdNoLeSucc : Π {n : ℕ}, Not (LE.le (n + 1) n)
    | Nat.zero,   H => stdNoLeOneZero H
    | Nat.succ n, H => @stdNoLeSucc n (@stdPredLePred (n + 2) (n + 1) H)

    hott lemma stdLeRev {n m : ℕ} (H : LE.le (m + 1) n) : Not (LE.le n m) :=
    λ G, @stdNoLeSucc m (stdLeTrans H G)

    hott theorem natDecLE (n m : ℕ) : Decidable (LE.le n m) :=
    match le.dec n m with
    | Sum.inl q₁ => Decidable.isTrue (stdLeOf q₁)
    | Sum.inr q₂ => Decidable.isFalse (stdLeRev (stdLeOf q₂))

    hott definition absurd {P Q : Sort 0} : P → Not P → Q :=
    λ H₁ H₂, explode (H₂ H₁)

    hott theorem decideEqTrue {P : Sort 0} : [Decidable P] → P → Eq (decide P) true
    | isTrue  _,  _  => rfl
    | isFalse H₁, H₂ => absurd H₂ H₁

    hott theorem decideEqFalse {P : Sort 0} : [Decidable P] → Not P → Eq (decide P) false
    | isTrue  H₁, H₂ => absurd H₁ H₂
    | isFalse _,  _  => rfl

    hott lemma trueNeqFalse : Not (Eq false true) :=
    Leibnitz false (λ | false, _ => True | true, _ => False) True.intro true

    hott lemma symmEq {A : Type u} {a b : A} : Eq a b → Eq b a :=
    Leibnitz a (λ c _, Eq c a) rfl b

    hott theorem neTrueOfEqFalse : Π {b : 𝟐}, Eq b false → Not (Eq b true)
    | false, H, G => trueNeqFalse G
    | true,  H, G => trueNeqFalse (symmEq H)

    hott theorem ofDecideEqTrue {P : Sort 0} [inst : Decidable P] (H₂ : Eq (decide P) true) : P :=
    match (generalizing := false) inst with
    | isTrue  H₁ => H₁
    | isFalse H₁ => absurd H₂ (neTrueOfEqFalse (decideEqFalse H₁))

    hott implementation Nat.decLe           ← natDecLE
    hott implementation decide_eq_true      ← decideEqTrue
    hott implementation decide_eq_false     ← decideEqFalse
    hott implementation ne_true_of_eq_false ← neTrueOfEqFalse
    hott implementation of_decide_eq_true   ← ofDecideEqTrue
    hott implementation Nat.le_trans        ← stdLeTrans

    hott theorem isValidChar_UInt32 {n : ℕ} : n.isValidChar → LT.lt n UInt32.size
    | Or.inl H => Nat.lt_trans H (by decide)
    | Or.inr G => Nat.lt_trans (right G) (by decide)

    hott definition charOfNatAux (n : ℕ) (h : n.isValidChar) : Char :=
    { val := UInt32.ofNatLT n (isValidChar_UInt32 h), valid := h }

    hott implementation Char.ofNatAux ← charOfNatAux

    hott check Char.ofNat
  end Example
end Nat

namespace UnitList
  universe u

  hott definition zero' : List 𝟏 := []
  hott definition succ' : List 𝟏 → List 𝟏 := List.cons ★

  hott definition ind' {E : List 𝟏 → Type u} (e₀ : E zero') (eₛ : Π (n : List 𝟏), E n → E (succ' n)) : Π n, E n
  | []      => e₀
  | ★ :: xs => eₛ xs (ind' e₀ eₛ xs)

  hott definition encode : ℕ → List 𝟏
  | Nat.zero   => zero'
  | Nat.succ n => succ' (encode n)

  hott definition decode : List 𝟏 → ℕ
  | []      => Nat.zero
  | _ :: xs => Nat.succ (decode xs)

  hott lemma decodeEncode : Π n, decode (encode n) = n
  | Nat.zero   => idp _
  | Nat.succ n => ap Nat.succ (decodeEncode n)

  hott lemma encodeDecode : Π xs, encode (decode xs) = xs
  | []      => idp _
  | ★ :: xs => ap succ' (encodeDecode xs)

  hott theorem iso : ℕ ≃ List 𝟏 :=
  ⟨encode, (⟨decode, decodeEncode⟩, ⟨decode, encodeDecode⟩)⟩

  hott corollary equality : ℕ = List 𝟏 := ua iso
end UnitList

end Theorems

namespace Structures
open GroundZero.Theorems

namespace hlevel
  hott corollary comm : Π n m, add n m = add m n
  | n, −2            => (minusTwoAdd n)⁻¹
  | n, −1            => (minusOneAdd n)⁻¹
  | n, succ (succ m) => addNatToAdd _ _ ⬝ ap predPred (Nat.comm _ _) ⬝
                        (addNatToAdd _ _)⁻¹ ⬝ (addSuccSucc m n)⁻¹
end hlevel

end Structures

end GroundZero
