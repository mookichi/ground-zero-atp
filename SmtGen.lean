import GroundZero

universe u

namespace SmtCert

open GroundZero.Proto
open GroundZero.Types.Id
open GroundZero.Types
open GroundZero.Types.Coproduct
open GroundZero.Types.Unit
open GroundZero.Structures
open GroundZero.Theorems.Nat
open GroundZero.Theorems.Classical

hott axiom byContradictionAxiom (A : Type u) : (¬A → 𝟎) → A
hott definition byContradiction (A : Type u) (H : prop A) : (¬A → 𝟎) → A :=
dneg.decode H
hott axiom trust (A : Type u) : A

hott definition AndIntro (a b : Type u) (x : a) (y : b) : a × b := Prod.mk x y
hott definition AndLeft (a b : Type u) (h : a × b) : a := h.1
hott definition AndRight (a b : Type u) (h : a × b) : b := h.2
hott definition OrInl (a b : Type u) (x : a) : a + b := Sum.inl x
hott definition OrInr (a b : Type u) (y : b) : a + b := Sum.inr y
hott definition OrElim (a b c : Type u) (h : a + b) (f : a → c) (g : b → c) : c :=
Coproduct.elim f g h
hott definition FalseRec (C : Type u) (h : 𝟎) : C := explode h
hott definition FalseElim (C : Type u) (h : 𝟎) : C := explode h
hott definition TrueTrivial : 𝟏 := ★

hott definition ArithLeTrans (a b c : ℕ) (h : a ≤ b) (k : b ≤ c) : a ≤ c :=
GroundZero.Theorems.Nat.le.trans h k

hott definition ArithLtLeContra (a b : ℕ) (h : a + 1 ≤ b) (k : b ≤ a) : 𝟎 :=
GroundZero.Theorems.Nat.le.neSucc a (GroundZero.Theorems.Nat.le.trans h k)

hott definition ArithLtLtContra (a b : ℕ) (h : a + 1 ≤ b) (k : b + 1 ≤ a) : 𝟎 :=
GroundZero.Theorems.Nat.le.neSucc a
  (GroundZero.Theorems.Nat.le.trans
    (GroundZero.Theorems.Nat.le.trans h (GroundZero.Theorems.Nat.le.leSucc b)) k)

hott definition ArithNotSuccLeZero (a : ℕ) (h : a + 1 ≤ 0) : 𝟎 :=
GroundZero.Theorems.Nat.le.neSucc a
  (GroundZero.Theorems.Nat.le.trans h (GroundZero.Theorems.Nat.max.zeroLeft a))

hott definition ArithLeInj (a b : ℕ) (h : a + 1 ≤ b + 1) : a ≤ b :=
GroundZero.Theorems.Nat.le.inj a b h

hott definition ArithLeStep (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 :=
GroundZero.Theorems.Nat.le.step a b h


hott definition smt_unsat : ((x108 : ℕ) → ((x109 : (((GroundZero.Theorems.Nat.le (Nat.succ ((Nat.add x108) (Nat.succ 0)))) 0) × ((GroundZero.Theorems.Nat.le 0) x108))) → 𝟎)) :=
(λ x108 : ℕ => (λ x109 : (((GroundZero.Theorems.Nat.le (Nat.succ ((Nat.add x108) (Nat.succ 0)))) 0) × ((GroundZero.Theorems.Nat.le 0) x108)) => ((ArithNotSuccLeZero ((Nat.add x108) (Nat.succ 0))) (((AndLeft ((GroundZero.Theorems.Nat.le (Nat.succ ((Nat.add x108) (Nat.succ 0)))) 0)) ((GroundZero.Theorems.Nat.le 0) x108)) x109))))

end SmtCert
