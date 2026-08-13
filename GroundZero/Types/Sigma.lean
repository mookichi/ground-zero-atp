import GroundZero.Theorems.Funext
import GroundZero.Types.Equiv
import GroundZero.Types.Coproduct

open GroundZero.Types.Equiv (apd pathOverAp transport)
open GroundZero.Types.Id (ap)

namespace GroundZero.Types
universe u v w

namespace Sigma
  variable {A : Type u} {B : A → Type v}

  hott definition pr₁ (x : Σ x, B x) := x.1
  hott definition pr₂ (x : Σ x, B x) := x.2

  hott definition elim {C : Type w} (g : Π x, B x → C) (w : Sigma B) : C := g w.1 w.2

  hott definition Ind {π : Sigma B → Type w} (g : Π (a : A) (b : B a), π ⟨a, b⟩) : Π x, π x :=
  λ w, g w.1 w.2

  hott remark uniq : Π (x : Σ x, B x), ⟨pr₁ x, pr₂ x⟩ = x := idp

  hott definition prod : Π {u v : Sigma B} (p : u.1 = v.1) (q : transport B p u.2 = v.2), u = v :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y); induction p;
    intro (q : u = v); induction q; apply idp
  end

  hott theorem mapFstOverProd : Π {u v : Sigma B} (p : u.1 = v.1) (q : transport B p u.2 = v.2), ap pr₁ (prod p q) = p :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y); induction p;
    intro (q : u = v); induction q; apply idp
  end

  hott theorem mapSndOverProd : Π {u v : Sigma B} (p : u.1 = v.1) (q : transport B p u.2 = v.2),
    apd pr₂ (prod p q) = pathOverAp Sigma.fst (prod p q) (transport (λ s, u.2 =[s] v.2) (mapFstOverProd p q)⁻¹ q) :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y); induction p;
    intro (q : u = v); induction q; reflexivity
  end

  hott lemma apOverSigma (f : Π x, B x) {a b : A} (p : a = b) :
    @ap A (Σ x, B x) a b (λ x, ⟨x, f x⟩) p = Sigma.prod p (apd f p) :=
  begin induction p; reflexivity end

  hott lemma prodRefl (u : Sigma B) : prod (idp u.1) (idp u.2) = idp u :=
  idp (idp u)

  hott lemma prodComp : Π {x y z : Sigma B} (p : x.1 = y.1) (q : y.1 = z.1)
    (r : x.2 =[p] y.2) (s : y.2 =[q] z.2), prod (p ⬝ q) (r ⬝′ s) = prod p r ⬝ prod q s :=
  begin
    intro ⟨x, X⟩ ⟨y, Y⟩ ⟨z, Z⟩ (p : x = y) (q : y = z);
    induction p; induction q; intro (r : X = Y) (s : Y = Z);
    induction r; induction s; apply idp
  end

  hott lemma prodEq : Π {u v : Sigma B} (p p' : u.1 = v.1)
    (q : transport B p u.2 = v.2) (q' : transport B p' u.2 = v.2)
    (r : p = p') (s : q =[λ ρ, transport B ρ u.2 = v.2, r] q'),
    Sigma.prod p q = Sigma.prod p' q' :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩ (p : x = y) (p' : x = y) q q' r;
    induction r; induction p; intro (s : q = q'); induction s; apply idp
  end

  hott definition spec {A : Type u} {B : Type v} (w : Σ (a : A), B) : A × B := (w.1, w.2)
  hott definition gen {A : Type u} {B : Type v} (w : A × B) : Σ (a : A), B := ⟨w.1, w.2⟩

  hott lemma const (A : Type u) (B : Type v) : (Σ (a : A), B) ≃ A × B :=
  Equiv.intro spec gen idp idp

  hott definition hmtpyInv {A : Type v} {B : Type u} (f g : A → B)
    (w : Σ x, f x = g x) : (Σ x, g x = f x) :=
  ⟨w.1, w.2⁻¹⟩

  hott definition map {A : Type v} {η : A → Type u} {ε : A → Type w}
    (f : Π x, η x → ε x) (w : Σ x, η x) : (Σ x, ε x) :=
  ⟨w.1, f w.1 w.2⟩

  hott theorem respectsEquiv {A : Type u} {η : A → Type v} {ε : A → Type w}
    (e : Π x, η x ≃ ε x) : (Σ x, η x) ≃ (Σ x, ε x) :=
  begin
    existsi (map (λ x, (e x).forward)); apply Prod.mk;
    { existsi (map (λ x, (e x).left)); intro w;
      apply ap (Sigma.mk w.1); apply (e w.1).leftForward };
    { existsi (map (λ x, (e x).right)); intro w;
      apply ap (Sigma.mk w.1); apply (e w.1).forwardRight }
  end

  hott lemma replaceIshae {A : Type u} {B : Type v} {C : A → Type w}
    (g : B → A) (ρ : ishae g) : (Σ x, C x) ≃ (Σ x, C (g x)) :=
  begin
    existsi (λ w, ⟨ρ.1 w.1, Equiv.transport C (ρ.2.2.1 w.1)⁻¹ w.2⟩);
    apply Qinv.toBiinv; existsi (λ w, ⟨g w.1, w.2⟩); apply Prod.mk <;> intro w;
    { apply @prod B (C ∘ g) ⟨ρ.1 (g w.1), _⟩ w (ρ.2.1 w.1);
      transitivity; apply Equiv.transportComp;
      transitivity; symmetry; apply Equiv.transportcom;
      transitivity; apply ap (λ p, transport C p w.2);
      apply Id.compReflIfEq; symmetry; apply ρ.2.2.2; reflexivity };
    { apply prod; apply Equiv.transportBackAndForward }
  end

  hott corollary hmtpyInvEqv {A : Type v} {B : Type u} (f g : A → B) : (Σ x, f x = g x) ≃ (Σ x, g x = f x) :=
  respectsEquiv (λ _, Equiv.inveqv)

  hott definition sigmaEqOfEq {a b : Σ x, B x} (p : a = b) : (Σ (p : a.1 = b.1), transport B p a.2 = b.2) :=
  begin induction p; existsi idp a.1; reflexivity end

  hott definition eqOfSigmaEq {a b : Σ x, B x} (p : Σ (p : a.1 = b.1), transport B p a.2 = b.2) : (a = b) :=
  Sigma.prod p.1 p.2

  hott lemma prodRepr {a b : Σ x, B x} : @eqOfSigmaEq A B a b ∘ @sigmaEqOfEq A B a b ~ id :=
  begin intro p; induction p; reflexivity end

  hott lemma reprProd : Π {a b : Σ x, B x}, @sigmaEqOfEq A B a b ∘ @eqOfSigmaEq A B a b ~ id :=
  begin intro ⟨a, u⟩ ⟨b, v⟩ ⟨(p : a = b), q⟩; induction p; dsimp at q; induction q; apply idp end

  hott theorem sigmaPath {a b : Σ x, B x} : (a = b) ≃ (Σ (p : a.1 = b.1), transport B p a.2 = b.2) :=
  begin
    existsi sigmaEqOfEq; apply Qinv.toBiinv;
    existsi eqOfSigmaEq; apply Prod.mk; apply reprProd; apply prodRepr
  end

  hott theorem assoc (C : (Σ x, B x) → Type w) : (Σ x, Σ y, C ⟨x, y⟩) ≃ (Σ p, C p) :=
  begin
    fapply Equiv.intro;
    { intro w; existsi ⟨w.1, w.2.1⟩; exact w.2.2 };
    { intro w; existsi w.1.1; existsi w.1.2; exact w.2 };
    { intro; reflexivity };
    { intro; reflexivity }
  end

  hott theorem prodSigmaDistrib {A : Type u} {P : A → Type v} {B : Type w} :
    (Σ a, P a) × B ≃ (Σ a, P a × B) :=
  begin
    fapply Equiv.intro;
    { intro w; existsi w.1.1; exact (w.1.2, w.2) };
    { intro w; exact (⟨w.1, w.2.1⟩, w.2.2) };
    { intro w; reflexivity };
    { intro w; reflexivity }
  end

  hott theorem comm {A : Type u} {B : Type v} (C : A → B → Type w) :
    (Σ a : A, Σ b : B, C a b) ≃ (Σ b : B, Σ a : A, C a b) :=
  begin
    fapply Equiv.intro;
    { intro w; existsi w.2.1; existsi w.1; exact w.2.2 };
    { intro w; existsi w.2.1; existsi w.1; exact w.2.2 };
    { intro w; reflexivity };
    { intro w; reflexivity }
  end

  hott theorem piSigmaSwap {A : Type u} {B : A → Type v} (P : Π a, B a → Type w) :
    (Π a, Σ b, P a b) ≃ (Σ f : Π a, B a, Π a, P a (f a)) :=
  begin
    let fw : (Π a, Σ b, P a b) → (Σ f : Π a, B a, Π a, P a (f a)) :=
      λ g, ⟨λ a, (g a).1, λ a, (g a).2⟩;
    let bw : (Σ f : Π a, B a, Π a, P a (f a)) → (Π a, Σ b, P a b) :=
      λ w a, ⟨w.1 a, w.2 a⟩;
    fapply Equiv.intro fw bw;
    { intro h; apply GroundZero.HITs.Interval.funext; intro a; exact uniq (h a) };
    { intro w;
      change ⟨λ a, w.1 a, λ a, w.2 a⟩ = w;
      exact uniq w }
  end

  /- Σ over the empty type (Tier 2 gap fill). -/
  hott theorem sigmaEmpty (P : 𝟎 → Type v) : (Σ x : 𝟎, P x) ≃ 𝟎 :=
  begin
    fapply Equiv.intro;
    { intro w; exact w.1 };
    { intro x; exact GroundZero.Proto.explode x };
    { intro w; induction w with | mk x px => induction x };
    { intro x; induction x }
  end

  /- Moved here from HITs/Circle.lean (was buried there). -/
  hott theorem sigmaSumDistrib {A : Type u} (B : A → Type v) (C : A → Type w) :
    (Σ x, B x + C x) ≃ (Σ x, B x) + (Σ x, C x) :=
  begin
    fapply Equiv.intro;
    { intro w; exact Sum.casesOn w.2 (λ b, Sum.inl ⟨w.1, b⟩) (λ c, Sum.inr ⟨w.1, c⟩) };
    { intro s; exact Sum.casesOn s (λ w, ⟨w.1, Sum.inl w.2⟩) (λ w, ⟨w.1, Sum.inr w.2⟩) };
    { intro w; induction w with | mk x bx => induction bx with
      | inl b => reflexivity
      | inr c => reflexivity };
    { intro s; induction s with
      | inl w₁ => reflexivity
      | inr w₂ => reflexivity }
  end
end Sigma

end GroundZero.Types
