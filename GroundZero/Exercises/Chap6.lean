import GroundZero.Theorems.Univalence
import GroundZero.HITs.Merely
import GroundZero.HITs.Circle
import GroundZero.HITs.Suspension
import GroundZero.HITs.Interval
import GroundZero.Types.Integer
import GroundZero.Types.Coproduct
import GroundZero.Types.Unit
import GroundZero.Types.Equiv
import GroundZero.Algebra.Monoid

open GroundZero
open GroundZero.HITs
open GroundZero.Types
open GroundZero.Types.Equiv
open GroundZero.Types.Coproduct (inl inr)
open GroundZero.Types.Unit
open GroundZero.Types.Id (ap)
open GroundZero.Structures (prop hset productProp)
open GroundZero.HITs.Interval (happly funext seg recβrule mapHapply)
open GroundZero.Algebra

universe u v w

-- ============================================================================
-- Exercise 6.2  (HoTT 6.3: Circles and spheres)
--   Prove that Susp(S¹) ≃ S², using the explicit definition of S² in
--   terms of base and surf.
--
--   In this library the spheres are defined recursively *via* suspension:
--   S 0 := 𝟚, S (n + 1) := ∑ (S n)   (Circle.lean), so this is definitional.
--   See also Exercise 6.5 below (the general Susp(Sⁿ) ≃ Sⁿ⁺¹).
-- ============================================================================

hott theorem suspS1 : Suspension Circle ≃ S² :=
Types.Equiv.ideqv _

-- ============================================================================
-- Exercise 6.5  (HoTT 6.4: Suspensions)
--   Prove that Susp(Sⁿ) ≃ Sⁿ⁺¹, using the definition of Sⁿ in terms of Ωⁿ
--   from HoTT 6.3.  (Here: definitional, because S (n + 1) := ∑ (S n).)
-- ============================================================================

hott theorem suspSphere (n : ℕ) : Suspension (S n) ≃ S (Nat.succ n) :=
Types.Equiv.ideqv _

-- ============================================================================
-- Exercise 6.7  (HoTT 6.7: monoids, groups)
--   Prove that if G is a monoid and x : G, then
--       Σ (y : G), (x·y = e) × (y·x = e)
--   is a mere proposition.  (Hence a group could equivalently be defined as a
--   monoid with *merely* existing inverses, by unique choice.)
-- ============================================================================

namespace «6.7»
  -- y₁ = e·y₁ = (y₂·x)·y₁ = y₂·(x·y₁) = y₂·e = y₂; only p₁ and q₂ are used.
  hott lemma inversePath (G : Monoid) {x y₁ y₂ : G.carrier}
    (p₁ : G.φ x y₁ = G.e) (q₂ : G.φ y₂ x = G.e) : y₁ = y₂ :=
  begin
    transitivity; apply Id.symm; apply G.oneMul;
    transitivity; apply ap (λ z, G.φ z y₁); apply Id.symm; exact q₂;
    transitivity; apply G.mulAssoc;
    transitivity; apply ap (G.φ y₂); exact p₁;
    apply G.mulOne
  end

  hott lemma inverseFiberProp (G : Monoid) (x y : G.carrier) :
    prop ((G.φ x y = G.e) × (G.φ y x = G.e)) :=
  productProp (G.hset (G.φ x y) G.e) (G.hset (G.φ y x) G.e)

  hott theorem inverseProp (G : Monoid) (x : G.carrier) :
    prop (Σ (y : G.carrier), (G.φ x y = G.e) × (G.φ y x = G.e)) :=
  begin
    intro w₁ w₂;
    fapply Sigma.prod;
    apply inversePath G w₁.2.1 w₂.2.2;
    apply inverseFiberProp G x w₂.1
  end
end «6.7»

-- ============================================================================
-- Exercise 6.8  (HoTT 6.10: Free monoids and monoid presentations)
--   Prove that if A is a set, then List A is a monoid.  Then complete the
--   proof of the free monoid theorem: for any monoid M and f : A → M there
--   is a unique monoid homomorphism extending f.
--
--   Here we formalize the monoid laws of List A (with ++ and []), and the
--   uniqueness of the extension over the term algebra Term A (the free
--   monoid presented by generators A); the library's Monoid.lean already
--   provides the evaluation maps Term.toMonoid / Term.solve / Term.ret that
--   express list-normalization (see also Term.sec / Term.ofAppend).
--
--   Note: building the full `Monoid` instance additionally needs the result
--   that List A is a set (hset (List A)) when A is a set, which requires
--   cons-injectivity machinery for the identity type and is left out here.
-- ============================================================================

namespace «6.8»
  hott lemma listAssoc {A : Type u} : Π (xs ys zs : List A), (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  begin
    intro xs; induction xs with
    | nil => intro ys zs; reflexivity
    | cons x xs ih => intro ys zs; apply ap (λ t, x :: t); apply ih
  end

  hott lemma nilAppend {A : Type u} : Π (xs : List A), [] ++ xs = xs :=
  λ xs, Id.refl

  hott lemma appendNil {A : Type u} : Π (xs : List A), xs ++ [] = xs :=
  begin
    intro xs; induction xs with
    | nil => reflexivity
    | cons x xs ih => apply ap (λ t, x :: t); apply ih
  end

  -- The unique monoid homomorphism extending f : A → M.
  -- (The library's `Term.toMonoid M` is the special case f = idfun.)
  hott definition Term.evalF {A : Type u} (M : Monoid) (f : A → M.carrier) :
    Term A → M.carrier
  | Term.φ x y => M.φ (Term.evalF M f x) (Term.evalF M f y)
  | Term.ι a   => f a
  | Term.e     => M.e

  -- Uniqueness: any monoid homomorphism h with h ∘ ι = f is the evaluation.
  hott definition Term.unique {A : Type u} (M : Monoid) (f : A → M.carrier)
    (h : Term A → M.carrier)
    (Hφ : Π x y, h (Term.φ x y) = M.φ (h x) (h y))
    (Hι : Π a, h (Term.ι a) = f a) (He : h Term.e = M.e) : h ~ Term.evalF M f :=
  begin
    intro τ; induction τ with
    | φ x y ihx ihy =>
        transitivity; apply Hφ;
        transitivity; apply ap (λ v, M.φ (h x) v); apply ihy;
        apply ap (λ u, M.φ u (Term.evalF M f y)); apply ihx
    | ι a => apply Hι
    | e => apply He
  end
end «6.8»

-- ============================================================================
-- Exercise 6.9  (HoTT 6.9: unnatural endomorphisms)
--   Assuming LEM, construct a family f : Π(X : Type), X → X such that
--   f_bool : bool → bool is the nonidentity automorphism.
-- ============================================================================

namespace «6.9»
  open GroundZero HITs Types Proto Structures Types.Equiv Theorems.Equiv

  variable (lem : LEM₋₁ 0)

  hott definition hasNonidAut (X : Type) :=
  Σ (f : X ≃ X), f ≁ idfun

  hott definition boolNonidAut : hasNonidAut 𝟐 :=
  ⟨negBoolEquiv, λ np, ffNeqTt (np true)⟩

  hott lemma boolNonidAutIsNeg (f : 𝟐 ≃ 𝟐) : f ≁ idfun → f = negBoolEquiv :=
  begin
    intro np; apply boolEquivEqvBool.eqvInj; apply neqBoolToEqNot _ false; intro p;
    apply np; apply happly; apply @ap _ _ _ (ideqv _) Equiv.forward; transitivity;
    symmetry; apply boolEquivEqvBool.leftForward; apply ap boolEquivEqvBool.left p
  end

  hott lemma boolNonidAutContr : contr (hasNonidAut 𝟐) :=
  ⟨boolNonidAut, λ w, Sigma.prod (boolNonidAutIsNeg _ w.2)⁻¹ (notIsProp _ _)⟩

  hott lemma merelyBoolNonidAutContr (X : Type) : ∥X ≃ 𝟐∥ → contr (hasNonidAut X) :=
  Merely.rec contrIsProp (λ f, transport (contr ∘ hasNonidAut) (ua f)⁻¹ boolNonidAutContr)

  hott definition f : Π (X : Type), X → X :=
  λ X, Coproduct.elim (λ H, (merelyBoolNonidAutContr X H).1.1.forward) (λ _, idfun)
                      (lem ∥X ≃ 𝟐∥ Merely.uniq)

  hott proposition lemBoolEqv : inl |ideqv 𝟐| = lem ∥𝟐 ≃ 𝟐∥ Merely.uniq :=
  propEM Merely.uniq _ _

  hott example : f lem 𝟐 ≁ idfun :=
  transport (· ≁ idfun) (ap (Coproduct.elim _ _) (lemBoolEqv lem))
            (merelyBoolNonidAutContr _ _).1.2
end «6.9»

-- ============================================================================
-- Exercise 6.10  (HoTT 6.3: The interval)
--   Show that the map constructed in HoTT's thm:interval-funext is a
--   quasi-inverse to happly, so that an interval type implies the full
--   function extensionality axiom.  (You may have to use the
--   "strong-from-weak-funext" argument, HoTT exercise 4.x.)
--
--   The library derives funext from the interval in HITs/Interval.lean
--   (Interval.funext / Interval.happly) and completes the quasi-inverse in
--   Structures.lean (Theorems.happlyFunext / Theorems.funextHapply /
--   Theorems.full).  Below we re-derive the interval construction and prove
--   the left quasi-inverse direction `happly (intervalFunext p) ~ p`
--   directly from the interval's β-rule (transport in path spaces).
-- ============================================================================

namespace «6.10»
  hott definition intervalFunext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) : f = g :=
  ap (λ i x, Interval.rec (f x) (g x) (p x) i) seg

  -- Transport in a Π-family evaluated at a point.
  -- (A pointwise specialization of the library's `Equiv.transportOverPi`,
  -- which is exactly the `happly (transportOverPi _ _ _) x` pattern that
  -- `Interval.transportOverHmtpy` uses; written out here because the
  -- elaborator needs the index type pinned.)
  hott lemma transportPiAt {I : Type u} {X : Type v} (P : I → X → Type w)
    {a b : I} (p : a = b) (u : Π y, P a y) (x : X) :
    transport (λ a', Π y, P a' y) p u x = transport (λ a', P a' x) p (u x) :=
  begin induction p; reflexivity end

  -- Transport in a path-space family (fixed left endpoint, dependent version).
  hott lemma transportOverFunction' {A : Type u} {B : A → Type v}
    {a : A} (f g : Π x, B x) (p : f = g) (q : f a = f a) :
    transport (λ (f' : Π x, B x) => f a = f' a) p q = q ⬝ ap (λ f', f' a) p :=
  begin induction p; transitivity; reflexivity; symmetry; apply Id.rid end

  hott lemma happlyOfApPt {A : Type u} {B : A → Type v} {f g : Π x, B x} (p : f ~ g) (x : A) :
    ap (λ g, g x) (ap (λ i y, Interval.rec (f y) (g y) (p y) i) seg) =
    ap (λ i, Interval.rec (f x) (g x) (p x) i) seg :=
  begin
    symmetry;
    apply mapOverComp (λ i y, Interval.rec (f y) (g y) (p y) i) (λ h, h x) seg
  end

  hott lemma happlyIntervalFunext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) (x : A) :
    happly (intervalFunext p) x = p x :=
  begin
    unfold intervalFunext happly;
    transitivity; apply transportPiAt (λ (g : Π (x : A), B x) (y : A) => f y = g y)
      (ap (λ i y, Interval.rec (f y) (g y) (p y) i) seg) (Homotopy.id f) x;
    transitivity; apply transportOverFunction' f g
      (ap (λ i y, Interval.rec (f y) (g y) (p y) i) seg) (idp (f x));
    transitivity; apply Id.lid;
    transitivity; apply happlyOfApPt p x;
    apply Interval.recβrule (f x) (g x) (p x)
  end

  -- Completion to a quasi-inverse of happly (as in HoTT 6.10): the full
  -- equivalence (f = g) ≃ (f ~ g) is already in the library
  -- (Theorems.full in Structures.lean, derived from the interval via the
  -- strong-from-weak argument).  For the record:
  hott corollary intervalFunextQuasiInverse {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) : happly (intervalFunext p) ~ p :=
  happlyIntervalFunext p
end «6.10»

-- ============================================================================
-- Exercise 6.11  (HoTT 6.4: Suspensions)
--   Prove the universal property of suspension:
--       (Susp A → B)  ≃  Σ (bₙ : B), Σ (bₛ : B), (A → bₙ = bₛ).
-- ============================================================================

namespace «6.11»
  open GroundZero.HITs.Suspension (north south merid)

  hott definition toLump {A : Type u} {B : Type v} (f : ∑ A → B) :
    Σ (bₙ : B), Σ (bₛ : B), A → bₙ = bₛ :=
  ⟨f north, ⟨f south, λ a, ap f (merid a)⟩⟩

  hott definition fromLump {A : Type u} {B : Type v} (w : Σ (bₙ : B), Σ (bₛ : B), A → bₙ = bₛ) : ∑ A → B :=
  Suspension.rec w.1 w.2.1 w.2.2

  -- Any map from a suspension is determined by its values on the generators.
  hott definition suspMapExt {A : Type u} {B : Type v} (f : ∑ A → B) :
    Suspension.rec (f north) (f south) (λ a, ap f (merid a)) ~ f :=
  begin
    fapply Suspension.ind;
    reflexivity;
    reflexivity;
    intro a; apply Id.trans;
    apply Equiv.transportOverHmtpy; transitivity; apply ap (· ⬝ _);
    transitivity; apply Id.rid; transitivity; apply Id.mapInv;
    apply ap; apply Suspension.recβrule; apply Id.invComp
  end

  hott definition lumpFromTo {A : Type u} {B : Type v} (f : ∑ A → B) : fromLump (toLump f) = f :=
  begin
    apply Interval.funext; intro x; apply suspMapExt f x
  end

  hott definition lumpToFrom {A : Type u} {B : Type v} (w : Σ (bₙ : B), Σ (bₛ : B), A → bₙ = bₛ) :
    toLump (fromLump w) = w :=
  begin
    fapply Sigma.prod;
    reflexivity;
    fapply Sigma.prod;
    reflexivity;
    apply Interval.funext; intro a; apply Suspension.recβrule
  end

  hott theorem suspLump {A : Type u} {B : Type v} :
    (∑ A → B) ≃ (Σ (bₙ : B), Σ (bₛ : B), A → bₙ = bₛ) :=
  Types.Equiv.intro toLump fromLump lumpFromTo lumpToFrom
end «6.11»

-- ============================================================================
-- Exercise 6.12  (HoTT 6.10: The integers)
--   Show that ℤ ≃ ℕ + 𝟏 + ℕ.  Show that if we were to define ℤ as
--   ℕ + 𝟏 + ℕ, then we could obtain the sign-induction principle with
--   judgmental computation rules.
--
--   The library's Types.Integer is the signed integers ℕ + ℕ (pos/neg, with
--   neg 0 = −1), which is ℕ + 𝟏 + ℕ up to the shift in the first summand.
--   (The sign-induction with its β-rules is Integer.indsp/recsp in
--   Types/Integer.lean.)
-- ============================================================================

namespace «6.12»
  hott definition altF : Integer → (ℕ + 𝟏) + ℕ
  | inl Nat.zero        => inl (inr ★)
  | inl (Nat.succ n)    => inl (inl n)
  | inr m               => inr m

  hott definition altG : (ℕ + 𝟏) + ℕ → Integer
  | inl (inl n)   => Integer.pos (Nat.succ n)
  | inl (inr ★)   => Integer.pos Nat.zero
  | inr m         => Integer.neg m

  hott definition altGF : Π x, altG (altF x) = x
  | inl Nat.zero     => Id.refl
  | inl (Nat.succ n) => Id.refl
  | inr m            => Id.refl

  hott definition altFG : Π y, altF (altG y) = y
  | inl (inl n)   => Id.refl
  | inl (inr ★)   => Id.refl
  | inr m         => Id.refl

  hott theorem altIntegers : Integer ≃ (ℕ + 𝟏) + ℕ :=
  Types.Equiv.intro altF altG altGF altFG
end «6.12»
