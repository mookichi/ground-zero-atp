import GroundZero.Theorems.Classical
import GroundZero.Algebra.Basic

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.Types
open GroundZero.Proto
open GroundZero

namespace GroundZero.Algebra

universe u

namespace Precategory
  inductive Arity : Type
  | left | right | mul | bottom

  hott definition signature : Arity + ⊥ → ℕ
  | Sum.inl Arity.mul     => 2
  | Sum.inl Arity.left    => 1
  | Sum.inl Arity.right   => 1
  | Sum.inl Arity.bottom  => 0
  | Sum.inr h             => explode h
end Precategory

hott def Precategory : Type (u + 1) :=
Alg.{0, 0, u, 0} Precategory.signature

namespace Precategory
  hott def intro {α : Type u} (H : hset α) (μ : α → α → α)
    (dom cod : α → α) (bot : α) : Precategory.{u} :=
  ⟨zeroeqv H,
   (λ | Arity.mul     => λ (a, b, _), μ a b
      | Arity.left    => λ (a, _), dom a
      | Arity.right   => λ (a, _), cod a
      | Arity.bottom  => λ _, bot,
    λ z, explode z)⟩

  variable (𝒞 : Precategory.{u})

  hott def bottom : 𝒞.carrier :=
  𝒞.op Arity.bottom ★
  notation "∄" => bottom _

  hott def μ : 𝒞.carrier → 𝒞.carrier → 𝒞.carrier :=
  λ x y, 𝒞.op Arity.mul (x, y, ★)

  hott def dom : 𝒞 →ᴬ 𝒞 :=
  λ x, 𝒞.op Arity.left (x, ★)

  hott def cod : 𝒞 →ᴬ 𝒞 :=
  λ x, 𝒞.op Arity.right (x, ★)

  hott def defined (x : 𝒞.carrier) : Type u := x ≠ ∄
  prefix:70 "∃" => defined _

  hott def id (x : 𝒞.carrier) := x = 𝒞.dom x

  hott def Obj := Σ x, 𝒞.id x × 𝒞.defined x
  hott def Obj.val {𝒞 : Precategory} : Obj 𝒞 → 𝒞.carrier := Sigma.fst

  hott def Hom (a b : 𝒞.carrier) :=
  Σ φ, (𝒞.dom φ = a) × (𝒞.cod φ = b)

  hott def Hom.ap {𝒞 : Precategory} {a b : 𝒞.carrier} : Hom 𝒞 a b → 𝒞.carrier :=
  Sigma.fst

  hott def homext {a b : 𝒞.carrier} (f g : Hom 𝒞 a b) : f.ap = g.ap → f = g :=
  begin intro p; apply Sigma.prod p; apply Structures.productProp <;> apply 𝒞.hset end

  hott def monic (a : 𝒞.carrier) :=
  Π b c, ∃(𝒞.μ a b) → 𝒞.μ a b = 𝒞.μ a c → b = c

  hott def epic (a : 𝒞.carrier) :=
  Π b c, ∃(𝒞.μ b a) → 𝒞.μ b a = 𝒞.μ c a → b = c

  hott def bimorphism (a : 𝒞.carrier) :=
  monic 𝒞 a × epic 𝒞 a

  hott def following (a b : 𝒞.carrier) :=
  𝒞.dom a = 𝒞.cod b

  hott def endo (a : 𝒞.carrier) :=
  𝒞.following a a

  hott def rinv (a b : 𝒞.carrier) :=
  𝒞.μ a b = 𝒞.cod a

  hott def linv (a b : 𝒞.carrier) :=
  𝒞.μ b a = 𝒞.dom a

  hott def biinv (a b : 𝒞.carrier) :=
  linv 𝒞 a b × rinv 𝒞 a b

  hott def biinv.prop {a b : 𝒞.carrier} : prop (biinv 𝒞 a b) :=
  begin fapply Structures.productProp <;> apply 𝒞.hset end

  hott def coretraction (a : 𝒞.carrier) :=
  Σ b, linv 𝒞 a b

  hott def retraction (a : 𝒞.carrier) :=
  Σ b, rinv 𝒞 a b

  hott def iso (a : 𝒞.carrier) :=
  Σ b, biinv 𝒞 a b

  hott def invertible (a : 𝒞.carrier) :=
  ∥𝒞.iso a∥

  hott def Iso (a b : Obj 𝒞) :=
  Σ (f : Hom 𝒞 a.val b.val), 𝒞.invertible f.ap

  hott def univalent (𝒞 : Precategory) :=
  Π a, 𝒞.endo a ≃ 𝒞.invertible a

  hott def groupoid (𝒞 : Precategory) :=
  Π a, 𝒞.invertible a

  hott def commutative (𝒞 : Precategory) :=
  Π a b, 𝒞.dom a = 𝒞.dom b → 𝒞.cod a = 𝒞.cod b → a = b

  hott def auto (a : 𝒞.carrier) :=
  endo 𝒞 a × iso 𝒞 a

  hott def op : Precategory :=
  intro 𝒞.hset (λ a b, 𝒞.μ b a) 𝒞.cod 𝒞.dom ∄
  postfix:max "ᵒᵖ" => op

  -- Homomoprhism of algebras is a functor here
  variable (𝒟 : Precategory) (f : Algebra.Hom 𝒞 𝒟)

  hott def functorComp :
    Π a b, f.ap (𝒞.μ a b) = 𝒟.μ (f.ap a) (f.ap b) :=
  λ a b, f.2.1 Arity.mul (a, b, ★)

  hott def functorDom : Π a, f.ap (𝒞.dom a) = 𝒟.dom (f.ap a) :=
  λ a, f.2.1 Arity.left (a, ★)

  hott def functorCod : Π a, f.ap (𝒞.cod a) = 𝒟.cod (f.ap a) :=
  λ a, f.2.1 Arity.right (a, ★)

  hott def functorBottom : f.ap ∄ = ∄ :=
  f.2.1 Arity.bottom ★
end Precategory

/-
  MacLane, S.: Categories for the Working Mathematician. Springer-Verlag, New York (1971).
  Similar axioms can be found in XII. 5. Single-Set Categories.
-/

class category (𝒞 : Precategory) :=
(defDec      : Π (a : 𝒞.carrier), dec (a = ∄))
(bottomLeft  : Π a, 𝒞.μ ∄ a = ∄)
(bottomRight : Π a, 𝒞.μ a ∄ = ∄)
(bottomDom   : 𝒞.dom ∄ = ∄)
(bottomCod   : 𝒞.cod ∄ = ∄)
(domComp     : Π a, 𝒞.μ a (𝒞.dom a) = a)
(codComp     : Π a, 𝒞.μ (𝒞.cod a) a = a)
(mulDom      : Π a b, ∃(𝒞.μ a b) → 𝒞.dom (𝒞.μ a b) = 𝒞.dom b)
(mulCod      : Π a b, ∃(𝒞.μ a b) → 𝒞.cod (𝒞.μ a b) = 𝒞.cod a)
(domCod      : 𝒞.dom ∘ 𝒞.cod ~ 𝒞.cod)
(codDom      : 𝒞.cod ∘ 𝒞.dom ~ 𝒞.dom)
(mulAssoc    : Π a b c, 𝒞.μ (𝒞.μ a b) c = 𝒞.μ a (𝒞.μ b c))
(mulDef      : Π a b, ∃a → ∃b → (∃(𝒞.μ a b) ↔ 𝒞.following a b))

namespace Category
  open Precategory (Obj Hom)
  open category

  variable {𝒞 : Precategory} [category 𝒞]

  hott def domDom : 𝒞.dom ∘ 𝒞.dom ~ 𝒞.dom :=
  begin
    intro x; match defDec x with
    | Sum.inl p => _ | Sum.inr q => _;
      { transitivity; apply ap; exact p;
        transitivity; apply ap 𝒞.dom; apply bottomDom;
        apply ap; symmetry; assumption };
      { symmetry; transitivity; apply ap 𝒞.dom;
        symmetry; apply domComp; apply mulDom;
        apply transport 𝒞.defined (domComp x)⁻¹ q }
  end

  hott def codCod : 𝒞.cod ∘ 𝒞.cod ~ 𝒞.cod :=
  begin
    intro x; match defDec x with
    | Sum.inl p => _ | Sum.inr q => _;
    { transitivity; apply ap; exact p;
      transitivity; apply ap 𝒞.cod; apply bottomCod;
      apply ap; symmetry; assumption };
    { symmetry; transitivity; apply ap 𝒞.cod;
      symmetry; apply codComp; apply mulCod;
      apply transport 𝒞.defined (codComp x)⁻¹ q }
  end

  hott def codMulCod : Π a, 𝒞.μ (𝒞.cod a) (𝒞.cod a) = 𝒞.cod a :=
  begin
    intro a; transitivity; apply ap (𝒞.μ · (𝒞.cod a));
    symmetry; apply codCod; apply codComp
  end

  hott def domMulDom : Π a, 𝒞.μ (𝒞.dom a) (𝒞.dom a) = 𝒞.dom a :=
  begin
    intro a; transitivity; apply ap (𝒞.μ (𝒞.dom a));
    symmetry; apply domDom; apply domComp
  end

  hott def undefDomImplUndef {a : 𝒞.carrier} : 𝒞.dom a = ∄ → a = ∄ :=
  begin
    intro p; transitivity; apply (domComp a)⁻¹;
    transitivity; apply ap (𝒞.μ a) p; apply bottomRight
  end

  hott def undefCodImplUndef {a : 𝒞.carrier} : 𝒞.cod a = ∄ → a = ∄ :=
  begin
    intro p; transitivity; apply (codComp a)⁻¹;
    transitivity; apply ap (𝒞.μ · a) p; apply bottomLeft
  end

  hott def defImplDomDef {a : 𝒞.carrier} : ∃a → ∃(𝒞.dom a) :=
  Classical.Contrapos.intro undefDomImplUndef

  hott def defImplCodDef {a : 𝒞.carrier} : ∃a → ∃(𝒞.cod a) :=
  Classical.Contrapos.intro undefCodImplUndef

  hott def domDefImplDef {a : 𝒞.carrier} : ∃(𝒞.dom a) → ∃a :=
  begin
    apply Classical.Contrapos.intro; intro p;
    transitivity; apply ap 𝒞.dom p; apply bottomDom
  end

  hott def codDefImplDef {a : 𝒞.carrier} : ∃(𝒞.cod a) → ∃a :=
  begin
    apply Classical.Contrapos.intro; intro p;
    transitivity; apply ap 𝒞.cod p; apply bottomCod
  end

  hott def codDefImplDomDef {a : 𝒞.carrier} : ∃(𝒞.cod a) → ∃(𝒞.dom a) :=
  defImplDomDef ∘ codDefImplDef

  hott def domDefImplCodDef {a : 𝒞.carrier} : ∃(𝒞.dom a) → ∃(𝒞.cod a) :=
  defImplCodDef ∘ domDefImplDef

  hott def idMulId {a : 𝒞.carrier} : 𝒞.id a → 𝒞.μ a a = a :=
  λ p, @transport _ (λ x, 𝒞.μ x x = x) (𝒞.dom a) a p⁻¹ (domMulDom a)

  hott def domEndo : Π a, 𝒞.endo (𝒞.dom a) :=
  λ x, (domDom x) ⬝ (codDom x)⁻¹

  hott def codEndo : Π a, 𝒞.endo (𝒞.cod a) :=
  λ x, (domCod x) ⬝ (codCod x)⁻¹

  hott def idEndo (a : 𝒞.carrier) : 𝒞.id a → 𝒞.endo a :=
  begin
    intro p; change _ = _; symmetry; transitivity;
    apply ap; exact p; apply codDom
  end

  hott def following.domImplTotal {f g : 𝒞.carrier} :
    𝒞.following (𝒞.dom f) g → 𝒞.following f g :=
  λ p, (domDom f)⁻¹ ⬝ p

  hott def following.codImplTotal {f g : 𝒞.carrier} :
    𝒞.following f (𝒞.cod g) → 𝒞.following f g :=
  λ p, p ⬝ codCod g

  hott def following.compLeft {f g h : 𝒞.carrier} :
    ∃(𝒞.μ f g) → 𝒞.following g h → 𝒞.following (𝒞.μ f g) h :=
  begin intros p q; apply Id.trans; apply mulDom f g p; exact q end

  hott def following.compRight {f g h : 𝒞.carrier} :
    ∃(𝒞.μ g h) → 𝒞.following f g → 𝒞.following f (𝒞.μ g h) :=
  begin intros p q; apply Id.trans; exact q; exact (mulCod g h p)⁻¹ end

  hott def idIffEqCod (a : 𝒞.carrier) : 𝒞.id a ↔ (a = 𝒞.cod a) :=
  begin
    apply Prod.mk; { intro p; transitivity; exact p; apply idEndo a p };
    { intro p; change _ = _; transitivity; exact p; symmetry;
      transitivity; apply ap; exact p; apply domCod }
  end

  hott def mulDefImplLeftDef {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → ∃a :=
  begin
    apply Classical.Contrapos.intro; intro p; transitivity;
    apply ap (𝒞.μ · b); exact p; apply bottomLeft
  end

  hott def mulDefImplRightDef {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → ∃b :=
  begin
    apply Classical.Contrapos.intro; intro p; transitivity;
    apply ap (𝒞.μ a); exact p; apply bottomRight
  end

  hott def defImplFollowing {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → 𝒞.following a b :=
  begin
    intro p; fapply (mulDef a b _ _).left;
    exact p; apply mulDefImplLeftDef p;
    apply mulDefImplRightDef p
  end

  hott def domCompDefImplDef {a b : 𝒞.carrier} : ∃(𝒞.μ (𝒞.dom a) b) → ∃(𝒞.μ a b) :=
  begin
    intro p; fapply (mulDef a b _ _).right;
    apply following.domImplTotal;
    apply defImplFollowing; exact p;
    apply domDefImplDef;
    apply mulDefImplLeftDef p;
    apply mulDefImplRightDef p
  end

  hott def codCompDefImplDef {a b : 𝒞.carrier} : ∃(𝒞.μ a (𝒞.cod b)) → ∃(𝒞.μ a b) :=
  begin
    intro p; fapply (mulDef a b _ _).right;
    apply following.codImplTotal;
    apply defImplFollowing; exact p;
    apply mulDefImplLeftDef p;
    apply codDefImplDef;
    apply mulDefImplRightDef p
  end

  hott def defImplDomCompDef {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → ∃(𝒞.μ (𝒞.dom a) b) :=
  begin
    intro p; fapply (mulDef (𝒞.dom a) b _ _).right;
    apply Id.trans; apply domDom; apply defImplFollowing p;
    apply defImplDomDef; apply mulDefImplLeftDef p;
    apply mulDefImplRightDef p
  end

  hott def defImplCodCompDef {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → ∃(𝒞.μ a (𝒞.cod b)) :=
  begin
    intro p; fapply (mulDef a (𝒞.cod b) _ _).right;
    apply Id.trans; apply defImplFollowing p;
    symmetry; apply codCod; apply mulDefImplLeftDef p;
    apply defImplCodDef; apply mulDefImplRightDef p
  end

  hott def domHeteroComp {a b : 𝒞.carrier} : ∃(𝒞.μ (𝒞.dom a) b) → 𝒞.μ (𝒞.dom a) b = b :=
  begin
    intro p; transitivity; apply ap (𝒞.μ · b);
    transitivity; apply (domDom a)⁻¹;
    apply defImplFollowing p; apply codComp
  end

  hott def codHeteroComp {a b : 𝒞.carrier} : ∃(𝒞.μ a (𝒞.cod b)) → 𝒞.μ a (𝒞.cod b) = a :=
  begin
    intro p; transitivity; apply ap (𝒞.μ a);
    transitivity; apply (codCod b)⁻¹;
    symmetry; apply defImplFollowing p; apply domComp
  end

  hott def idComp {a b : 𝒞.carrier} : ∃(𝒞.μ a b) → 𝒞.id a → 𝒞.μ a b = b :=
  begin
    intros p q; transitivity; apply ap (𝒞.μ · b);
    exact q; apply domHeteroComp; apply defImplDomCompDef p
  end

  hott def coretractionImplMonic {a : 𝒞.carrier} : 𝒞.coretraction a → 𝒞.monic a :=
  begin
    intro ⟨b, p⟩ x y q r; transitivity; symmetry;
    apply domHeteroComp (defImplDomCompDef q);
    symmetry; transitivity; symmetry; apply domHeteroComp;
    apply defImplDomCompDef; apply transport 𝒞.defined r q;
    apply transport (λ z, 𝒞.μ z y = 𝒞.μ z x); exact p;
    transitivity; apply mulAssoc; symmetry;
    transitivity; apply mulAssoc; apply ap; exact r
  end

  hott def retractionImplEpic {a : 𝒞.carrier} : 𝒞.retraction a → 𝒞.epic a :=
  begin
    intro ⟨b, p⟩ x y q r; transitivity; symmetry;
    apply codHeteroComp (defImplCodCompDef q);
    symmetry; transitivity; symmetry; apply codHeteroComp;
    apply defImplCodCompDef; apply transport 𝒞.defined r q;
    apply transport (λ z, 𝒞.μ y z = 𝒞.μ x z); exact p;
    transitivity; symmetry; apply mulAssoc;
    transitivity; apply ap (𝒞.μ · b);
    exact Id.inv r; apply mulAssoc
  end

  @[reducible]
  hott def dual (𝒞 : Precategory) (η : category 𝒞) : category 𝒞ᵒᵖ :=
  { defDec      := @defDec 𝒞 η,
    bottomLeft  := @bottomRight 𝒞 η,
    bottomRight := @bottomLeft 𝒞 η,
    bottomDom   := @bottomCod 𝒞 η,
    bottomCod   := @bottomDom 𝒞 η,
    domComp     := @codComp 𝒞 η,
    codComp     := @domComp 𝒞 η,
    mulDom      := λ _ _ δ, @mulCod 𝒞 η _ _ δ,
    mulCod      := λ _ _ δ, @mulDom 𝒞 η _ _ δ,
    domCod      := @codDom 𝒞 η,
    codDom      := @domCod 𝒞 η,
    mulAssoc    := λ _ _ _, (@mulAssoc 𝒞 η _ _ _)⁻¹,
    mulDef      := λ a b α β, Iff.comp (@mulDef 𝒞 η b a β α) (Id.inv, Id.inv) }

  @[reducible]
  hott instance (𝒞 : Precategory) [η : category 𝒞] : category 𝒞ᵒᵖ := dual 𝒞 η

  /-
    https://ncatlab.org/nlab/show/natural+transformation
    “In terms of morphismwise components”

    “Categories for the Working Mathematician”
    I. 4. Natural Transformations. Exercise 5.
  -/
  hott def Natural {𝒜 ℬ : Precategory} (F G : Algebra.Hom 𝒜 ℬ) :=
  Σ (μ : 𝒜.carrier → ℬ.carrier), Π f g, 𝒜.following f g →
    ℬ.μ (μ f) (F.ap g) = ℬ.μ (G.ap f) (μ g)

  infix:75 " ⟹ " => Natural

  hott def id {𝒜 ℬ : Precategory} {F : Algebra.Hom 𝒜 ℬ} : F ⟹ F :=
  ⟨F.ap, λ _ _ _, Id.refl⟩

  hott def Natural.happly {𝒜 ℬ : Precategory} {F G : Algebra.Hom 𝒜 ℬ}
    {μ η : F ⟹ G} (p : μ = η) : μ.1 ~ η.1 :=
  begin induction p; reflexivity end

  hott def Natural.funext {𝒜 ℬ : Precategory} {F G : Algebra.Hom 𝒜 ℬ}
    {μ η : F ⟹ G} (p : μ.1 ~ η.1) : μ = η :=
  begin
    fapply Sigma.prod; apply Theorems.funext; exact p;
    apply Structures.piProp; intro;
    apply Structures.piProp; intro;
    apply Structures.piProp; intro;
    apply ℬ.hset
  end

  hott def bottomBiinv : 𝒞.biinv ∄ ∄ :=
  begin
    apply Prod.mk <;> change _ = _ <;> transitivity;
    apply bottomLeft; apply Id.inv bottomDom;
    apply bottomLeft; apply Id.inv bottomCod
  end

  section
    variable {a b c : Obj 𝒞}

    hott def homDefined (f : 𝒞.Hom a.val b.val) : ∃f.ap :=
    begin
      apply domDefImplDef; apply Equiv.transport 𝒞.defined;
      symmetry; exact f.2.1; apply a.2.2
    end

    hott def homCompDefined (f : 𝒞.Hom b.val c.val) (g : 𝒞.Hom a.val b.val) : ∃(𝒞.μ f.ap g.ap) :=
    begin
      apply (mulDef f.ap g.ap _ _).right;
      { change _ = _; transitivity; exact f.2.1;
        symmetry; exact g.2.2 };
      repeat { apply homDefined }
    end

    hott def comp (f : 𝒞.Hom b.val c.val) (g : 𝒞.Hom a.val b.val) : 𝒞.Hom a.val c.val :=
    begin
      existsi 𝒞.μ f.ap g.ap; apply Prod.mk;
      transitivity; apply mulDom; apply homCompDefined; apply g.2.1;
      transitivity; apply mulCod; apply homCompDefined; apply f.2.2
    end
  end

  hott def ε (a : Obj 𝒞) : 𝒞.Hom a.val a.val :=
  begin
    existsi a.val; apply Prod.mk <;> symmetry;
    apply a.2.1; apply (idIffEqCod _).left; exact a.2.1
  end

  local infix:60 " ∘ " => comp

  hott def leftε {a b : Obj 𝒞} (f : 𝒞.Hom a.val b.val) : ε b ∘ f = f :=
  begin
    apply 𝒞.homext; transitivity; apply ap (𝒞.μ · f.ap);
    symmetry; apply f.2.2; apply codComp
  end

  hott def rightε {a b : Obj 𝒞} (f : 𝒞.Hom a.val b.val) : f ∘ ε a = f :=
  begin
    apply 𝒞.homext; transitivity; apply ap (𝒞.μ f.ap);
    symmetry; apply f.2.1; apply domComp
  end

  hott def compAssoc {a b c d : Obj 𝒞} (f : 𝒞.Hom c.val d.val)
    (g : 𝒞.Hom b.val c.val) (h : 𝒞.Hom a.val b.val) : (f ∘ g) ∘ h = f ∘ (g ∘ h) :=
  begin apply 𝒞.homext; apply mulAssoc end
end Category

end GroundZero.Algebra
