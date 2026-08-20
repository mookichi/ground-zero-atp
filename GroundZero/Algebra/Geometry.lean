import GroundZero.Algebra.Basic

open GroundZero.Structures (prop propset contr)
open GroundZero.Types GroundZero.Proto
open GroundZero.HITs
open GroundZero.Types

namespace GroundZero.Algebra
  universe u v

  hott def Pregeometry : Type (max u v + 1) :=
  @Alg.{0, 0, u, v} 𝟎 𝟐 (Coproduct.elim explode (Bool.rec 3 4))

  namespace Pregeometry
    hott def between (G : Pregeometry) (a b c : G.carrier) :=
    (G.rel false (a, b, c, ★)).1

    hott def congruent (G : Pregeometry) (a b c d : G.carrier) :=
    (G.rel true (a, b, c, d, ★)).1

    hott def prop₁ (G : Pregeometry) {a b c : G.carrier} : prop (G.between a b c) :=
    (G.rel false (a, b, c, ★)).2

    hott def prop₂ (G : Pregeometry) {a b c d : G.carrier} : prop (G.congruent a b c d) :=
    (G.rel true (a, b, c, d, ★)).2

    hott def collinear (G : Pregeometry) (a b c : G.carrier) :=
    ∥G.between a b c + G.between c a b + G.between b c a∥

    class geometry (G : Pregeometry) :=
    (refl  : Π a b, G.congruent a b b a)
    (trans : Π a₁ b₁ a₂ b₂ a₃ b₃, G.congruent a₁ b₁ a₂ b₂ → G.congruent a₁ b₁ a₃ b₃ → G.congruent a₂ b₂ a₃ b₃)
    (idp₁  : Π a b c, G.congruent a b c c → a = b)
    (idp₂  : Π a b, G.between a b a → a = b)
    (pasch : Π a b c u v, G.between a u c → G.between b v c → ∥Σ x, G.between u x b × G.between v x a∥)

    class nonlinear (G : Pregeometry) :=
    (lower : ∥Σ a b c, (¬G.between a b c) × (¬G.between b c a) × (¬G.between c a b)∥)

    class planar (G : Pregeometry) :=
    (upper : Π a b c u v, G.congruent a u a v → G.congruent b u b v → G.congruent c u c v → ¬(u = v) → G.collinear a b c)

    class planimetry (G : Pregeometry) extends geometry G, nonlinear G, planar G

    class isotropic (G : Pregeometry) :=
    (construct : Π a b x y, ∥Σ z, G.between x y z × G.congruent y z a b∥)

    class continuous (G : Pregeometry) :=
    (cut (φ ψ : G.carrier → Sort 0) :
      ∥Σ a, Π x y, (φ x) → (ψ y) → G.between a x y∥ →
      ∥Σ b, Π x y, (φ x) → (ψ y) → G.between x b y∥)

    class absolute (G : Pregeometry) extends geometry G, isotropic G :=
    (five : Π x₁ y₁ z₁ u₁ x₂ y₂ z₂ u₂, ¬(x₁ = y₁) → G.between x₁ y₁ z₁ → G.between x₂ y₂ z₂ →
      G.congruent x₁ y₁ x₂ y₂ → G.congruent y₁ z₁ y₂ z₂ →
      G.congruent x₁ u₁ x₂ u₂ → G.congruent y₁ u₁ y₂ u₂ →
      G.congruent z₁ u₁ z₂ u₂)

    hott def segment (G : Pregeometry) (a b : G.carrier) : Ens G.carrier :=
    ⟨λ c, G.between a c b, λ _, G.prop₁⟩

    hott def geodesic (G : Pregeometry) (a b : G.carrier) : Ens.{u, 0} G.carrier :=
    ⟨G.collinear a b, λ _, Merely.uniq⟩

    hott def circle (G : Pregeometry) (a b : G.carrier) : Ens G.carrier :=
    ⟨λ c, G.congruent a b a c, λ _, G.prop₂⟩

    hott def triangle (G : Pregeometry) (a b c : G.carrier) : Ens G.carrier :=
    ⟨λ z, ∥G.between a z b + G.between b z c + G.between a z c∥, λ _, Merely.uniq⟩

    hott def ray (G : Pregeometry) (a b : G.carrier) : Ens G.carrier :=
    ⟨λ c, ∥G.between a c b + G.between a b c∥, λ _, Merely.uniq⟩

    set_option backward.isDefEq.respectTransparency false in
    class euclidean (G : Pregeometry) extends absolute G :=
    (fifth : Π (a₁ b₁ a₂ b₂ a₃ b₃ : G.carrier),
      Ens.parallel (geodesic G a₁ b₁) (geodesic G a₃ b₃) →
      Ens.parallel (geodesic G a₂ b₂) (geodesic G a₃ b₃) →
      Ens.parallel (geodesic G a₁ b₁) (geodesic G a₂ b₂))
  end Pregeometry
end GroundZero.Algebra
