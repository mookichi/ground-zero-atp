import GroundZero.Algebra.Ring
import GroundZero.Theorems.Nat
import GroundZero.Theorems.Classical

open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Types.Equiv (transport)
open GroundZero.Proto (explode)
open GroundZero.Theorems
open GroundZero.HITs

namespace GroundZero.Algebra
universe u

/-
  Euclidean domain structure for HoTT (Ground Zero style).

  Design (following the classical definition):
  * the primary datum is an *evaluation function* δ : R → ℕ
    (a Euclidean function / norm), rather than a well-founded relation;
  * division comes as a dependent elimination: any a can be written as
    a = q·b + r with b proper, and the remainder r is either zero or has
    δ r < δ b.  Since δ maps into ℕ and ℕ is well-founded by construction,
    termination of the Euclidean algorithm is inherited from ℕ's well-founded
    order (no separate well-founded relation or W-type encoding is needed);
  * in HoTT, structure projections are transparent (hott definitions and
    abbreviations are reducible), so the elaborator-layer issues that plague
    opaque class fields in ordinary dependent type theories do not arise:
    δ and the division witness reduce definitionally where needed;
  * the classical proof of the existence of a greatest common divisor
    (GroundZero.Algebra.Euclidean.gcd below) is formalized by course-of-values
    recursion on δ b, which is what the δ-based "constructive Euclid structure"
    provides for free.

  A "well-founded relation only" variant (for rings where no constructive
  δ exists) would be expressed via accessibility of the relation, which in
  this library can be encoded through W-types (GroundZero.Types.W).  That
  fallback is deliberately not included here: the δ-based formulation is the
  primary interface, and all classical examples (ℤ with |·|, F[x] with deg)
  admit a constructive δ.
-/

/--
  A Euclidean domain: a commutative ring with a Euclidean function
  δ : R → ℕ and a division algorithm producing a quotient/remainder
  decomposition with the remainder smaller (or zero) in δ.

  The class itself is constructive: δ and the division witness are plain
  data (no choice principles involved).  δmul (multiplicativity of the
  Euclidean function) is part of the classical definition and is kept for
  completeness; the gcd existence proof below only needs δ and div.
-/
class Euclidean (T : Prering) extends ring T, ring.monoid T, ring.assoc T, ring.comm T :=
(δ    : T.carrier → ℕ)
(δmul : Π a b, T.isproper a → T.isproper b → δ a ≤ δ (a * b))
(div  : Π (a b : T.carrier), T.isproper b →
          Σ (q r : T.carrier), (a = q * b + r) × ((r = 0) + (δ r + 1 ≤ δ b)))

namespace Euclidean
  variable {T : Prering} [E : Euclidean T]

  /-- Divisibility: dvd a b  iff  ∃ q, b = q · a.
      Written as `dvd a b` (not `a | b`): the `|` infix notation clashes
      with the equation-clause syntax of the hott parser in binder-heavy
      types such as `Π c, c | a → c | b → c | d`. -/
  hott definition dvd (a b : T.carrier) : Type := Σ q, b = q * a

  hott definition dvd.refl (a : T.carrier) : dvd a a :=
  ⟨1, Id.symm (ring.monoid.oneMul a)⟩

  hott definition dvd.zero (a : T.carrier) : dvd a 0 :=
  ⟨0, Id.symm (ring.zeroMul a)⟩

  hott definition dvd.mulLeft {a b : T.carrier} (p : dvd a b) (c : T.carrier) : dvd a (c * b) :=
  ⟨c * p.1, calc c * b = c * (p.1 * a) : ap (T.ψ c) p.2,
                    = (c * p.1) * a   : Id.symm (ring.assoc.mulAssoc c p.1 a)⟩

  hott definition dvd.neg {a b : T.carrier} (p : dvd a b) : dvd a (-b) :=
  ⟨-p.1, calc -b = -(p.1 * a) : ap T.neg p.2,
                = (-p.1) * a   : Id.symm (ring.negMul p.1 a)⟩

  hott definition dvd.add {a b c : T.carrier} (p : dvd a b) (q : dvd a c) : dvd a (b + c) :=
  ⟨p.1 + q.1, calc b + c = b + (q.1 * a)      : ap (T.φ b) q.2,
                      = (p.1 * a) + (q.1 * a) : ap (T.φ · (q.1 * a)) p.2,
                      = (p.1 + q.1) * a       : Id.symm (T.distribRight p.1 q.1 a)⟩

  hott definition dvd.sub {a b c : T.carrier} (p : dvd a b) (q : dvd a c) : dvd a (b - c) :=
  dvd.add p (dvd.neg q)

  hott definition dvd.trans {a b c : T.carrier} (p : dvd a b) (q : dvd b c) : dvd a c :=
  ⟨q.1 * p.1, calc c = q.1 * b       : q.2,
                = q.1 * (p.1 * a)   : ap (T.ψ q.1) p.2,
                = (q.1 * p.1) * a   : Id.symm (ring.assoc.mulAssoc q.1 p.1 a)⟩

  /-- (x + y) - x = y: adding then subtracting x cancels. -/
  hott lemma addSubLeft (x y : T.carrier) : (x + y) - x = y :=
  calc (x + y) - x = (x + y) + (-x) : Id.refl,
                  = x + (y + (-x)) : T.addAssoc x y (-x),
                  = x + ((-x) + y) : ap (T.φ x) (T.addComm y (-x)),
                  = (x + (-x)) + y : Id.inv (T.addAssoc x (-x) y),
                  = 0 + y : ap (T.φ · y) (T.addComm x (-x) ⬝ T.addLeftNeg x),
                  = y : T.zeroAdd y

  /-- From a = q·b + r we get r = a - q·b. -/
  hott lemma divEq (a b q r : T.carrier) (H : a = q * b + r) : r = a - q * b :=
  calc r = (q * b + r) - q * b : Id.inv (addSubLeft (q * b) r),
       = a - q * b : ap (λ z, z - q * b) (Id.inv H)

  /-- Course-of-values recursion on ℕ (strong induction / complete induction),
      implemented via Nat.rec (structural recursion on ℕ): to compute P n one
      may use P m for every m + 1 ≤ n.  This is generic ℕ machinery (no ring
      data is involved) — the Euclidean instance only supplies the ambient
      context here. -/
  hott definition strongRecAux (P : ℕ → Type u)
    (step : Π (n : ℕ), (Π (m : ℕ), m + 1 ≤ n → P m) → P n) :
    Π (n : ℕ), Π (m : ℕ), m ≤ n → P m :=
  Nat.rec (λ m h, transport P (Id.symm (Nat.max.zero m h))
      (step 0 (λ k lt, explode (Nat.le.empty 0 k (Nat.max.zeroLeft k) lt))))
    (λ n ih m h,
      match Nat.natDecEq m (n + 1) with
      | Sum.inl q => transport P (Id.symm q) (step (n + 1) (λ k lt, ih k (Nat.le.inj k n lt)))
      | Sum.inr q => ih m (Nat.le.neqSucc q h))

  hott definition strongRec (P : ℕ → Type u)
    (step : Π (n : ℕ), (Π (m : ℕ), m + 1 ≤ n → P m) → P n) : Π (n : ℕ), P n :=
  λ n, strongRecAux P step n n (Nat.max.refl n)

  /-- Existence of a greatest common divisor: for any a, b there is d with
      d | a, d | b and every common divisor of a and b divides d.
      This follows the classical Euclidean algorithm by course-of-values
      recursion on the Euclidean measure δ of the second argument: the
      division algorithm gives a = q·b + r with δ r < δ b (or r = 0),
      so the pair (b, r) is strictly smaller in δ.

      Note: the split on `b = 0` uses Classical.lem, so gcd is a classical
      construction (the class itself stays constructive). -/
  hott definition gcd (a b : T.carrier) :
    Σ d, (dvd d a) × (dvd d b) × (Π c, dvd c a → dvd c b → dvd c d) :=
  strongRec
    (λ n, Π (a b : T.carrier), E.δ b = n → Σ d, (dvd d a) × (dvd d b) × (Π c, dvd c a → dvd c b → dvd c d))
    (λ n ih a b hb,
      match Classical.lem (Alg.hset T b 0) with
      | Sum.inl z =>
          transport (λ x, Σ d, (dvd d a) × (dvd d x) × (Π c, dvd c a → dvd c x → dvd c d))
            (Id.symm z) ⟨a, ⟨dvd.refl a, ⟨dvd.zero a, λ c ca cz, ca⟩⟩⟩
      | Sum.inr nz =>
          let pb : T.isproper b := nz;
          match E.div a b pb with
          | ⟨q, r, decomp, rem⟩ =>
              match rem with
              | Sum.inl rz =>
                  ⟨b, ⟨⟨q, decomp ⬝ ap (T.φ (T.ψ q b)) rz ⬝ T.addZero (T.ψ q b)⟩,
                      ⟨dvd.refl b, λ c ca cb, cb⟩⟩⟩
              | Sum.inr lt =>
                  let ⟨d, db, dr, mx⟩ :=
                    ih (E.δ r) (transport (λ z, E.δ r + 1 ≤ z) hb lt) b r (Id.idp (E.δ r));
                  ⟨d, ⟨transport (dvd d ·) (Id.symm decomp) (dvd.add (dvd.mulLeft db q) dr),
                       ⟨db, λ c ca cb, mx c cb
                         (transport (dvd c ·) (Id.inv (divEq a b q r decomp)) (dvd.sub ca (dvd.mulLeft cb q)))⟩⟩⟩)
    (E.δ b) a b (Id.idp (E.δ b))
end Euclidean

end GroundZero.Algebra
