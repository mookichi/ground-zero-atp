import GroundZero
import PosDef

open GroundZero.Algebra
open GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.HITs

namespace KernelUniversal

/-
  ============================================================================
  ガウス RBF の普遍性（universal kernel）の形式化評価
  ============================================================================

  目的: 前回整備した定理（sum 機構: sumMul / sum.ext / sumSwap（有限 Fubini）、
        分配則: prodReorder、exp 公理: expAdd / negAdd / expZero）を使って、
        ガウスカーネル k(x, y) = exp(-ε²·(x-y)²) が「普遍カーネル」
        （Stone–Weierstrass の意味: 連続関数を有限スパンで一様近似できる）
        であることの証明に挑戦する。

  このファイルで完全に形式化するもの（代数的核心）:
    1. 環ツールキット: subSelf / negNeg / sqrNeg / sqrMul / sqrSubSwapped /
       prodReorder / subSub / sumSwap2（x - y = x + (-y) は定義的）
    2. 半減と平行四辺形: twoInvMul / twoInvSqr / half / twoInvTimes /
       sqrAdd2 / sumRearrange / paral（平行四辺形恒等式）→ midGeneric → midSquare
    3. ガウスバンプ bump a c x = exp(-a·(x-c)²) の性質:
       bumpCenter（中心で 1）/ bumpSymm（対称）/ bumpNonneg（非負）
    4. 中点クロージャ bumpProduct:
       bump a c₁ · bump a c₂ = exp(-a·twoInv·(c₁-c₂)²) · bump (2a) ((c₁+c₂)/2)
       （2つのガウスの積は再びガウス。midSquare + expAdd/negAdd のチェーン）
    5. スパンの積閉包 bumpSumMulClosed:
       Σᵢαᵢk(cᵢ) · Σⱼβⱼk(dⱼ) = Σᵢⱼ (αᵢβⱼ·exp(-a·twoInv·(cᵢ-dⱼ)²))·k(2a, mᵢⱼ)
       （sumMul / sum.ext / prodReorder / bumpProduct / mulAssoc のチェーン）
    6. 普遍性の定式化:
       windowApprox: 有界窓 |x| ≤ B 上の一様 δ-近似（コンパクト集合上の SW に対応）
       universalKernel a = ∀B (f : ℝ→ℝ) [連続] δ>0, ∃n α c, 窓 |x|≤B 上の一様 δ-近似
       stoneWeierstrassGauss（実解析の残差をまとめた公理）
       gaussianUniversal: ε > 0 ⇒ universalKernel (ε²)

  分離した公理について: Stone–Weierstrass の密度部分（連続関数空間と sup ノルム、
  点分離 x≠y ⇒ k(x,x)=1≠k(x,y)、定数関数の近似）は実解析（Weierstrass 近似定理）の
  内容であり、本ライブラリの射程外として 1 つの公理にまとめた。代数的核心
  （スパンが乗法で閉じる）は本ファイルで完全に証明されている。
-/

/-========== 環ツールキット（x - y = x + (-y) が定義的） ==========-/

/-- x - x = 0 -/
hott lemma subSelf (x : ℝ) : x - x = 0 :=
calc x - x = x + (-x) : by reflexivity,
     = 0 : @ring.addComm R.τ _ x (-x) ⬝ @ring.addLeftNeg R.τ _ x

/-- -(-x) = x（加法群の逆元の対合性） -/
hott lemma negNeg (x : ℝ) : -(-x) = x :=
by exact R.τ⁺.invInv x

/-- a - (-b) = a + b -/
hott lemma subNegRight (a b : ℝ) : a - (-b) = a + b :=
calc a - (-b) = a + (-(-b)) : by reflexivity,
     = a + b : ap (a + ·) (negNeg b)

/-- a - b = -(b - a) -/
hott lemma subNeg (a b : ℝ) : a - b = -(b - a) :=
calc a - b = a + (-b) : by reflexivity,
     = (-b) + a : @ring.addComm R.τ _ a (-b),
     = (-b) + (-(-a)) : ap ((-b) + ·) (Id.inv (negNeg a)),
     = -(b + (-a)) : Id.inv (negAdd b (-a)),
     = -(b - a) : by reflexivity

/-- sqr 0 = 0 -/
hott lemma sqrZero : PosDef.sqr (0 : ℝ) = 0 :=
calc PosDef.sqr 0 = 0 * 0 : by reflexivity,
     = 0 : @ring.mulZero R.τ _ 0

/-- sqr(-b) = sqr b -/
hott lemma sqrNeg (b : ℝ) : PosDef.sqr (-b) = PosDef.sqr b :=
calc PosDef.sqr (-b) = (-b) * (-b) : by reflexivity,
     = b * b : PosDef.negMulNeg b b,
     = PosDef.sqr b : by reflexivity

/-- sqr (a·b) = sqr a · sqr b -/
hott lemma sqrMul (a b : ℝ) : PosDef.sqr (a * b) = PosDef.sqr a * PosDef.sqr b :=
calc PosDef.sqr (a * b) = (a * b) * (a * b) : by reflexivity,
     = (a * a) * (b * b) :
       @ring.assoc.mulAssoc R.τ _ a b (a * b) ⬝
       ap (a * ·) (Id.inv (@ring.assoc.mulAssoc R.τ _ b a b) ⬝
                     ap (· * b) (@ring.comm.mulComm R.τ _ b a) ⬝
                     @ring.assoc.mulAssoc R.τ _ a b b) ⬝
       Id.inv (@ring.assoc.mulAssoc R.τ _ a a (b * b)),
     = PosDef.sqr a * PosDef.sqr b : by reflexivity

/-- sqr (x - y) = sqr (y - x) -/
hott lemma sqrSubSwapped (x y : ℝ) : PosDef.sqr (x - y) = PosDef.sqr (y - x) :=
ap PosDef.sqr (subNeg x y) ⬝ sqrNeg (y - x)

/-- (a·c)·(b·d) = (a·b)·(c·d) -/
hott lemma prodReorder (a b c d : ℝ) : (a * c) * (b * d) = (a * b) * (c * d) :=
calc (a * c) * (b * d)
     = a * (c * (b * d)) : @ring.assoc.mulAssoc R.τ _ a c (b * d),
     = a * ((c * b) * d) : ap (a * ·) (Id.inv (@ring.assoc.mulAssoc R.τ _ c b d)),
     = a * ((b * c) * d) : ap (λ z, a * (z * d)) (@ring.comm.mulComm R.τ _ c b),
     = a * (b * (c * d)) : ap (a * ·) (@ring.assoc.mulAssoc R.τ _ b c d),
     = (a * b) * (c * d) : Id.inv (@ring.assoc.mulAssoc R.τ _ a b (c * d))

/-- (x - c₁) - (x - c₂) = c₂ - c₁ -/
hott lemma subSub (x c₁ c₂ : ℝ) : (x - c₁) - (x - c₂) = c₂ - c₁ :=
calc (x - c₁) - (x - c₂) = (x + (-c₁)) + (-(x + (-c₂))) : by reflexivity,
     = (x + (-c₁)) + ((-x) + (-(-c₂))) : ap ((x + (-c₁)) + ·) (negAdd x (-c₂)),
     = (x + (-c₁)) + ((-x) + c₂) : ap (λ z, (x + (-c₁)) + ((-x) + z)) (negNeg c₂),
     = ((x + (-c₁)) + (-x)) + c₂ : Id.symm (@ring.addAssoc R.τ _ (x + (-c₁)) (-x) c₂),
     = (x + ((-c₁) + (-x))) + c₂ : ap (· + c₂) (@ring.addAssoc R.τ _ x (-c₁) (-x)),
     = (x + ((-x) + (-c₁))) + c₂ : ap (λ z, (x + z) + c₂) (@ring.addComm R.τ _ (-c₁) (-x)),
     = ((x + (-x)) + (-c₁)) + c₂ : ap (· + c₂) (Id.inv (@ring.addAssoc R.τ _ x (-x) (-c₁))),
     = (0 + (-c₁)) + c₂ : ap (λ z, (z + (-c₁)) + c₂) (@ring.addComm R.τ _ x (-x) ⬝ @ring.addLeftNeg R.τ _ x),
     = (-c₁) + c₂ : ap (· + c₂) (@ring.zeroAdd R.τ _ (-c₁)),
     = c₂ + (-c₁) : @ring.addComm R.τ _ (-c₁) c₂,
     = c₂ - c₁ : by reflexivity

/-- (A+B) + (C+D) = (A+C) + (B+D) -/
hott lemma sumSwap2 (A B C D : ℝ) : (A + B) + (C + D) = (A + C) + (B + D) :=
calc (A + B) + (C + D) = A + (B + (C + D)) : @ring.addAssoc R.τ _ A B (C + D),
     = A + ((B + C) + D) : ap (A + ·) (Id.inv (@ring.addAssoc R.τ _ B C D)),
     = A + ((C + B) + D) : ap (λ z, A + (z + D)) (@ring.addComm R.τ _ B C),
     = A + (C + (B + D)) : ap (A + ·) (@ring.addAssoc R.τ _ C B D),
     = (A + C) + (B + D) : Id.inv (@ring.addAssoc R.τ _ A C (B + D))

/-- x - ((c₁+c₂)·twoInv) = ((x - c₁) + (x - c₂))·twoInv -/
hott lemma midSub (x c₁ c₂ : ℝ) :
  x - ((c₁ + c₂) * PosDef.twoInv) = ((x - c₁) + (x - c₂)) * PosDef.twoInv :=
calc x - ((c₁ + c₂) * PosDef.twoInv)
     = x + (-((c₁ + c₂) * PosDef.twoInv)) : by reflexivity,
     = x + (-(c₁ + c₂)) * PosDef.twoInv :
         ap (x + ·) (Id.inv (@ring.negMul R.τ _ (c₁ + c₂) PosDef.twoInv)),
     = x * 1 + (-(c₁ + c₂)) * PosDef.twoInv :
         ap (· + (-(c₁ + c₂)) * PosDef.twoInv) (Id.inv (@ring.monoid.mulOne R.τ _ x)),
     = x * (PosDef.twoInv + PosDef.twoInv) + (-(c₁ + c₂)) * PosDef.twoInv :
         ap (· + (-(c₁ + c₂)) * PosDef.twoInv) (ap (x * ·) (Id.inv PosDef.twoInvAdd)),
     = (x * PosDef.twoInv + x * PosDef.twoInv) + (-(c₁ + c₂)) * PosDef.twoInv :
         ap (· + (-(c₁ + c₂)) * PosDef.twoInv) (@ring.distribLeft R.τ _ x PosDef.twoInv PosDef.twoInv),
     = (x * PosDef.twoInv + x * PosDef.twoInv) + ((-c₁) * PosDef.twoInv + (-c₂) * PosDef.twoInv) :
         ap ((x * PosDef.twoInv + x * PosDef.twoInv) + ·)
            (ap (· * PosDef.twoInv) (negAdd c₁ c₂) ⬝
             @ring.distribRight R.τ _ (-c₁) (-c₂) PosDef.twoInv),
     = (x * PosDef.twoInv + (-c₁) * PosDef.twoInv) + (x * PosDef.twoInv + (-c₂) * PosDef.twoInv) :
         sumSwap2 (x * PosDef.twoInv) (x * PosDef.twoInv) ((-c₁) * PosDef.twoInv) ((-c₂) * PosDef.twoInv),
     = (x + (-c₁)) * PosDef.twoInv + (x + (-c₂)) * PosDef.twoInv :
         ap (· + (x * PosDef.twoInv + (-c₂) * PosDef.twoInv)) (Id.inv (@ring.distribRight R.τ _ x (-c₁) PosDef.twoInv)) ⬝
         ap ((x + (-c₁)) * PosDef.twoInv + ·) (Id.inv (@ring.distribRight R.τ _ x (-c₂) PosDef.twoInv)),
     = ((x + (-c₁)) + (x + (-c₂))) * PosDef.twoInv :
         Id.inv (@ring.distribRight R.τ _ (x + (-c₁)) (x + (-c₂)) PosDef.twoInv),
     = ((x - c₁) + (x - c₂)) * PosDef.twoInv : by reflexivity

/-========== 2 の逆元と半減・平行四辺形 ==========-/

/-- (1+1)·twoInv = 1 -/
hott lemma twoInvMul : (1 + 1) * PosDef.twoInv = 1 :=
calc (1 + 1) * PosDef.twoInv = PosDef.twoInv + PosDef.twoInv : PosDef.twoMul PosDef.twoInv,
     = 1 : PosDef.twoInvAdd

/-- twoInv·(1+1) = 1 -/
hott lemma twoInvMulComm : PosDef.twoInv * (1 + 1) = 1 :=
calc PosDef.twoInv * (1 + 1) = (1 + 1) * PosDef.twoInv : @ring.comm.mulComm R.τ _ PosDef.twoInv (1 + 1),
     = 1 : twoInvMul

/-- (1+1)·(twoInv·twoInv) = twoInv -/
hott lemma twoInvSqr : (1 + 1) * (PosDef.twoInv * PosDef.twoInv) = PosDef.twoInv :=
calc (1 + 1) * (PosDef.twoInv * PosDef.twoInv)
     = ((1 + 1) * PosDef.twoInv) * PosDef.twoInv : Id.inv (@ring.assoc.mulAssoc R.τ _ (1 + 1) PosDef.twoInv PosDef.twoInv),
     = 1 * PosDef.twoInv : ap (· * PosDef.twoInv) twoInvMul,
     = PosDef.twoInv : @ring.monoid.oneMul R.τ _ PosDef.twoInv

/-- half: (1+1)·s = t なら s = twoInv·t -/
hott lemma half (s t : ℝ) (H : (1 + 1) * s = t) : s = PosDef.twoInv * t :=
calc s = 1 * s : Id.inv (@ring.monoid.oneMul R.τ _ s),
     = (PosDef.twoInv * (1 + 1)) * s : ap (· * s) (Id.inv twoInvMulComm),
     = PosDef.twoInv * ((1 + 1) * s) : @ring.assoc.mulAssoc R.τ _ PosDef.twoInv (1 + 1) s,
     = PosDef.twoInv * t : ap (PosDef.twoInv * ·) H

/-- (1+1)·(A·twoInv²) = twoInv·A -/
hott lemma twoInvTimes (A : ℝ) : (1 + 1) * (A * (PosDef.twoInv * PosDef.twoInv)) = PosDef.twoInv * A :=
calc (1 + 1) * (A * (PosDef.twoInv * PosDef.twoInv))
     = ((1 + 1) * A) * (PosDef.twoInv * PosDef.twoInv) :
         Id.inv (@ring.assoc.mulAssoc R.τ _ (1 + 1) A (PosDef.twoInv * PosDef.twoInv)),
     = (A * (1 + 1)) * (PosDef.twoInv * PosDef.twoInv) : ap (· * (PosDef.twoInv * PosDef.twoInv)) (@ring.comm.mulComm R.τ _ (1 + 1) A),
     = A * ((1 + 1) * (PosDef.twoInv * PosDef.twoInv)) : @ring.assoc.mulAssoc R.τ _ A (1 + 1) (PosDef.twoInv * PosDef.twoInv),
     = A * PosDef.twoInv : ap (A * ·) twoInvSqr,
     = PosDef.twoInv * A : @ring.comm.mulComm R.τ _ A PosDef.twoInv

/-- (u+v)² = u² + 2uv + v² -/
hott lemma sqrAdd2 (u v : ℝ) :
  PosDef.sqr (u + v) = (PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr v :=
calc PosDef.sqr (u + v) = PosDef.sqr (u - (-v)) : ap PosDef.sqr (Id.inv (subNegRight u v)),
     = (PosDef.sqr u + -(((1 + 1) * (u * (-v))))) + PosDef.sqr (-v) : PosDef.distSquare u (-v),
     = (PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr (-v) : ap (· + PosDef.sqr (-v)) (ap (PosDef.sqr u + ·)
          (calc -(((1 + 1) * (u * (-v))))
               = -(((1 + 1) * (-(u * v)))) : ap (λ z, -((1 + 1) * z)) (@ring.mulNeg R.τ _ u v),
               = -(-(((1 + 1) * (u * v)))) : ap (λ z, -z) (@ring.mulNeg R.τ _ (1 + 1) (u * v)),
               = (1 + 1) * (u * v) : negNeg ((1 + 1) * (u * v)))),
     = (PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr v :
         ap (λ (z : ℝ), (PosDef.sqr u + (1 + 1) * (u * v)) + z) (sqrNeg v)

/-- A+B の再配列: ((A+B)+C) + ((A+-B)+C) = (A+A) + (C+C) -/
hott lemma sumRearrange (A B C : ℝ) : ((A + B) + C) + ((A + -B) + C) = (A + A) + (C + C) :=
calc ((A + B) + C) + ((A + -B) + C)
     = (A + B) + (C + ((A + -B) + C)) : @ring.addAssoc R.τ _ (A + B) C ((A + -B) + C),
     = (A + B) + (((A + -B) + C) + C) : ap ((A + B) + ·) (@ring.addComm R.τ _ C ((A + -B) + C)),
     = (A + B) + ((A + -B) + (C + C)) : ap ((A + B) + ·) (@ring.addAssoc R.τ _ (A + -B) C C),
     = ((A + B) + (A + -B)) + (C + C) : Id.inv (@ring.addAssoc R.τ _ (A + B) (A + -B) (C + C)),
     = (A + A) + (C + C) : ap (· + (C + C))
          (calc (A + B) + (A + -B)
               = A + (B + (A + -B)) : @ring.addAssoc R.τ _ A B (A + -B),
               = A + ((B + A) + -B) : ap (A + ·) (Id.inv (@ring.addAssoc R.τ _ B A (-B))),
               = A + ((A + B) + -B) : ap (λ z, A + (z + -B)) (@ring.addComm R.τ _ B A),
               = A + (A + (B + -B)) : ap (A + ·) (@ring.addAssoc R.τ _ A B (-B)),
               = A + (A + 0) : ap (λ z, A + (A + z)) (@ring.addComm R.τ _ B (-B) ⬝ @ring.addLeftNeg R.τ _ B),
               = A + A : ap (A + ·) (R.τ⁺.mulOne A))

/-- 平行四辺形: (u+v)² + (u-v)² = 2(u²+v²) -/
hott lemma paral (u v : ℝ) :
  PosDef.sqr (u + v) + PosDef.sqr (u - v) = (1 + 1) * (PosDef.sqr u + PosDef.sqr v) :=
calc PosDef.sqr (u + v) + PosDef.sqr (u - v)
     = ((PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr v) + PosDef.sqr (u - v) :
         ap (· + PosDef.sqr (u - v)) (sqrAdd2 u v),
     = ((PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr v) +
       ((PosDef.sqr u + -((1 + 1) * (u * v))) + PosDef.sqr v) :
         ap (((PosDef.sqr u + (1 + 1) * (u * v)) + PosDef.sqr v) + ·) (PosDef.distSquare u v),
     = (PosDef.sqr u + PosDef.sqr u) + (PosDef.sqr v + PosDef.sqr v) :
         sumRearrange (PosDef.sqr u) ((1 + 1) * (u * v)) (PosDef.sqr v),
     = (1 + 1) * PosDef.sqr u + (1 + 1) * PosDef.sqr v :
         ap (λ (y : ℝ), (PosDef.sqr u + PosDef.sqr u) + y) (Id.inv (PosDef.twoMul (PosDef.sqr v))) ⬝
         ap (λ (y : ℝ), y + (1 + 1) * PosDef.sqr v) (Id.inv (PosDef.twoMul (PosDef.sqr u))),
     = (1 + 1) * (PosDef.sqr u + PosDef.sqr v) :
         Id.inv (@ring.distribLeft R.τ _ (1 + 1) (PosDef.sqr u) (PosDef.sqr v))

/-- 中点公式（u,v 形）: u² + v² = (u-v)²/2 + 2·((u+v)/2)² -/
hott lemma midGeneric (u v : ℝ) :
  PosDef.sqr u + PosDef.sqr v =
  (PosDef.twoInv * PosDef.sqr (u - v)) + ((1 + 1) * PosDef.sqr ((u + v) * PosDef.twoInv)) :=
calc PosDef.sqr u + PosDef.sqr v
     = PosDef.twoInv * (PosDef.sqr (u + v) + PosDef.sqr (u - v)) :
         half (PosDef.sqr u + PosDef.sqr v) (PosDef.sqr (u + v) + PosDef.sqr (u - v)) (Id.symm (paral u v)),
     = PosDef.twoInv * (PosDef.sqr (u - v) + PosDef.sqr (u + v)) :
         ap (PosDef.twoInv * ·) (@ring.addComm R.τ _ (PosDef.sqr (u + v)) (PosDef.sqr (u - v))),
     = PosDef.twoInv * PosDef.sqr (u - v) + PosDef.twoInv * PosDef.sqr (u + v) :
         @ring.distribLeft R.τ _ PosDef.twoInv (PosDef.sqr (u - v)) (PosDef.sqr (u + v)),
     = PosDef.twoInv * PosDef.sqr (u - v) + (1 + 1) * PosDef.sqr ((u + v) * PosDef.twoInv) :
         ap (PosDef.twoInv * PosDef.sqr (u - v) + ·)
            (calc PosDef.twoInv * PosDef.sqr (u + v)
                 = (1 + 1) * (PosDef.sqr (u + v) * (PosDef.twoInv * PosDef.twoInv)) :
                     Id.symm (twoInvTimes (PosDef.sqr (u + v))),
                 = (1 + 1) * PosDef.sqr ((u + v) * PosDef.twoInv) :
                     ap ((1 + 1) * ·) (Id.symm (sqrMul (u + v) PosDef.twoInv)))

/-- 中点公式（x, c₁, c₂ 形） -/
hott lemma midSquare (x c₁ c₂ : ℝ) :
  PosDef.sqr (x - c₁) + PosDef.sqr (x - c₂) =
  (PosDef.twoInv * PosDef.sqr (c₁ - c₂)) + ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))) :=
calc PosDef.sqr (x - c₁) + PosDef.sqr (x - c₂)
     = (PosDef.twoInv * PosDef.sqr ((x - c₁) - (x - c₂))) +
       ((1 + 1) * PosDef.sqr (((x - c₁) + (x - c₂)) * PosDef.twoInv)) :
         midGeneric (x - c₁) (x - c₂),
     = (PosDef.twoInv * PosDef.sqr (c₁ - c₂)) +
       ((1 + 1) * PosDef.sqr (((x - c₁) + (x - c₂)) * PosDef.twoInv)) :
         ap (λ (y : ℝ), y + ((1 + 1) * PosDef.sqr (((x - c₁) + (x - c₂)) * PosDef.twoInv)))
            (ap (λ (y : ℝ), PosDef.twoInv * y) (ap PosDef.sqr (subSub x c₁ c₂) ⬝ sqrSubSwapped c₂ c₁)),
     = (PosDef.twoInv * PosDef.sqr (c₁ - c₂)) +
       ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))) :
         ap (PosDef.twoInv * PosDef.sqr (c₁ - c₂) + ·)
            (ap (λ z, (1 + 1) * PosDef.sqr z) (Id.symm (midSub x c₁ c₂)))

/-========== ガウスバンプと積閉包 ==========-/

/-- ガウスバンプ: bump a c x = exp(-a·(x-c)²)、a = ε² が幅パラメータ -/
hott definition bump (a c x : ℝ) : ℝ := exp (-(a * PosDef.sqr (x - c)))

/-- 中心で規格化: bump a c c = 1 -/
hott theorem bumpCenter (a c : ℝ) : bump a c c = 1 :=
begin
  unfold bump;
  transitivity; apply ap exp;
    apply ap (λ z, -(a * z)); apply ap PosDef.sqr (subSelf c);
  transitivity; apply ap exp;
    transitivity; apply ap (λ z, -(a * z)); apply sqrZero;
    transitivity; apply ap (λ z, -z); apply @ring.mulZero R.τ _ a;
    symmetry; apply R.zeroEqMinusZero (idp 0);
  apply expZero
end

/-- 対称性: bump a c x = bump a x c -/
hott theorem bumpSymm (a c x : ℝ) : bump a c x = bump a x c :=
by unfold bump; apply ap exp; apply ap (λ z, -(a * z)); exact sqrSubSwapped x c

/-- 非負性: 0 ≤ bump a c x -/
hott theorem bumpNonneg (a c x : ℝ) : R.ρ 0 (bump a c x) :=
by unfold bump; exact PosDef.expNonneg (-(a * PosDef.sqr (x - c)))

/-- 積は再びバンプ（中点クロージャ）:
   bump a c₁ · bump a c₂ = γ · bump (2a) m,  γ = exp(-a·twoInv·(c₁-c₂)²), m = (c₁+c₂)/2 -/
hott theorem bumpProduct (a c₁ c₂ x : ℝ) :
  bump a c₁ x * bump a c₂ x =
  exp (-(a * PosDef.twoInv * PosDef.sqr (c₁ - c₂))) * bump ((1 + 1) * a) ((c₁ + c₂) * PosDef.twoInv) x :=
calc bump a c₁ x * bump a c₂ x
     = exp (-(a * PosDef.sqr (x - c₁))) * exp (-(a * PosDef.sqr (x - c₂))) :
         by unfold bump; reflexivity,
     = exp (-(a * PosDef.sqr (x - c₁)) + -(a * PosDef.sqr (x - c₂))) :
         Id.symm (expAdd (-(a * PosDef.sqr (x - c₁))) (-(a * PosDef.sqr (x - c₂)))),
     = exp (-(a * PosDef.sqr (x - c₁) + a * PosDef.sqr (x - c₂))) :
         ap exp (Id.inv (negAdd (a * PosDef.sqr (x - c₁)) (a * PosDef.sqr (x - c₂)))),
     = exp (-(a * (PosDef.sqr (x - c₁) + PosDef.sqr (x - c₂)))) :
         ap exp (ap (λ z, -z) (Id.inv (@ring.distribLeft R.τ _ a (PosDef.sqr (x - c₁)) (PosDef.sqr (x - c₂))))),
     = exp (-(a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂) + (1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))) :
         ap exp (ap (λ z, -(a * z)) (midSquare x c₁ c₂)),
     = exp (-(a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂)) + a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))) :
         ap exp (ap (λ z, -z) (@ring.distribLeft R.τ _ a (PosDef.twoInv * PosDef.sqr (c₁ - c₂)) ((1 + 1 : ℝ) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))),
     = exp (-(a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂))) + -(a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))) :
         ap exp (negAdd (a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂))) (a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))),
     = exp (-(a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂)))) * exp (-(a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))) :
         expAdd (-(a * (PosDef.twoInv * PosDef.sqr (c₁ - c₂)))) (-(a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))),
     = exp (-((a * PosDef.twoInv) * PosDef.sqr (c₁ - c₂))) * exp (-(a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))) :
         ap (· * exp (-(a * ((1 + 1) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv))))))
            (ap exp (ap (λ z, -z) (Id.inv (@ring.assoc.mulAssoc R.τ _ a PosDef.twoInv (PosDef.sqr (c₁ - c₂)))))),
     = exp (-((a * PosDef.twoInv) * PosDef.sqr (c₁ - c₂))) * exp (-(((1 + 1) * a) * PosDef.sqr (x - ((c₁ + c₂) * PosDef.twoInv)))) :
         ap (λ (y : ℝ), exp (-((a * PosDef.twoInv) * PosDef.sqr (c₁ - c₂))) * y)
            (ap exp (ap (λ z, -z) (PosDef.cScale a (x - ((c₁ + c₂) * PosDef.twoInv)) (x - ((c₁ + c₂) * PosDef.twoInv))))),
     = exp (-(a * PosDef.twoInv * PosDef.sqr (c₁ - c₂))) *
       bump ((1 + 1) * a) ((c₁ + c₂) * PosDef.twoInv) x :
         by unfold bump; reflexivity

/-========== 有限スパンと積閉包（整備済み sum 機構の活用） ==========-/

/-- 有限スパン: Σᵢ αᵢ·bump a (cᵢ) -/
hott definition bumpSum (a : ℝ) (n : ℕ) (α c : ℕ → ℝ) (x : ℝ) : ℝ :=
PosDef.sum n (λ i, α i * bump a (c i) x)

/-- 二重スパン: Σᵢⱼ γᵢⱼ·bump a (eᵢⱼ) -/
hott definition doubleBumpSum (a : ℝ) (n m : ℕ) (γ : ℕ → ℕ → ℝ) (e : ℕ → ℕ → ℝ) (x : ℝ) : ℝ :=
PosDef.sum n (λ i, PosDef.sum m (λ j, γ i j * bump a (e i j) x))

/-- スパンの積閉包: Σαᵢk(cᵢ) · Σβⱼk(dⱼ) = Σᵢⱼ (αᵢβⱼ·exp(-a·twoInv·(cᵢ-dⱼ)²))·k(2a, mᵢⱼ)
   （sumMul / sum.ext / prodReorder / bumpProduct / mulAssoc のチェーン） -/
hott theorem bumpSumMulClosed (a : ℝ) (n m : ℕ) (α c β d : ℕ → ℝ) (x : ℝ) :
  bumpSum a n α c x * bumpSum a m β d x =
  doubleBumpSum ((1 + 1) * a) n m
    (λ i j, (α i * β j) * exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j))))
    (λ i j, (c i + d j) * PosDef.twoInv) x :=
calc bumpSum a n α c x * bumpSum a m β d x
     = (PosDef.sum n (λ i, α i * bump a (c i) x)) * (PosDef.sum m (λ j, β j * bump a (d j) x)) :
         by unfold bumpSum; reflexivity,
     = PosDef.sum n (λ i, (α i * bump a (c i) x) * (PosDef.sum m (λ j, β j * bump a (d j) x))) :
         Id.symm (PosDef.sumMul n (λ i, α i * bump a (c i) x) (PosDef.sum m (λ j, β j * bump a (d j) x))),
     = PosDef.sum n (λ i, PosDef.sum m (λ j, (α i * bump a (c i) x) * (β j * bump a (d j) x))) :
         PosDef.sum.ext n (λ i,
            @ring.comm.mulComm R.τ _ (α i * bump a (c i) x) (PosDef.sum m (λ j, β j * bump a (d j) x)) ⬝
            Id.symm (PosDef.sumMul m (λ j, β j * bump a (d j) x) (α i * bump a (c i) x)) ⬝
            PosDef.sum.ext m (λ j,
               @ring.comm.mulComm R.τ _ (β j * bump a (d j) x) (α i * bump a (c i) x))),
     = PosDef.sum n (λ i, PosDef.sum m (λ j, (α i * β j) * (bump a (c i) x * bump a (d j) x))) :
         PosDef.sum.ext n (λ i, PosDef.sum.ext m (λ j,
            prodReorder (α i) (β j) (bump a (c i) x) (bump a (d j) x))),
     = PosDef.sum n (λ i, PosDef.sum m (λ j,
         (α i * β j) * (exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j))) *
                       bump ((1 + 1) * a) ((c i + d j) * PosDef.twoInv) x))) :
         PosDef.sum.ext n (λ i, PosDef.sum.ext m (λ j,
            ap (λ z, (α i * β j) * z) (bumpProduct a (c i) (d j) x))),
     = PosDef.sum n (λ i, PosDef.sum m (λ j,
         ((α i * β j) * exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j)))) *
         bump ((1 + 1) * a) ((c i + d j) * PosDef.twoInv) x)) :
         PosDef.sum.ext n (λ i, PosDef.sum.ext m (λ j,
            Id.inv (@ring.assoc.mulAssoc R.τ _ (α i * β j) (exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j)))) (bump ((1 + 1) * a) ((c i + d j) * PosDef.twoInv) x)))),
     = PosDef.sum n (λ i, PosDef.sum m (λ j,
         ((α i * β j) * exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j)))) *
         bump ((1 + 1) * a) ((c i + d j) * PosDef.twoInv) x)) : by reflexivity,
     = doubleBumpSum ((1 + 1) * a) n m
         (λ i j, (α i * β j) * exp (-(a * PosDef.twoInv * PosDef.sqr (c i - d j))))
         (λ i j, (c i + d j) * PosDef.twoInv) x :
         by unfold doubleBumpSum; reflexivity

/-========== 一様近似と普遍性 ==========-/

/-- |e| ≤ δ -/
hott definition absLe (e δ : ℝ) : Type := R.ρ (abs e) δ

/-- 有界窓 |x| ≤ B 上の bumpSum による一様 δ-近似
   （コンパクト集合 [-B,B] 上の SW 密度に対応。ℝ 全体ではガウススパンは
   消失しない関数を一様近似できないため、窓を明示する必要がある） -/
hott definition windowApprox (B : ℝ) (a : ℝ) (f : ℝ → ℝ) (n : ℕ) (α c : ℕ → ℝ) (δ : ℝ) : Type :=
Π x, R.ρ (abs x) B → absLe (f x - bumpSum a n α c x) δ

/-- 連続関数 f : ℝ → ℝ（各点連続。標準計量 Rₘ による）。
   Stone–Weierstrass の密度定理は連続関数の一様近似のみを保証するため、
   universalKernel の量化は連続関数に制限する。
   注意: この仮定は「窓 [-B,B] 上の連続性」より強い（ℝ 全体で連続）が、
   SW の近似保証が適用される十分条件としては安全側。 -/
hott definition continuousFun (f : ℝ → ℝ) : Type :=
Π x, @continuous Rₘ Rₘ f x

/-- 普遍カーネルの定義: 任意の有界窓上で任意の連続関数 f を有限スパンで一様に近似できる -/
hott definition universalKernel (a : ℝ) : Type :=
Π (B : ℝ) (f : ℝ → ℝ), continuousFun f → Π (δ : ℝ), 0 < δ → Σ n, Σ (α : ℕ → ℝ), Σ (c : ℕ → ℝ), windowApprox B a f n α c δ

/--
  Stone–Weierstrass（ガウススパン版）— 実解析の残差をまとめた公理。

  SW による密度定理の残差（本ライブラリの射程外）:
  (1) 定義域のコンパクト性（有界窓 [-B,B] 上の連続関数空間 C([-B,B],ℝ) と sup ノルム）
  (2) 点分離: x ≠ y ⇒ k(x,x) = 1 ≠ k(x,y)（exp の単調性・正値性、0 < sqr(x-y)）
  (3) 定数関数の近似（広幅ガウスの極限）
  注意: universalKernel の f は連続関数（continuousFun）に限定している。
  SW の仮定に整合させるためで、不連続関数の近似は一般に不可能。
  一方、代数的核心（スパンが積で閉じる = bumpSumMulClosed）は本ファイルで証明済み。
  これは HoTT の問題ではなく実解析（Weierstrass 近似定理）の内容。
  注意: 近似は有界窓 [-B,B] 上でのみ主張する。ℝ 全体では f ≡ 1 など
  消失しない関数はガウススパン（|x|→∞ で 0）では一様近似できないため。
-/
hott axiom stoneWeierstrassGauss (a : ℝ) : 0 < a → universalKernel a

/-- ガウスカーネル（幅 ε）は普遍カーネル: ε > 0 なら universalKernel (ε²) -/
hott theorem gaussianUniversal (ε : ℝ) (hε : 0 < ε) : universalKernel (ε * ε) :=
stoneWeierstrassGauss (ε * ε) (PosDef.mulPos hε hε)


/-
  ============================================================================
  追記評価20: 普遍性チェーンの D ワールド化（gaussianRbfD 切替）の評価
  ============================================================================

  評価: KernelUniversal（ガウス RBF の普遍性）の exp 依存 — bump が exp で定義され、
  expZero / expAdd / expNonneg（= expAdd 由来）に依存 — を、ライブラリ標準の
  D ワールド（expD = 級数定義。gaussKernelD / gaussianRbfD と同じ基盤）へ
  切替える評価。
  ※ 前提の正確化: KernelUniversal は RBF.lean を import せず（GroundZero + PosDef
    のみ）、bump := exp として exp 公理に直接依存している。切替先も expD 基盤
    （gaussianRbfD はその計量動径インスタンス）である。

  probe: /tmp/eval20_probe.lean（namespace Eval20、EXIT 0）
  ※ 以下の D ワールド宣言は probe 用であり、ライブラリの宣言ではない（import 不可）。

  切替の実体（機械的翻訳。環ツールキット subSelf / midSquare / prodReorder /
  twoInvMul / half / paral 等は exp フリーで共有）:
    · bumpD a c x := PosDef.expD (-(a · sqr (x-c)))      （exp → expD）
    · bumpCenterD / bumpSymmD / bumpProductD / bumpSumMulClosedD
      （expAdd → PosDef.expAddD、expZero → BinomTaylor.expZeroD、negAdd は環公理のまま）
    · expNonnegD（新規導出）: expD z = expD(z·twoInv)² ≥ 0
      （PosDef.expNonneg と同型の証明: expAddD + halve + sqrNonneg）
    · windowApproxD / universalKernelD / stoneWeierstrassGaussD / gaussianUniversalD

  検証（#print axioms 実測）:
    bumpSymmD                      : exp 系ゼロ（インフラのみ）
    bumpCenterD                    : infSumIsLim のみ（expZeroD 経由）
    expNonnegD / bumpNonnegD /
    bumpProductD / bumpSumMulClosedD: {convExpD, convAbsExpD, infSumIsLim, mertens}
                                      の 4 公理（= expAddD の依存。infSumNonneg は
                                      不要 — gaussPsdD 系のみが要する）
    gaussianUniversalD             : stoneWeierstrassGaussD + インフラ（exp 系ゼロ）
    （対照: 現行 exp 版は bumpProduct / bumpSumMulClosed = {exp, expAdd}、
      bumpCenter = {exp, expZero}、bumpSymm = {exp}、gaussianUniversal =
      {stoneWeierstrassGauss, exp}）

  結論:
    · 切替は完全に可能（証明構造は同一、exp → expD / expAdd → expAddD の置換のみ。
      probe が一回で EXIT 0）。
    · exp 公理 {exp, expAdd, expZero} は KernelUniversal から消滅し、ライブラリ
      全体の統一基盤（conv 系）に乗る — gram / RBF / 表現子系（追記評価17〜19、
      5 公理）の部分集合（4 公理）で済み、むしろ少ない。残る公理は
      stoneWeierstrassGaussD（実解析の残差。exp 版と同内容）。
    · コスト: bump 系 12 宣言（bumpD / bumpCenterD / bumpSymmD / bumpNonnegD /
      bumpProductD / bumpSumD / doubleBumpSumD / bumpSumMulClosedD / windowApproxD /
      universalKernelD / stoneWeierstrassGaussD / gaussianUniversalD）+ expNonnegD の
      D 版二重化。exp 版は孤児化するため、RBF.lean 移設または削除が後続課題
      （追記評価19 の exp 理論と同列に集約可能）。
  ============================================================================
-/
end KernelUniversal
