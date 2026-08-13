import GroundZero
import PosDef

namespace RBF

open GroundZero.Algebra
open GroundZero.Algebra.Group
open GroundZero.Theorems (funext)
open GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv

/-
  Radial Basis Function（動径基底関数）: カーネル k と距離 ρ の合成。

  rbf k M c x := k (ρ x c)

  * M : Metric（距離構造、GroundZero.Algebra.Reals 由来）
  * k : カーネル関数（ガウス exp(-ε²r²) 等は、exp を追加すればこの k に入る）
  * D ワールド版（gaussKernelD / gaussianRbfD、追記評価18）は expD を扱うため
    PosDef を import する（循環なし: PosDef は GroundZero のみ import）。
  * exp ワールドのカーネル理論（absSqr / negSub / sqrSym / rbfGaussEq /
    gaussSymm / kernelSym / expPos / kernelPos / expMonotone / kernelLeOne）は
    追記評価19 で KernelLearn から移設した（KernelLearn の表現子系の D 化に伴う
    孤児化対策。これにより exp ワールドの残存範囲は本ファイルのみ）。
-/
hott definition rbf (k : ℝ → ℝ) (M : Metric) (c : M.carrier) : M.carrier → ℝ :=
λ x, k (M.ρ x c)

/-
  シフト不変性（単純版）:
  距離を保つ写像 T で「中心 c と評価点 x」を同時にずらしても値は不変。
-/
hott theorem rbfShiftInvariant (k : ℝ → ℝ) (M : Metric) (T : M.carrier → M.carrier)
  (hT : Π x c, M.ρ x c = M.ρ (T x) (T c)) (c x : M.carrier) :
  rbf k M c x = rbf k M (T c) (T x) :=
begin
  unfold rbf;
  apply ap k;
  exact hT x c
end

/-
  シフト不変性（群作用版）:
  群 G が距離を保つように左作用 φ : G ⮎ M.carrier で動いているとき、
  評価点を g でずらすのは、中心を g⁻¹ でずらすのと等価。
  （RBF 補間の「入力の平行移動 = 中心の逆平行移動」に対応）
-/
hott theorem rbfShiftEquivariant (k : ℝ → ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c : M.carrier) (g : G.carrier) (x : M.carrier) :
  rbf k M c (φ.1 g x) = rbf k M (φ.1 (G.ι g) c) x :=
begin
  unfold rbf;
  apply ap k;
  have actInv : φ.1 g (φ.1 (G.ι g) c) = c :=
    φ.2.2 g (G.ι g) c ⬝ ap (φ.1 · c) (G.mulRightInv g) ⬝ φ.2.1 c;
  exact ap (M.ρ (φ.1 g x)) (Id.symm actInv) ⬝ Id.symm (hφ g x (φ.1 (G.ι g) c))
end

/-- 関数的な形: 入力を g だけずらす ≃ 中心を g⁻¹ だけずらす
    （`~` 表記はこの文脈で宇宙が曖昧になるため `Homotopy` を明示） -/
hott corollary rbfShiftEquivariantHom (k : ℝ → ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c : M.carrier) (g : G.carrier) :
  Homotopy (rbf k M c ∘ φ.1 g) (rbf k M (φ.1 (G.ι g) c)) :=
λ x, rbfShiftEquivariant k M G φ hφ c g x

/-- 関数等式の形（関数外延性による持ち上げ） -/
hott corollary rbfShiftEquivariantFun (k : ℝ → ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c : M.carrier) (g : G.carrier) :
  rbf k M c ∘ φ.1 g = rbf k M (φ.1 (G.ι g) c) :=
funext (λ x, rbfShiftEquivariant k M G φ hφ c g x)

/-- 2 中心の RBF の和（シフト不変性が和に持ち上がる例） -/
hott definition rbfSum (k : ℝ → ℝ) (M : Metric) (c₁ c₂ : M.carrier) : M.carrier → ℝ :=
λ x, k (M.ρ x c₁) + k (M.ρ x c₂)

hott theorem rbfSumShiftEquivariant (k : ℝ → ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c₁ c₂ : M.carrier) (g : G.carrier) (x : M.carrier) :
  rbfSum k M c₁ c₂ (φ.1 g x) = rbfSum k M (φ.1 (G.ι g) c₁) (φ.1 (G.ι g) c₂) x :=
begin
  unfold rbfSum;
  exact Equiv.bimap (λ (a b : ℝ), a + b)
    (rbfShiftEquivariant k M G φ hφ c₁ g x)
    (rbfShiftEquivariant k M G φ hφ c₂ g x)
end

/-
  Gaussian RBF（ガウス動径基底関数）の具体化。

  指数関数 exp・正規化 expZero・加法性 expAdd・符号分配 negAdd は
  ライブラリ本体（GroundZero/Algebra/Reals.lean）に統合済み。
  `hott axiom` によりこれらには [GroundZero] 仮定が付き、
  HoTT スコープ内（hott 定義）でのみ使用できる。
-/
/-- ガウスカーネル k(r) = exp(-ε²·r²) -/
hott definition gaussKernel (ε : ℝ) : ℝ → ℝ :=
λ r, exp (-(ε * ε * (r * r)))

/-- ガウス型 RBF: φ(x) = exp(-ε²·ρ(x,c)²) -/
hott definition gaussianRbf (ε : ℝ) (M : Metric) (c : M.carrier) : M.carrier → ℝ :=
rbf (gaussKernel ε) M c

/-- ガウス RBF のシフト不変性（単純版）: 一般定理からの帰着 -/
hott corollary gaussianRbfShiftInvariant (ε : ℝ) (M : Metric) (T : M.carrier → M.carrier)
  (hT : Π x c, M.ρ x c = M.ρ (T x) (T c)) (c x : M.carrier) :
  gaussianRbf ε M c x = gaussianRbf ε M (T c) (T x) :=
rbfShiftInvariant (gaussKernel ε) M T hT c x

/-- ガウス RBF のシフト等価性（群作用版）: 入力を g でシフト ≃ 中心を g⁻¹ でシフト -/
hott corollary gaussianRbfShiftEquivariant (ε : ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c : M.carrier) (g : G.carrier) (x : M.carrier) :
  gaussianRbf ε M c (φ.1 g x) = gaussianRbf ε M (φ.1 (G.ι g) c) x :=
rbfShiftEquivariant (gaussKernel ε) M G φ hφ c g x

/-- ガウス RBF は中心で規格化される: φ(c) = exp(-ε²·0²) = 1 -/
hott corollary gaussianRbfCenter (ε : ℝ) (M : Metric) (c : M.carrier) :
  gaussianRbf ε M c c = 1 :=
begin
  unfold gaussianRbf gaussKernel;
  transitivity; apply ap exp;
    apply ap (λ z, -(ε * ε * (z * z))); apply M.refl c;
  transitivity; apply ap exp;
    transitivity; apply ap (λ z, -(ε * ε * z)); apply @ring.zeroMul R.τ _ 0;
    transitivity; apply ap (λ z, -z); apply @ring.mulZero R.τ _ (ε * ε);
    symmetry; apply R.zeroEqMinusZero (idp 0);
  apply expZero
end

/-- 2 中心のガウス RBF の和 -/
hott definition gaussianRbfSum (ε : ℝ) (M : Metric) (c₁ c₂ : M.carrier) : M.carrier → ℝ :=
rbfSum (gaussKernel ε) M c₁ c₂

hott corollary gaussianRbfSumShiftEquivariant (ε : ℝ) (M : Metric) (G : Group)
  (φ : G ⮎ M.carrier) (hφ : Π g x y, M.ρ x y = M.ρ (φ.1 g x) (φ.1 g y))
  (c₁ c₂ : M.carrier) (g : G.carrier) (x : M.carrier) :
  gaussianRbfSum ε M c₁ c₂ (φ.1 g x) = gaussianRbfSum ε M (φ.1 (G.ι g) c₁) (φ.1 (G.ι g) c₂) x :=
rbfSumShiftEquivariant (gaussKernel ε) M G φ hφ c₁ c₂ g x

/-
  ============================================================================
  D ワールド版ガウス RBF（追記評価16 (C) の実装 = 追記評価18）
  ============================================================================

  exp の代わりに expD（級数定義）を使う D ワールド版。rbfPsd / gramRbfNonneg
  （RBF 名義の正半定値性）の exp 依存（expSeries 公理）を除去するための再定義。
  追記評価16 (C) のとおり exp 版 gaussianRbf と二重化する（コスト）。

  正半定値性は KernelLearn 側で、gaussianRbfD と PosDef.gaussKernelD の一致
  （absSqr + sqrSym による、exp 公理・conv 公理に非依存）を経由して
  PosDef.gaussPsdD から導出される（#print axioms 実測: 5 公理、exp 系ゼロ）。
-/
/-- ガウスカーネル（D ワールド版）: k(r) = expD(-ε²·r²) -/
hott definition gaussKernelD (ε : ℝ) : ℝ → ℝ :=
λ r, PosDef.expD (-(ε * ε * (r * r)))

/-- ガウス型 RBF（D ワールド版）: φ(x) = expD(-ε²·ρ(x,c)²) -/
hott definition gaussianRbfD (ε : ℝ) (M : Metric) (c : M.carrier) : M.carrier → ℝ :=
rbf (gaussKernelD ε) M c

/-
  ガウスカーネルの積則（正しい形）:
  同幅のガウスの積はガウス:  k(r₁)·k(r₂) = exp(-ε²(r₁² + r₂²))

  注意: k(r₁ + r₂) = k(r₁)·k(r₂) はガウスでは一般に不成立
        （成立するのは指数カーネル expKernel の方、下参照）
-/
hott theorem gaussKernelMul (ε r₁ r₂ : ℝ) :
  gaussKernel ε r₁ * gaussKernel ε r₂ = exp (-(ε * ε * (r₁ * r₁ + r₂ * r₂))) :=
begin
  unfold gaussKernel;
  exact Id.symm (expAdd (-(ε * ε * (r₁ * r₁))) (-(ε * ε * (r₂ * r₂)))) ⬝
    ap exp (Id.symm (negAdd (ε * ε * (r₁ * r₁)) (ε * ε * (r₂ * r₂))) ⬝
            ap (λ z, -z) (Id.symm (@ring.distribLeft R.τ _ (ε * ε) (r₁ * r₁) (r₂ * r₂))))
end

/-- 指数カーネル k(r) = exp(-ε·r): 加法性 k(r₁ + r₂) = k(r₁)·k(r₂) を満たす -/
hott definition expKernel (ε : ℝ) : ℝ → ℝ :=
λ r, exp (-(ε * r))

/-- 指数カーネルの合成性質（ユーザー指定の形）: k(r₁ + r₂) = k(r₁)·k(r₂) -/
hott theorem expKernelAdd (ε r₁ r₂ : ℝ) :
  expKernel ε (r₁ + r₂) = expKernel ε r₁ * expKernel ε r₂ :=
begin
  unfold expKernel;
  exact ap (λ z, exp (-z)) (@ring.distribLeft R.τ _ ε r₁ r₂) ⬝
        ap exp (negAdd (ε * r₁) (ε * r₂)) ⬝
        expAdd (-(ε * r₁)) (-(ε * r₂))
end

/-- 公理の整合性チェック: exp a · exp (-a) = exp 0 = 1（expAdd と expZero が連携） -/
hott corollary expNeg (a : ℝ) : exp a * exp (-a) = 1 :=
Id.symm (expAdd a (-a)) ⬝ ap exp (R.τ.addComm a (-a) ⬝ R.τ.addLeftNeg a) ⬝ expZero

/-
  ============================================================================
  exp ワールドのカーネル理論 — KernelLearn から移設（追記評価19）
  ============================================================================

  追記評価19 により KernelLearn の表現子系は D ワールド（gaussKernelD）に切替わり、
  孤児化した exp ワールドの橋渡し・カーネル基本性質をここへ移設した（exp 理論の
  住処への集約）。これにより exp ワールドの残存範囲は本ファイルの exp 理論のみ。

  ※ KernelLearn 側は D 版カーネルの対称性・ブリッジで本節の absSqr / sqrSym を
    RBF.absSqr / RBF.sqrSym として参照する。
-/
/-- 絶対値の平方は元の平方: |z|² = z²（全順序 R.total で場合分け） -/
hott lemma absSqr (z : ℝ) : abs z * abs z = z * z :=
begin
  match R.total 0 z with
  | Sum.inl p => { transitivity; apply ap (· * abs z); apply abs.pos p;
                   transitivity; apply ap (z * ·); apply abs.pos p;
                   reflexivity }
  | Sum.inr q => { transitivity; apply ap (· * abs z); apply abs.neg q.2;
                   transitivity; apply ap ((-z) * ·); apply abs.neg q.2;
                   exact PosDef.negMulNeg z z }
end

/-- 減法と符号: x - y = -(y - x) -/
hott lemma negSub (x y : ℝ) : x - y = -(y - x) :=
calc x - y = x + (-y) : by reflexivity,
     = (-y) + x : R.τ.addComm x (-y),
     = -(y + (-x)) : Id.symm (negAdd y (-x) ⬝ ap ((-y) + ·) (@Group.invInv R.τ⁺ x)),
     = -(y - x) : by reflexivity

/-- 平方の対称性: (x - y)² = (y - x)² -/
hott lemma sqrSym (x y : ℝ) : PosDef.sqr (x - y) = PosDef.sqr (y - x) :=
calc PosDef.sqr (x - y) = (x - y) * (x - y) : by reflexivity,
     = (-(y - x)) * (-(y - x)) : ap (λ z, z * z) (negSub x y),
     = (y - x) * (y - x) : PosDef.negMulNeg (y - x) (y - x),
     = PosDef.sqr (y - x) : by reflexivity

/-
  橋渡し: 動径関数の形の RBF と双変数カーネルの形は、ℝ の標準計量上で一致。
  RBF.gaussianRbf ε Rₘ c x = exp (-ε²·|x-c|²) = PosDef.gaussKernel ε x c
-/
hott theorem rbfGaussEq (ε c x : ℝ) : RBF.gaussianRbf ε Rₘ c x = PosDef.gaussKernel ε x c :=
begin
  unfold RBF.gaussianRbf RBF.rbf RBF.gaussKernel PosDef.gaussKernel;
  apply ap exp; apply ap (λ z, -((ε * ε) * z));
  exact absSqr (x - c)
end

/-- 正規化（exp 版）: k(x,x) = exp(-ε²·0²) = 1（D 版は KernelLearn の kernelCenter） -/
hott corollary kernelCenter (ε x : ℝ) : PosDef.gaussKernel ε x x = 1 :=
Id.symm (rbfGaussEq ε x x) ⬝ gaussianRbfCenter ε Rₘ x

/-
  対称性（exp 版）: k(x,y) = k(y,x)（核行列は対称）。

  証明を一度だけ IsSymmetric インスタンス（関数レベルの対称性クラス、
  Meta/Symm.lean）として登録し、以後 k x y = k y x の形のゴールは
  `by symm` 一発で閉じる。※ 循環に注意: kernelSym を `⟨kernelSym ε⟩` と
  定義し直さないこと（kernelSym は本インスタンスから導出される）。
-/
hott instance gaussSymm (ε : ℝ) : IsSymmetric (PosDef.gaussKernel ε) :=
⟨λ x y, begin
  unfold PosDef.gaussKernel;
  apply ap exp; apply ap (λ z, -((ε * ε) * z));
  exact sqrSym x y
end⟩

hott corollary kernelSym (ε x y : ℝ) : PosDef.gaussKernel ε x y = PosDef.gaussKernel ε y x := by
  symm

/-- exp は狭義正: 0 < exp z（expNonneg と expNeg から導出 — 公理不要） -/
hott theorem expPos (z : ℝ) : 0 < exp z :=
⟨λ p, @field.nontrivial R.τ _
  (Id.symm (expNeg z) ⬝ ap (· * exp (-z)) (Id.symm p) ⬝
   @ring.zeroMul R.τ _ (exp (-z)) ⬝ Id.symm PosDef.additiveUnit),
  PosDef.expNonneg z⟩

/-- ガウスカーネルは狭義正: 0 < k(x,y) -/
hott corollary kernelPos (ε x y : ℝ) : 0 < PosDef.gaussKernel ε x y :=
expPos (-((ε * ε) * PosDef.sqr (x - y)))

/--
  実解析の公理（3つ目、収束論の代用）: exp は単調増加。
  expAdd・expZero からは導出できない。カーネルの有界性 k ≤ 1 に必要。
-/
hott axiom expMonotone (a b : ℝ) : R.ρ a b → R.ρ (exp a) (exp b)

/-- 有界性: k(x,y) ≤ 1（expMonotone による。0 < k ≤ 1 で正規化カーネル） -/
hott theorem kernelLeOne (ε x y : ℝ) : R.ρ (PosDef.gaussKernel ε x y) (1 : ℝ) :=
begin
  unfold PosDef.gaussKernel;
  apply Equiv.transport (R.ρ (exp (-((ε * ε) * PosDef.sqr (x - y))))); exact expZero;
  apply expMonotone (-((ε * ε) * PosDef.sqr (x - y))) 0;
  apply R.zeroLeImplZeroGeMinus;
  exact PosDef.mulNonneg (PosDef.sqrNonneg ε) (PosDef.sqrNonneg (x - y))
end

end RBF
