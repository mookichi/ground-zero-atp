import PosDef
import RBF
import BinomTaylor

/-
  ============================================================================
  カーネル学習（kernel learning）の形式化評価
  ============================================================================

  目的: PosDef.lean で完成したガウスカーネルの正半定値性を、カーネル法
        （カーネル学習）の中心的な応用の形式化に使う。追記評価17（追記評価16
        (A) の実装）により gram 系は D ワールド版カーネル gaussKernelD に切替え、
        PSD は gaussPsdD（5 公理 {convExpD, convAbsExpD, infSumIsLim, mertens,
        infSumNonneg}、exp 系ゼロ）を直接適用して証明する。旧 gaussPsdDE
        （追記評価14 で導入）は追記評価17 で削除。RBF 名義の命題
        （gramRbfNonneg / rbfPsd）も追記評価18（追記評価16 (C) の実装）で
        D ワールド版 RBF（RBF.gaussianRbfD）に切替え、exp 依存を完全除去。
        #print axioms 実測: gramRbfNonneg / rbfPsd も gaussPsdD と同じ 5 公理。
        追記評価19 で表現子系（representer / featureMap / representerAsFeatures /
        gaussEqShift / representerShiftInvariant / kernelCenter）も D ワールド化。
        孤児化した exp ワールドのカーネル理論（rbfGaussEq / gaussSymm / kernelSym /
        expPos / kernelPos / expMonotone / kernelLeOne / absSqr / sqrSym）は
        RBF.lean へ移設。KernelLearn の exp 依存は完全に消滅した。

  このファイルで形式化するもの:
    1. RBF とカーネルの橋渡し
       D ワールド版: RBF.gaussianRbfD ε Rₘ c x = PosDef.gaussKernelD ε c x
       （absSqr: |z|² = z² を要する。RBF は動径関数の形、
        gaussKernel は双変数カーネルの形 — カーネル学習は両方の視点を使う）
       ※ exp ワールド版の橋渡し rbfGaussEq と absSqr / sqrSym は追記評価19 で
         RBF.lean へ移設（RBF.rbfGaussEq / RBF.absSqr / RBF.sqrSym）。
    2. カーネルの基本性質（学習の前提となる性質）
       · k(x,x) = 1          （正規化。D 版 kernelCenter — BinomTaylor.expZeroD
                               による、exp 公理に非依存）
       · k(x,y) = k(y,x)     （対称性 → 核行列は対称。D 版 gaussSymmD）
       · 0 < k(x,y) ≤ 1      （exp ワールドの基本性質。RBF.lean へ移設:
                               RBF.kernelPos / RBF.kernelLeOne）
       · 多項式カーネル (x·y+c)ᵈ の対称性（IsSymmetric → biFormSymI）
    3. 核行列（Gram 行列）の半正定値性 — gaussPsd の直接の応用:        · gramNonneg: 0 ≤ Σᵢⱼ αᵢ αⱼ k(xᵢ, xⱼ)（任意の有限訓練集合と係数）
        · rbfPsd: RBF 版カーネルの PSD（橋渡し経由の転送）
        · gramSym: gram α β = gram β α（双線型形式レベルの対称性 G = Gᵀ。
          PosDef.biFormSymI（IsSymmetric 型クラス版）から導出）
    4. 表現子（representer）とカーネルトリック:
       · f = Σᵢ αᵢ k(xᵢ, ·) の評価 f(xⱼ) = Σᵢ αᵢ k(xᵢ, xⱼ)
         （特徴写像 φ(xⱼ) = k(·, xⱼ) との内積 = カーネルトリック）
       · 予測のシフト不変性（RBF.lean の rbfShiftInvariant からの帰着）

  完全形式化できていないもの（末尾の評価コメント参照）:
    · カーネルリッジ回帰の双対解 α = (G + λI)⁻¹y — 行列・逆行列・
      ベクトル空間の理論が必要（gramNonneg はその正定値性の前提）。
    · 表現定理（正則化 ERM の最小解が訓練点のカーネルが張る空間に
      落ちる）— RKHS・Hilbert 空間の理論が必要。
    · 狭義正定値性（相異なる点で G が正則 → 補間の一意性）
      — gaussPsd は半正定値性のみ。
  ============================================================================
-/
namespace KernelLearn

open GroundZero.Algebra
open GroundZero.Algebra.Group
open GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv

/-
  ============================================================================
  1. RBF とカーネルの橋渡し
  ============================================================================

  exp ワールドの橋渡し（absSqr / negSub / sqrSym / rbfGaussEq）は追記評価19 で
  RBF.lean へ移設した（exp 理論の住処。RBF.absSqr / RBF.sqrSym 等として参照）。
  D ワールドの橋渡し gaussianRbfD_eq_gaussKernelD は §2 の D セクションにある。
-/

/-
  ==========================================================================
  2. カーネルの基本性質
  ==========================================================================
-/

/-
  正規化 k(x,x) = 1 は D ワールド版カーネル gaussKernelD で示す（追記評価19。
  BinomTaylor.expZeroD によるため exp 公理に非依存。infSumIsLim のみに依存）。
  対称性と 0 < k ≤ 1 の exp ワールド版は RBF.lean へ移設した（下記ポインタ）。
-/

/-- 正規化（D 版）: k(x,x) = expD(-ε²·0²) = 1（BinomTaylor.expZeroD による） -/
hott corollary kernelCenter (ε x : ℝ) : PosDef.gaussKernelD ε x x = 1 :=
begin
  unfold PosDef.gaussKernelD;
  transitivity; apply ap PosDef.expD;
    apply ap (λ z, -((ε * ε) * z)); apply ap PosDef.sqr;
    exact R.τ.addComm x (-x) ⬝ R.τ.addLeftNeg x;
  transitivity; apply ap PosDef.expD;
    transitivity; apply ap (λ z, -((ε * ε) * z)); apply @ring.zeroMul R.τ _ 0;
    transitivity; apply ap (λ z, -z); apply @ring.mulZero R.τ _ (ε * ε);
    symmetry; apply R.zeroEqMinusZero (idp 0);
  exact BinomTaylor.expZeroD
end

/-
  対称性（exp 版 gaussSymm インスタンス / kernelSym）は追記評価19 で RBF.lean
  へ移設した（RBF.gaussSymm / RBF.kernelSym）。D 版の対称性は下記の gaussSymmD
  （IsSymmetric インスタンス）。
-/

/-
  ============================================================================
  D ワールド（expD 版カーネル）— 追記評価16 (A) の実装（追記評価17）
  ============================================================================

  gram 系の核を gaussKernel から gaussKernelD に切替えるための部品群。
    · gaussSymmD     : IsSymmetric (gaussKernelD ε) — sqrSym のみで閉じる
                       （exp 公理に非依存）。gaussSymm の D 版ツイン。
                       gramSym の biFormSymI 型クラス解決に使用する。
    · gaussianRbfD_eq_gaussKernelD : RBF.gaussianRbfD ε Rₘ c x = gaussKernelD ε c x
                       （absSqr + sqrSym による、exp 公理・conv 公理に非依存
                       — 追記評価18）。gramRbfNonneg / rbfPsd（RBF 名義の
                       PSD）のブリッジ。
                       （absSqr / sqrSym は追記評価19 で RBF.lean へ移設、
                       KernelLearn 側は RBF.absSqr / RBF.sqrSym を参照）
    · rbfGaussSymmD  : IsSymmetric (λ a b, RBF.gaussianRbfD ε Rₘ a b)。
                       gramRbfSym の biFormSymI 型クラス解決に使用。

  ※ 追記評価17 で追加した gaussKernelEqD / rbfGaussEqD（exp 版 RBF と D 版
    カーネルの接続、expSeries 依存）は、追記評価18 で RBF 名義の PSD チェーンが
    gaussianRbfD（exp フリー）に切替わったため不要になり削除した。
  ============================================================================
-/
/-- D ワールド版カーネルの対称性（IsSymmetric インスタンス）: gaussKernelD は
    expD と sqr の対称性のみで閉じる（exp 公理に非依存）。gaussSymm の D 版。 -/
hott instance gaussSymmD (ε : ℝ) : IsSymmetric (PosDef.gaussKernelD ε) :=
⟨λ x y, ap (λ z, PosDef.expD (-((ε * ε) * z))) (RBF.sqrSym x y)⟩

/-- D 版 RBF と D 版カーネルの一致: RBF.gaussianRbfD ε Rₘ c x = gaussKernelD ε c x
    （absSqr と sqrSym による。exp 公理・conv 公理に非依存 — 追記評価18）。
    #print axioms 実測: exp 系ゼロ（インフラ公理のみ）。 -/
hott theorem gaussianRbfD_eq_gaussKernelD (ε c x : ℝ) :
  RBF.gaussianRbfD ε Rₘ c x = PosDef.gaussKernelD ε c x :=
calc RBF.gaussianRbfD ε Rₘ c x
     = PosDef.expD (-((ε * ε) * ((x - c) * (x - c)))) :
         begin
           unfold RBF.gaussianRbfD RBF.rbf RBF.gaussKernelD;
           apply ap PosDef.expD; apply ap (λ z, -((ε * ε) * z));
           exact RBF.absSqr (x - c)
         end,
     = PosDef.gaussKernelD ε c x :
         begin
           unfold PosDef.gaussKernelD;
           exact ap PosDef.expD (ap (λ z, -((ε * ε) * z)) (RBF.sqrSym x c))
         end

/-- D 版 RBF も対称（IsSymmetric インスタンス）: ブリッジ + gaussSymmD で exp フリー -/
hott instance rbfGaussSymmD (ε : ℝ) : IsSymmetric (λ a b, RBF.gaussianRbfD ε Rₘ a b) :=
⟨λ a b, gaussianRbfD_eq_gaussKernelD ε a b ⬝ (gaussSymmD ε).symm a b ⬝
        Id.symm (gaussianRbfD_eq_gaussKernelD ε b a)⟩

/-
  exp ワールドの性質（expPos / kernelPos / expMonotone / kernelLeOne）は
  追記評価19 で RBF.lean へ移設した（RBF.expPos / RBF.kernelPos /
  RBF.expMonotone / RBF.kernelLeOne）。
-/

/-
  ==========================================================================
  2.6 多項式カーネル — k(x,y) = (⟨x,y⟩ + c)ᵈ
  ==========================================================================

  多項式カーネル（多項式特徴写像に対応するカーネル）:
  k(x,y) = (⟨x,y⟩ + c)ᵈ。ℝ 上では内積はスカラー積 ⟨x,y⟩ = x·y なので
  k(x,y) = (x·y + c)ᵈ（c : ℝ はシフト定数、d : ℕ は次数）。
  冪 rpow はライブラリの GroundZero.Algebra.rpow を再利用。

  ※ PosDef.lean の polyKernelPsd はシフトなし版 (x·y)ⁿ の正半定値性
    （c = 0 の場合）。本セクションの +c 版は対称性のみを形式化しており、
    PSD は主張しない（c ≥ 0 が必要で、形式化は未実施）。

  対称性の証明は IsSymmetric インスタンスとして1回だけ与え、以後
  k x y = k y x は by symm、グラム形式レベルの対称性は biFormSymI
  （型クラス合成）で自動導出される。
-/

/-- 多項式カーネル: k(x,y) = (⟨x,y⟩ + c)ᵈ = (x·y + c)ᵈ -/
hott definition polyKernel (c : ℝ) (d : ℕ) (x y : ℝ) : ℝ :=
rpow (x * y + c) d

/-- 多項式カーネルの対称性（IsSymmetric インスタンス）: x·y = y·x に冪を適用 -/
hott instance polyKernelSymm (c : ℝ) (d : ℕ) : IsSymmetric (polyKernel c d) := ⟨
  λ x y, ap (fun z : ℝ => rpow (z + c) d) (@ring.comm.mulComm R.τ _ x y)
⟩

/-- 多項式カーネルの核行列（グラム行列） -/
hott definition polyGram (c : ℝ) (d : ℕ) (n : ℕ) (α β x : ℕ → ℝ) : ℝ :=
PosDef.sum n (λ i, PosDef.sum n (λ j, (α i * β j) * polyKernel c d (x i) (x j)))

/-- 核行列の対称性: polyGram α β = polyGram β α（biFormSymI による型クラス合成の自動導出） -/
hott theorem polyGramSym (c : ℝ) (d : ℕ) (n : ℕ) (α β x : ℕ → ℝ) :
  polyGram c d n α β x = polyGram c d n β α x :=
begin
  unfold polyGram;
  exact PosDef.biFormSymI (polyKernel c d) n α β x
end

/-
  ============================================================================
  3. 核行列（Gram 行列）の半正定値性 — gaussPsdD の応用
     （追記評価16 (A): gram 系を D ワールド版カーネル gaussKernelD に切替）
  ==========================================================================
-/

/-- 核行列の双線型形式: αᵀGβ = Σᵢⱼ αᵢ βⱼ k(xᵢ, xⱼ)。
    追記評価16 (A): カーネルを D ワールド版 gaussKernelD に切替（exp 系ゼロ）。 -/
hott definition gram (ε : ℝ) (n : ℕ) (α β : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
PosDef.sum n (λ i, PosDef.sum n (λ j, (α i * β j) * PosDef.gaussKernelD ε (x i) (x j)))

/--
  核行列の半正定値性 — gaussPsdD そのものの再定式化。
  カーネル学習の中心命題: 任意の有限訓練集合 {x₁..xₙ} と係数 α について
  αᵀGα = Σᵢⱼ αᵢ αⱼ k(xᵢ, xⱼ) ≥ 0。これが正則化リッジ回帰・SVM の
  最適化問題が well-posed である根拠（→ 末尾の評価コメント (1)）。
  追記評価16 (A): gaussPsdDE から gaussPsdD（D ワールド）に切替。
  #print axioms 実測: {convExpD, convAbsExpD, infSumIsLim, mertens,
  infSumNonneg} の 5 公理（exp / expAdd / expSeries 非依存）。
-/
hott theorem gramNonneg (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ) :
  R.ρ 0 (gram ε n α α x) :=
PosDef.gaussPsdD ε n α x

/-- RBF 版の核行列（Rₘ 計量上のガウス RBF で構成）。
    追記評価18: カーネルを D ワールド版 RBF（RBF.gaussianRbfD）に切替（exp フリー）。 -/
hott definition gramRbf (ε : ℝ) (n : ℕ) (α β : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
PosDef.sum n (λ i, PosDef.sum n (λ j, (α i * β j) * RBF.gaussianRbfD ε Rₘ (x i) (x j)))

/-- RBF 版核行列の半正定値性（gaussianRbfD_eq_gaussKernelD 経由の転送）。
    追記評価18: RBF 名義の PSD も exp フリーに。#print axioms 実測は
    gaussPsdD と同じ 5 公理（{convExpD, convAbsExpD, infSumIsLim, mertens,
    infSumNonneg}、exp / expAdd / expSeries 非依存）。 -/
hott theorem gramRbfNonneg (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ) :
  R.ρ 0 (gramRbf ε n α α x) :=
begin
  unfold gramRbf;
  apply Equiv.transport (R.ρ 0);
  exact PosDef.sum.ext n (λ i, PosDef.sum.ext n (λ j,
    ap (λ z, (α i * α j) * z) (Id.symm (gaussianRbfD_eq_gaussKernelD ε (x i) (x j)))));
  exact gramNonneg ε n α x
end

/-- ガウス RBF（D 版、ℝ 標準計量上）は正半定値カーネル:
    PSD (λ x y, RBF.gaussianRbfD ε Rₘ x y)（追記評価18: exp フリー、5 公理） -/
hott corollary rbfPsd (ε : ℝ) : PosDef.PSD (λ x y, RBF.gaussianRbfD ε Rₘ x y) :=
begin
  unfold PosDef.PSD; intro n α x;
  exact gramRbfNonneg ε n α x
end

/-- 核行列の対称性（双線型形式レベル）: gram α β = gram β α（G = Gᵀ）。
    追記評価16 (A): gaussKernelD 版に切替（gaussSymmD インスタンスで自動解決）。 -/
hott theorem gramSym (ε : ℝ) (n : ℕ) (α β : ℕ → ℝ) (x : ℕ → ℝ) :
  gram ε n α β x = gram ε n β α x :=
begin
  unfold gram;
  exact PosDef.biFormSymI (PosDef.gaussKernelD ε) n α β x
end

/- ※ 追記評価18: exp 版インスタンス rbfGaussSymm（rbfGaussEq 経由）は削除。
    gramRbfSym は D 版 rbfGaussSymmD（exp フリー）を使う。 -/

/-- RBF 版核行列の対称性（双線型形式レベル）。
    追記評価18: gaussianRbfD 版に切替（rbfGaussSymmD インスタンスで自動解決）。 -/
hott theorem gramRbfSym (ε : ℝ) (n : ℕ) (α β : ℕ → ℝ) (x : ℕ → ℝ) :
  gramRbf ε n α β x = gramRbf ε n β α x :=
begin
  unfold gramRbf;
  exact PosDef.biFormSymI (λ a b, RBF.gaussianRbfD ε Rₘ a b) n α β x
end

/-
  ============================================================================
  4. 表現子（representer）とカーネルトリック
  ============================================================================

  追記評価19 で D ワールド版カーネル gaussKernelD に切替（gram 系と同一カーネル）。
  表現子・特徴写像・予測のシフト不変性はすべて exp 公理に非依存
  （#print axioms 実測: インフラ公理のみ）。
-/

/--
  表現子: f = Σᵢ αᵢ k(xᵢ, ·)。カーネル学習の仮説空間（カーネルが張る
  空間）の元。表現定理は「正則化 ERM の最小解はこの形に落ちる」ことを
  主張する（→ 末尾の評価コメント (2)）。
-/
hott definition representer (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ) : ℝ → ℝ :=
λ z, PosDef.sum n (λ i, α i * PosDef.gaussKernelD ε (x i) z)

/--
  カーネルトリック（評価 = カーネル値の線型結合）:
  f(xⱼ) = Σᵢ αᵢ k(xᵢ, xⱼ)。特徴写像 φ(xⱼ) = k(·, xⱼ) を陽に計算せず、
  カーネル値だけで予測が評価できる。定義により成立。
-/
hott corollary representerEval (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ) (j : ℕ) :
  representer ε n α x (x j) = PosDef.sum n (λ i, α i * PosDef.gaussKernelD ε (x i) (x j)) :=
by reflexivity

/-- 特徴写像 φ(x) = k(·, x)（RKHS への埋め込みのカーネル表現） -/
hott definition featureMap (ε : ℝ) (x : ℝ) : ℝ → ℝ :=
λ z, PosDef.gaussKernelD ε z x

/-- 表現子は特徴写像の有限線型結合: f = Σᵢ αᵢ φ(xᵢ)（カーネル対称性による） -/
hott theorem representerAsFeatures (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ) :
  Homotopy (representer ε n α x) (λ z, PosDef.sum n (λ i, α i * featureMap ε (x i) z)) :=
λ z, PosDef.sum.ext n (λ i, ap (α i * ·) ((gaussSymmD ε).symm (x i) z))

/-- D 版ガウス RBF のシフト不変性（一般定理 rbfShiftInvariant からの帰着、exp フリー） -/
hott corollary gaussianRbfDShiftInvariant (ε : ℝ) (M : Metric) (T : M.carrier → M.carrier)
  (hT : Π x c, M.ρ x c = M.ρ (T x) (T c)) (c x : M.carrier) :
  RBF.gaussianRbfD ε M c x = RBF.gaussianRbfD ε M (T c) (T x) :=
RBF.rbfShiftInvariant (RBF.gaussKernelD ε) M T hT c x

/-- 距離を保つ写像 T のもとで D 版ガウスカーネルは不変（D 版ブリッジ + シフト不変性） -/
hott lemma gaussEqShift (ε : ℝ) (T : ℝ → ℝ)
  (hT : Π x c, Rₘ.ρ x c = Rₘ.ρ (T x) (T c)) (x c : ℝ) :
  PosDef.gaussKernelD ε x c = PosDef.gaussKernelD ε (T x) (T c) :=
Id.symm (gaussianRbfD_eq_gaussKernelD ε x c) ⬝
  gaussianRbfDShiftInvariant ε Rₘ T hT x c ⬝
  gaussianRbfD_eq_gaussKernelD ε (T x) (T c)

/--
  予測のシフト不変性: 入力全体を T で動かしても表現子の値は不変
  （f_{α, x}(z) = f_{α, T∘x}(T z)）。RBF のシフト不変性の学習への応用。
-/
hott theorem representerShiftInvariant (ε : ℝ) (n : ℕ) (α : ℕ → ℝ) (x : ℕ → ℝ)
  (T : ℝ → ℝ) (hT : Π x c, Rₘ.ρ x c = Rₘ.ρ (T x) (T c)) (z : ℝ) :
  representer ε n α x z = representer ε n α (λ i, T (x i)) (T z) :=
begin
  unfold representer;
  apply PosDef.sum.ext n; intro i;
  exact ap (α i * ·) (gaussEqShift ε T hT (x i) z)
end

/-
  ============================================================================
  4.5 リッジ回帰双対問題の損失項の凸性 — normSqConvex の応用
  ============================================================================

  カーネルリッジ回帰の双対問題 min_α ‖Gα - y‖² + λ·αᵀGα のうち、
  損失項 ‖Gα - y‖² の凸性を形式化する（正則化項 λ·αᵀGα の凸性は
  biFormConvex に帰着 — 末尾の評価コメント (1) 参照）。

  構成:
    · gramRow : 行列ベクトル積 Gα の i 成分 = Σⱼ αⱼ·k(xᵢ, xⱼ)
    · gramRowLin : G の線型性（sumAdd / sumMul による成分ごとの証明）
    · affineSub : スカラー版アフィン分解 (t·a + (1-t)·b) - y = t·(a-y) + (1-t)·(b-y)
    · dualObjective : 双対目的関数 f(α) = ‖Gα - y‖² + λ·αᵀGα
    · dualLossConvex : 損失項の凸性（normSqConvex + gramRowLin + affineSub）
-/

/-- 行列ベクトル積 Gα の i 成分: (Gα)ᵢ = Σⱼ αⱼ·k(xᵢ, xⱼ)。
    追記評価16 (A): gaussKernelD に切替（dualObjective の G を gram と同一カーネルに整合）。 -/
hott definition gramRow (ε : ℝ) (n : ℕ) (α x : ℕ → ℝ) (i : ℕ) : ℝ :=
PosDef.sum n (λ j, α j * PosDef.gaussKernelD ε (x i) (x j))

/-- G は線型: G(tα + (1-t)β) = t·Gα + (1-t)·Gβ（成分ごと） -/
hott lemma gramRowLin (ε : ℝ) (n : ℕ) (t : ℝ) (α β x : ℕ → ℝ) (i : ℕ) :
  gramRow ε n (λ k, t * α k + ((1 : ℝ) - t) * β k) x i =
  t * gramRow ε n α x i + ((1 : ℝ) - t) * gramRow ε n β x i :=
calc gramRow ε n (λ k, t * α k + ((1 : ℝ) - t) * β k) x i
     = PosDef.sum n (λ j, (t * α j + ((1 : ℝ) - t) * β j) * PosDef.gaussKernelD ε (x i) (x j)) : by reflexivity,
     = PosDef.sum n (λ j, t * (α j * PosDef.gaussKernelD ε (x i) (x j)) + ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j))) :
         PosDef.sum.ext n (λ j, calc (t * α j + ((1 : ℝ) - t) * β j) * PosDef.gaussKernelD ε (x i) (x j)
              = (t * α j) * PosDef.gaussKernelD ε (x i) (x j) + (((1 : ℝ) - t) * β j) * PosDef.gaussKernelD ε (x i) (x j) : @ring.distribRight R.τ _ (t * α j) (((1 : ℝ) - t) * β j) (PosDef.gaussKernelD ε (x i) (x j)),
              = t * (α j * PosDef.gaussKernelD ε (x i) (x j)) + (((1 : ℝ) - t) * β j) * PosDef.gaussKernelD ε (x i) (x j) : ap (· + (((1 : ℝ) - t) * β j) * PosDef.gaussKernelD ε (x i) (x j)) (@ring.assoc.mulAssoc R.τ _ t (α j) (PosDef.gaussKernelD ε (x i) (x j))),
              = t * (α j * PosDef.gaussKernelD ε (x i) (x j)) + ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j)) : ap (t * (α j * PosDef.gaussKernelD ε (x i) (x j)) + ·) (@ring.assoc.mulAssoc R.τ _ ((1 : ℝ) - t) (β j) (PosDef.gaussKernelD ε (x i) (x j)))),
     = PosDef.sum n (λ j, t * (α j * PosDef.gaussKernelD ε (x i) (x j))) + PosDef.sum n (λ j, ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j))) :
         Id.symm (PosDef.sumAdd n (λ j, t * (α j * PosDef.gaussKernelD ε (x i) (x j))) (λ j, ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j)))),
     = t * PosDef.sum n (λ j, α j * PosDef.gaussKernelD ε (x i) (x j)) + PosDef.sum n (λ j, ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j))) :
         ap (· + PosDef.sum n (λ j, ((1 : ℝ) - t) * (β j * PosDef.gaussKernelD ε (x i) (x j)))) (Id.symm (PosDef.mulSum t n (λ j, α j * PosDef.gaussKernelD ε (x i) (x j)))),
     = t * PosDef.sum n (λ j, α j * PosDef.gaussKernelD ε (x i) (x j)) + ((1 : ℝ) - t) * PosDef.sum n (λ j, β j * PosDef.gaussKernelD ε (x i) (x j)) :
         ap (t * PosDef.sum n (λ j, α j * PosDef.gaussKernelD ε (x i) (x j)) + ·) (Id.symm (PosDef.mulSum ((1 : ℝ) - t) n (λ j, β j * PosDef.gaussKernelD ε (x i) (x j)))),
     = t * gramRow ε n α x i + ((1 : ℝ) - t) * gramRow ε n β x i : by reflexivity

/-- アフィン分解（スカラー）: (t·a + (1-t)·b) - y = t·(a - y) + (1-t)·(b - y) -/
hott lemma affineSub (t a b y : ℝ) :
  (t * a + ((1 : ℝ) - t) * b) - y = t * (a - y) + ((1 : ℝ) - t) * (b - y) :=
calc (t * a + ((1 : ℝ) - t) * b) - y
     = (t * a + ((1 : ℝ) - t) * b) - (t + ((1 : ℝ) - t)) * y :
         ap ((t * a + ((1 : ℝ) - t) * b) - ·) (Id.symm (ap (· * y) (PosDef.addSubSelf t) ⬝ @ring.monoid.oneMul R.τ _ y)),
     = (t * a + ((1 : ℝ) - t) * b) - (t * y + ((1 : ℝ) - t) * y) :
         ap ((t * a + ((1 : ℝ) - t) * b) - ·) (@ring.distribRight R.τ _ t ((1 : ℝ) - t) y),
     = (t * a + ((1 : ℝ) - t) * b) - t * y - ((1 : ℝ) - t) * y :
         PosDef.subAddSub (t * a + ((1 : ℝ) - t) * b) (t * y) (((1 : ℝ) - t) * y),
     = (t * a - t * y) + (((1 : ℝ) - t) * b - ((1 : ℝ) - t) * y) :
         PosDef.subRegroup4 (t * a) (((1 : ℝ) - t) * b) (t * y) (((1 : ℝ) - t) * y),
     = t * (a - y) + ((1 : ℝ) - t) * (b - y) :
         ap (· + (((1 : ℝ) - t) * b - ((1 : ℝ) - t) * y)) (Id.symm (@ring.subDistribLeft R.τ _ t a y)) ⬝
         ap (t * (a - y) + ·) (Id.symm (@ring.subDistribLeft R.τ _ ((1 : ℝ) - t) b y))

/-- 残差の点別分解: t·(Gα-y)ᵢ + (1-t)·(Gβ-y)ᵢ = (G(tα+(1-t)β))ᵢ - yᵢ -/
hott lemma dualLossPointwise (ε : ℝ) (n : ℕ) (t : ℝ) (α β x y : ℕ → ℝ) (i : ℕ) :
  t * (gramRow ε n α x i - y i) + ((1 : ℝ) - t) * (gramRow ε n β x i - y i) =
  gramRow ε n (λ k, t * α k + ((1 : ℝ) - t) * β k) x i - y i :=
calc t * (gramRow ε n α x i - y i) + ((1 : ℝ) - t) * (gramRow ε n β x i - y i)
     = (t * gramRow ε n α x i + ((1 : ℝ) - t) * gramRow ε n β x i) - y i :
         Id.symm (affineSub t (gramRow ε n α x i) (gramRow ε n β x i) (y i)),
     = gramRow ε n (λ k, t * α k + ((1 : ℝ) - t) * β k) x i - y i :
         Id.symm (ap (· - y i) (gramRowLin ε n t α β x i))

/-- リッジ回帰双対目的関数: f(α) = ‖Gα - y‖² + λ·αᵀGα -/
hott definition dualObjective (ε η : ℝ) (n : ℕ) (α y x : ℕ → ℝ) : ℝ :=
PosDef.normSq n (λ i, gramRow ε n α x i - y i) + η * gram ε n α α x

/-- 損失項の凸性: 0 ≤ t ≤ 1 で ‖G(tα+(1-t)β) - y‖² ≤ t·‖Gα - y‖² + (1-t)·‖Gβ - y‖²
    （normSqConvex を残差ベクトルに適用 — リッジ回帰双対の凸性の損失項部分） -/
hott lemma dualLossConvex (ε : ℝ) (n : ℕ) (t : ℝ) (α β y x : ℕ → ℝ)
  (ht0 : R.ρ 0 t) (ht1 : R.ρ t 1) :
  R.ρ (PosDef.normSq n (λ i, gramRow ε n (λ k, t * α k + ((1 : ℝ) - t) * β k) x i - y i))
      (t * PosDef.normSq n (λ i, gramRow ε n α x i - y i) +
       ((1 : ℝ) - t) * PosDef.normSq n (λ i, gramRow ε n β x i - y i)) :=
begin
  apply Equiv.transport (λ z, R.ρ z (t * PosDef.normSq n (λ i, gramRow ε n α x i - y i) +
                                    ((1 : ℝ) - t) * PosDef.normSq n (λ i, gramRow ε n β x i - y i)));
  exact PosDef.sum.ext n (λ i, ap (λ w, w * w) (dualLossPointwise ε n t α β x y i));
  exact PosDef.normSqConvex n t (λ i, gramRow ε n α x i - y i) (λ i, gramRow ε n β x i - y i) ht0 ht1
end

/-
  ============================================================================
  5. 評価: カーネル学習の完全形式化に必要なもの
  ============================================================================

  本ファイルで形式化できたこと（すべて hott スコープで検証済み）:
    · gaussPsdD の応用 = 核行列の半正定値性 gramNonneg / rbfPsd
      （両者とも 5 公理、exp 系ゼロ。gramNonneg は追記評価17、RBF 名義の
       rbfPsd / gramRbfNonneg は追記評価18 で gaussianRbfD に切替）
      （カーネル法が機能する根拠: 任意の有限訓練集合に対する Gram 行列は PSD）
    · カーネルの基本性質（正規化 k(x,x) = 1 — D 版 kernelCenter / gaussSymmD）
      （exp ワールドの基本性質 0 < k ≤ 1 は追記評価19 で RBF.lean へ移設）
    · 表現子とカーネルトリック（評価 = カーネル値の線型結合 = 特徴写像との内積）
      （追記評価19 で D ワールド化 — exp フリー）
    · 予測のシフト不変性
    · リッジ回帰双対の損失項の凸性 dualLossConvex
      （gramRowLin + affineSub + PosDef.normSqConvex で形式化:
       min_α ‖Gα - y‖² + λ·αᵀGα の損失項 ‖Gα-y‖² は 0 ≤ t ≤ 1 で凸）

  完全形式化にはさらに必要なもの（ライブラリ未整備）:

  (1) カーネルリッジ回帰の双対解と正則化項の凸性
      正則化最小化問題 min_α ‖Gα - y‖² + λ·αᵀGα の解は α* = (G + λI)⁻¹y。
      これを形式化するには行列（n×n）・逆行列・ℝ 上のベクトル空間の理論が
      必要。損失項の凸性は dualLossConvex で形式化済み。正則化項 λ·αᵀGα の
      凸性は「G が PSD のとき二次形式 αᵀGα は凸」（biForm 版の凸性恒等式
      biFormConvex）に帰着するが、これは次段階の課題。

  (2) 表現定理（representer theorem）
      RKHS 上の正則化 ERM の最小解が Σᵢ αᵢ k(xᵢ, ·) の形に落ちる定理。
      RKHS（再生核ヒルベルト空間）・ノルム・Hilbert 空間の理論が必要。
      本ファイルの representer はその「解の形」をすでに与えている。

  (3) 狭義正定値性
      相異なる訓練点で Gram 行列が正則 → 補間の一意性。gaussPsd は半正定値性
      のみであり、狭義版にはより強い解析（積分表示・Fourier 解析）が必要。

  (4) ワンホット係数による再生性質の完全形 ⟨α, eⱼ⟩_G = f(xⱼ)
      この証明は断念（決定事項）。ℕ の < ・指標関数の補題が必要で、
      Nat ライブラリが未整備のため。本ファイルでは representerEval の
      定義的な形でカーネルトリックを形式化している。
  ============================================================================
-/

/-
  ============================================================================
  追記評価17: 追記評価16 (A) の実装 — gram 系の gaussKernelD 切替
  ============================================================================

  実施内容:
    · gaussSymmD（IsSymmetric (gaussKernelD ε)）をライブラリ instance として
      登録（sqrSym のみで閉じる、exp 非依存）。gramSym の biFormSymI 型クラス
      解決に使用。
    · gram / gramNonneg / gramSym を gaussKernelD に切替。
      gramNonneg := PosDef.gaussPsdD（#print axioms 実測: 5 公理
      {convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}、exp 系ゼロ）。
    · gramRbfNonneg は rbfGaussEqD ブリッジで gram に帰着していた（RBF 名義のため
      expSeries 依存 — 追記評価16 (B)。実測: 5 + exp + expSeries = 7 公理）。
      ※ 追記評価18 で gaussianRbfD に切替、exp フリー（5 公理）になった。
    · gramRow / gramRowLin（4.5 節の行列ベクトル積）も D ワールド化し、
      dualObjective の G が gram と同一カーネルになるよう整合。
    · PosDef.gaussPsdDE は削除（PosDef.lean 側の追記評価17 ブロック参照）。
      expEqExpD は gaussKernelEqD（RBF ブリッジ）が使用するため残置していた。
      ※ 追記評価18 で gaussKernelEqD / rbfGaussEqD は不要化し削除（PosDef の
        expEqExpD は exp と expD の接続補題として保持）。
    · 表現子（representer）系・カーネルの基本性質は exp ワールドのままだった
      （追記評価16 (C) の範囲）が、追記評価19 で表現子系・kernelCenter は
      D ワールドに切替、基本性質（gaussSymm / kernelSym / expPos / kernelPos /
      expMonotone / kernelLeOne）は RBF.lean へ移設した。
  ============================================================================
-/

/-
  ============================================================================
  追記評価18: 追記評価16 (C) の実装 — RBFD（gaussianRbfD）と RBF 名義 PSD の exp 除去
  ============================================================================

  実施内容:
    · RBF.lean に D ワールド版ガウス RBF を追加:
        RBF.gaussKernelD ε : ℝ → ℝ（k(r) = expD(-ε²·r²)）
        RBF.gaussianRbfD ε M c  : M.carrier → ℝ（φ(x) = expD(-ε²·ρ(x,c)²)）
      （exp 版 gaussianRbf と二重化 — 追記評価16 (C) のコスト）
    · ブリッジ gaussianRbfD_eq_gaussKernelD :
        RBF.gaussianRbfD ε Rₘ c x = gaussKernelD ε c x
        （absSqr + sqrSym による。exp 公理・conv 公理に非依存）
    · gramRbf / gramRbfNonneg / rbfPsd / gramRbfSym を RBF.gaussianRbfD に切替。
      rbfGaussSymmD（IsSymmetric (λ a b, gaussianRbfD ε Rₘ a b)）を追加。
    · 不要化した gaussKernelEqD / rbfGaussEqD（exp 版 RBF ↔ D 版カーネルの
      接続、expSeries 依存）と exp 版インスタンス rbfGaussSymm は削除。

  検証（#print axioms 実測、probe /tmp/eval18_probe.lean で確認後反映）:
      gramRbfNonneg / rbfPsd  : {convExpD, convAbsExpD, infSumIsLim, mertens,
                                infSumNonneg} の 5 公理（exp / expAdd / expSeries 消滅）
      gaussianRbfD_eq_gaussKernelD / rbfGaussSymmD / gramRbfSym : exp フリー
      （インフラ公理のみ。ブリッジ自体も conv / mertens に依存しない）

  → 追記評価16 (B) の「RBF ブリッジには exp 依存が構造的に残る」は、
    (C) の RBFD 再定義により RBF 名義の PSD チェーンから解消された。
    exp 依存は「exp 版 gaussianRbf 自体の理論（RBF.lean）」のみに残る
    （表現子系は追記評価19 で D ワールド化して解消）。
  ============================================================================
-/

/-
  ============================================================================
  追記評価19: 表現子系・kernelCenter の D ワールド化（追記評価16 (C) の実装 2）
  ============================================================================

  実施内容:
    · 表現子系（representer / featureMap / representerAsFeatures / gaussEqShift /
      representerShiftInvariant）と kernelCenter を D ワールド版カーネル
      gaussKernelD に切替（probe /tmp/eval19_probe.lean で検証、namespace Eval19、
      EXIT 0）。kernelCenter は BinomTaylor.expZeroD（公理なしで導出済み）を
      使用するため infSumIsLim に依存するが、exp 公理はゼロ。
    · 切替により孤児化した exp ワールド宣言（rbfGaussEq / gaussSymm / kernelSym /
      expPos / kernelPos / expMonotone / kernelLeOne、およびブリッジ補題 absSqr /
      negSub / sqrSym）は RBF.lean へ移設（exp 理論の住処への集約。KernelLearn は
      RBF.absSqr / RBF.sqrSym を参照）。

  検証（#print axioms 実測、probe /tmp/eval19_probe.lean）:
      kernelCenter / gaussianRbfDShiftInvariant / gaussEqShift / representerEval /
      representerAsFeatures / representerShiftInvariant : exp 系ゼロ
      （kernelCenter のみ expZeroD 経由で infSumIsLim に依存）
      gramNonneg / gramRbfNonneg / rbfPsd / gramSym / gramRbfSym : 不変（5 / 0）

  → KernelLearn の exp 依存は完全消滅。残存 exp 範囲は「RBF.lean の exp 理論
    （gaussianRbf と exp 版基本性質）」のみ。
  ============================================================================
-/
end KernelLearn
