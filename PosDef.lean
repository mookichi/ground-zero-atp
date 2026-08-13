import GroundZero

/-
  ============================================================================
  正定値性（positive definiteness）の形式化評価
  ============================================================================

  目的: ガウス RBF カーネル K(x, y) = exp(-ε²·ρ(x,y)²) の正定値性
        （任意の有限点集合 x₁..xₙ と係数 c₁..cₙ について
         Σᵢⱼ cᵢ cⱼ K(xᵢ, xⱼ) ≥ 0）がどこまで形式化できるかを評価する。

  このファイルで完全に形式化するもの:
    1. 有限和 sum（Nat.rec による）と基本補題（外延性・定数のくくり出し・
       二重和の交換則 sumSwap（有限 Fubini）・双線型形式 biForm の対称性
       biFormSymI（IsSymmetric 型クラス版）— 核行列 G = Gᵀ の原型）
    2. 2次形式 quadForm と正半定値性 PSD の定義
    3. ランク1カーネル K(x,y) = f x · f y の PSD（Σᵢⱼ の平方分解 + 0 ≤ s²）
    4. PSD の加法閉包性（正定値カーネルの有限和は正定値）

  実装の最終形態（末尾の結論コメント参照）:
    · ガウスカーネル gaussPsd は、exp の級数分解（expSeries）と 2 つの
      実解析公理（infSumNonneg / infSumLin: 収束論）への還元として完成。
      交換則 infSumFinSwap は公理ではなく infSumLin から導出される定理。
    · 追記評価2/3: 2公理の sup（Dedekind 完備性）ベースの導出可能性を評価。
      sup 版の infSumNonneg は導出可能だが、交換則 infSumFinSwap は導出不能。
      さらに交代系列の反例（alt.supNeEventual / seriesNegNotSwap）が示す
      ように、infiniteSum の sup への「置き換え」は振動するガウス級数には
      使えない（単調な操作との交換は sumMonotone / supMonotone で確認）。
    · 追記評価4（最終形）: 交換則 infSumFinSwap は公理ではなく、「極限の
      線型性」infSumLin（無限和は線形汎関数）から導出される定理に格下げ
      された。gaussPsd の系列公理は {expSeries, infSumNonneg, infSumLin} の
      3つ（数は同じ、強さは最小標準形）。ライブラリ全体の公理数は ±0。
      収束仮定付きの infSumLin にはできない: ガウス級数は xy < 0 で交代系列
      （追記評価3 の alt 反例）となり、いかなる sup ベースの収束条件も
      満たさない。
    · 追記評価5: exp を級数で再定義すれば expSeries は公理から外れるが、
      expAdd の導出には無限コーシー積 cauchyProduct（任意の列）が必要。
      exp ブロックは {exp, expZero, expAdd, expSeries} の 4公理から
      {expZero, cauchyProduct} の 2公理に減るが、cauchyProduct は置き換えた
      公理より強い「一般化」である（絶対収束理論への布石。詳細は末尾参照）。
    · 追記評価6（統合済み）: コーシー列・極限の最小理論（ε-N 収束 conv・
      infSumIsLim・mertens）を PosDef に統合。infSumLinD（線型性の吸収）は
      {infSumIsLim} のみ、cauchyProductLim（コーシー積の定理化）は
      {infSumIsLim, mertens} に依存（#print axioms 実測）。ただし infSumIsLim
      は「収束 → 極限同定」の方向のみで、無条件形の infSumLin 公理は残る。
      gaussPsd の実解析公理 {expZero, infSumNonneg, infSumIsLim, mertens} への
      収束は exp の級数再定義（追記評価5）+ 絶対収束理論が前提（詳細は末尾。
      expZero は追記評価9 で定理化され（BinomTaylor.expZeroD）、目標集合は
      {infSumNonneg, infSumIsLim, mertens} + conv 仮説に更新）。
      expD 張り替え版 gaussPsdD（BinomTaylor.lean）では exp 3公理と
      cauchyProduct 公理が消滅し、依存は {convExpD, convAbsExpD, infSumIsLim,
      mertens, infSumLin, infSumNonneg} になる（#print axioms 実測）。
      追記評価7（BinomTaylor.lean）: conv 仮説（convExpD/convAbsExpD）を整備し、
      cauchyProduct 公理を削除して expAddD を cauchyProductLim（定理）に張り替え。
      追記評価8（BinomTaylor.lean）: conv 仮説の定理化を評価。乗法単調性 mulLe・
      facGePowTwo（2ᵏ ≤ (k+1)!）・rpowLeOne を公理ゼロで実証したが、比較判定・
      単調収束の残りは本格実解析として将来課題（convExpD/convAbsExpD は公理のまま）。
      追記評価10（本ファイルの infSumFinSwap 直後セクション）: conv 仮説付き
      有限 Fubini（sumSwapInfConv / infSumFinSwapConv 等、infSumLinD
      {infSumIsLim} のみから導出）を追加。PosDef.gaussPsdD をこれに張り
      替え、依存から infSumLin 公理を吸収（#print axioms 実測: 5 公理に縮減）。
      追記評価11: expD / expDSeries / convExpD / convAbsExpD を BinomTaylor.lean
      から本ファイルの Stage D′ へ移設（棚卸しの除去経路①）。BinomTaylor は
      open PosDef で短縮名参照し、依存循環を解消。gaussPsdD の公理 5 つは
      不変（公理名のみ PosDef. 接頭辞に移動、#print axioms 実測）。
      追記評価12: BinomTaylor.lean の二項定理チェーン（nCr ... binomTaylor）・
      expAddD・D ワールド gaussPsdD を本ファイルへ統合（除去経路②）。gaussPsdD
      が PosDef 層に揃い、依存は {convExpD, convAbsExpD, infSumIsLim, mertens,
      infSumNonneg} の 5 公理（exp ブロック・infSumLin 非依存、#print axioms
      実測）。チェーンの Nat 補題 subSelf は ℝ 版と衝突するため nSubSelf に改名。
      追記評価13: 演習問題の追加（Exercises）。
      追記評価14（除去経路③④完結）: exp ワールド gaussPsd と infSumLin を削除。
      gaussPsdDE（gaussPsdD + expEqExpD ブリッジ）が exp 版カーネルの PSD を担っていた
      （追記評価17 で削除。役割は KernelLearn.gramNonneg が gaussPsdD を直接適用）。
      infSumLin 公理と派生チェーン 6 件（infSumAdd / infSumScale / infSumZero /
      sumSwapInf / infSumScale2 / infSumFinSwap）、および exp ワールド専用の補助
      （expTriple / gaussDecomp / expMid / gaussKernelSeries）は削除済み。
      expSummand / gaussKernel は残存（D ワールド expMidD と KernelLearn が使用）。
      #print axioms 実測: gaussPsdDE = {convExpD, convAbsExpD, infSumIsLim,
      mertens, infSumNonneg, exp, expAdd, expSeries}（infSumLin 消滅）。
      KernelLearn.gramNonneg / rbfPsd も gaussPsdDE 経由で infSumLin 非依存に。
      追記評価17（追記評価16 (A) の実装）: KernelLearn.gram 系を gaussKernelD に
      切替。gaussPsdDE は削除（PSD は KernelLearn 側で gaussPsdD が直接担う）。
      expEqExpD は RBF ブリッジ（KernelLearn.gaussKernelEqD → rbfGaussEqD）用に
      残置。KernelLearn.gramNonneg は #print axioms 実測で {convExpD, convAbsExpD,
      infSumIsLim, mertens, infSumNonneg} の 5 公理（exp 系ゼロ）に縮減。
      追記評価18（追記評価16 (C) の実装）: RBF.lean に D ワールド版 RBF
      （RBF.gaussianRbfD := expD 版）を追加し、KernelLearn の RBF 名義 PSD
      （rbfPsd / gramRbfNonneg）も exp フリー（5 公理）に。不要化した
      gaussKernelEqD / rbfGaussEqD（exp ブリッジ）は削除。expEqExpD は
      exp と expD の接続補題として保持（使用箇所は消滅）。
  ============================================================================
-/
namespace PosDef

universe u

open GroundZero.Algebra
open GroundZero.Algebra.Group
open GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Proto (explode)
open GroundZero.Theorems.Nat

/-- 有限和: sum n f = f 0 + f 1 + ... + f (n-1) -/
hott definition sum (n : ℕ) (f : ℕ → ℝ) : ℝ :=
@Nat.rec (λ _, ℝ) 0 (λ m r, r + f m) n

/-- 有限和は被加数に対して外延的: f ~ g → Σf = Σg -/
hott lemma sum.ext (n : ℕ) {f g : ℕ → ℝ} (p : Π i, f i = g i) : sum n f = sum n g :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih =>
    exact calc sum (Nat.succ n) f = sum n f + f n : by reflexivity,
         = sum n g + f n     : ap (· + f n) ih,
         = sum n g + g n     : ap (sum n g + ·) (p n),
         = sum (Nat.succ n) g : by reflexivity
end

/-- 2次形式: quadForm K n c x = Σᵢⱼ (c i · c j) · K (x i) (x j) -/
hott definition quadForm {α : Type u} (K : α → α → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → α) : ℝ :=
sum n (λ i, sum n (λ j, (c i * c j) * K (x i) (x j)))

/-- 正半定値性: すべての有限集合・係数について 0 ≤ Σᵢⱼ cᵢ cⱼ K(xᵢ,xⱼ) -/
hott definition PSD {α : Type u} (K : α → α → ℝ) :=
Π n (c : ℕ → ℝ) (x : ℕ → α), R.ρ 0 (quadForm K n c x)

/-- 可換環の「中4交換」: (a·b)·(c·d) = (a·c)·(b·d) -/
hott lemma middleFour (a b c d : ℝ) : (a * b) * (c * d) = (a * c) * (b * d) :=
calc (a * b) * (c * d) = a * (b * (c * d)) : @ring.assoc.mulAssoc R.τ _ a b (c * d),
     = a * ((b * c) * d) : ap (a * ·) (Id.symm (@ring.assoc.mulAssoc R.τ _ b c d)),
     = a * ((c * b) * d) : ap (a * ·) (ap (· * d) (@ring.comm.mulComm R.τ _ b c)),
     = a * (c * (b * d)) : ap (a * ·) (@ring.assoc.mulAssoc R.τ _ c b d),
     = (a * c) * (b * d) : Id.symm (@ring.assoc.mulAssoc R.τ _ a c (b * d))

/-- 定数を右からくくり出す: Σᵢ (f i · b) = (Σᵢ f i) · b -/
hott lemma sumMul (n : ℕ) (f : ℕ → ℝ) (b : ℝ) : sum n (λ i, f i * b) = (sum n f) * b :=
begin
  induction n with
  | zero =>
    exact calc sum 0 (λ i, f i * b) = 0 : by reflexivity,
         = 0 * b : Id.symm (@ring.zeroMul R.τ _ b),
         = (sum 0 f) * b : by reflexivity
  | succ n ih =>
    exact calc sum (Nat.succ n) (λ i, f i * b) = sum n (λ i, f i * b) + f n * b : by reflexivity,
         = (sum n f) * b + f n * b : ap (· + f n * b) ih,
         = (sum n f + f n) * b : Id.symm (@ring.distribRight R.τ _ (sum n f) (f n) b),
         = (sum (Nat.succ n) f) * b : by reflexivity
end

/-- 定数を左からくくり出す: b · (Σᵢ f i) = Σᵢ (b · f i) -/
hott lemma mulSum (b : ℝ) (n : ℕ) (f : ℕ → ℝ) : b * (sum n f) = sum n (λ i, b * f i) :=
begin
  induction n with
  | zero =>
    exact calc b * (sum 0 f) = b * 0 : by reflexivity,
         = 0 : @ring.mulZero R.τ _ b,
         = sum 0 (λ i, b * f i) : by reflexivity
  | succ n ih =>
    exact calc b * (sum (Nat.succ n) f) = b * (sum n f + f n) : by reflexivity,
         = b * (sum n f) + b * f n : @ring.distribLeft R.τ _ b (sum n f) (f n),
         = sum n (λ i, b * f i) + b * f n : ap (· + b * f n) ih,
         = sum (Nat.succ n) (λ i, b * f i) : by reflexivity
end

/-- (a + b) + (c + d) = (a + c) + (b + d)（加法群の可換性） -/
hott lemma addRearr (a b c d : ℝ) : (a + b) + (c + d) = (a + c) + (b + d) :=
calc (a + b) + (c + d) = ((a + b) + c) + d : Id.symm (R.τ⁺.mulAssoc (a + b) c d),
     = (a + (b + c)) + d : ap (· + d) (R.τ⁺.mulAssoc a b c),
     = (a + (c + b)) + d : ap (· + d) (ap (a + ·) (R.τ.addComm b c)),
     = ((a + c) + b) + d : ap (· + d) (Id.symm (R.τ⁺.mulAssoc a c b)),
     = (a + c) + (b + d) : R.τ⁺.mulAssoc (a + c) b d

/-- 和は + に分配する: (Σf) + (Σg) = Σ(f + g) -/
hott lemma sumAdd (n : ℕ) (f g : ℕ → ℝ) : sum n f + sum n g = sum n (λ i, f i + g i) :=
begin
  induction n with
  | zero =>
    exact calc sum 0 f + sum 0 g = 0 + 0 : by reflexivity,
         = 0 : R.τ.addZero (0 : ℝ),
         = sum 0 (λ i, f i + g i) : by reflexivity
  | succ n ih =>
    exact calc sum (Nat.succ n) f + sum (Nat.succ n) g = (sum n f + f n) + (sum n g + g n) : by reflexivity,
         = (sum n f + sum n g) + (f n + g n) : addRearr (sum n f) (f n) (sum n g) (g n),
         = sum n (λ i, f i + g i) + (f n + g n) : ap (· + (f n + g n)) ih,
         = sum (Nat.succ n) (λ i, f i + g i) : by reflexivity
end

/-- 有限和の自明項: Σᵢ 0 = 0 -/
hott lemma sumZero (n : ℕ) : sum n (λ _, 0) = 0 :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih =>
    exact calc sum (Nat.succ n) (λ i, 0) = sum n (λ i, 0) + 0 : by reflexivity,
         = 0 + 0 : ap (· + 0) ih,
         = 0 : R.τ.addZero (0 : ℝ)
end

/--
  有限二重和の交換則（有限 Fubini）: Σᵢ Σⱼ f i j = Σⱼ Σᵢ f i j。
  二重和の総和順序の入れ替え（矩形領域上の Fubini）であり、
  核行列の対称性・グラム行列の転置などの基盤となる。
-/
hott lemma sumSwap (n m : ℕ) (f : ℕ → ℕ → ℝ) :
  sum n (λ i, sum m (λ j, f i j)) = sum m (λ j, sum n (λ i, f i j)) :=
begin
  induction n with
  | zero =>
    exact calc sum 0 (λ i, sum m (λ j, f i j)) = 0 : by reflexivity,
         = sum m (λ j, 0) : Id.symm (sumZero m),
         = sum m (λ j, sum 0 (λ i, f i j)) : Id.symm (sum.ext m (λ j, by reflexivity))
  | succ n ih =>
    exact calc sum (Nat.succ n) (λ i, sum m (λ j, f i j))
             = sum n (λ i, sum m (λ j, f i j)) + sum m (λ j, f n j) : by reflexivity,
         = sum m (λ j, sum n (λ i, f i j)) + sum m (λ j, f n j) : ap (· + sum m (λ j, f n j)) ih,
         = sum m (λ j, sum n (λ i, f i j) + f n j) : sumAdd m (λ j, sum n (λ i, f i j)) (λ j, f n j),
         = sum m (λ j, sum (Nat.succ n) (λ i, f i j)) : sum.ext m (λ j, by reflexivity)
end

/-- 双線型形式（グラム形式）: biForm K n c d x = Σᵢⱼ (c i · d j) · K(xᵢ,xⱼ)。quadForm の双線型版 -/
hott definition biForm {α : Type u} (K : α → α → ℝ) (n : ℕ) (c d : ℕ → ℝ) (x : ℕ → α) : ℝ :=
sum n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j)))

/-- 対称カーネルの積は添字の入れ替えに対して不変: (c j * d i)·K(xⱼ,xᵢ) = (d i * c j)·K(xᵢ,xⱼ) -/
hott lemma biFormSwapInner {α : Type u} (K : α → α → ℝ) (kSym : Π a b, K a b = K b a)
  (c d : ℕ → ℝ) (x : ℕ → α) (i j : ℕ) :
  (c j * d i) * K (x j) (x i) = (d i * c j) * K (x i) (x j) :=
calc (c j * d i) * K (x j) (x i)
     = (d i * c j) * K (x j) (x i) : ap (λ z, z * K (x j) (x i)) (@ring.comm.mulComm R.τ _ (c j) (d i)),
     = (d i * c j) * K (x i) (x j) : ap (λ z, (d i * c j) * z) (kSym (x j) (x i))

/--
  双線型形式レベルの対称性（sumSwap の応用）: カーネル K が IsSymmetric 型クラス
  （Meta/Symm.lean の関数レベル対称性、k a b = k b a の経路）を満たせば、
  グラム形式は係数に関して対称: Σᵢⱼ cᵢ dⱼ K(xᵢ,xⱼ) = Σᵢⱼ dᵢ cⱼ K(xᵢ,xⱼ)。
  核行列 G の対称性 G = Gᵀ の原型。対称性の証明は型クラスで自動供給される。

  インスタンス登録なしの一回限りの対称カーネルには、下位レベルの
  biFormSwapInner（明示 witness 版）がエスケープハッチとして使える。
-/
hott theorem biFormSymI {α : Type u} (K : α → α → ℝ) [inst : IsSymmetric K]
  (n : ℕ) (c d : ℕ → ℝ) (x : ℕ → α) : biForm K n c d x = biForm K n d c x :=
begin
  unfold biForm;
  exact calc sum n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j)))
       = sum n (λ j, sum n (λ i, (c i * d j) * K (x i) (x j))) : sumSwap n n (λ i, λ j, (c i * d j) * K (x i) (x j)),
       = sum n (λ i, sum n (λ j, (c j * d i) * K (x j) (x i))) : by reflexivity,
       = sum n (λ i, sum n (λ j, (d i * c j) * K (x i) (x j))) : sum.ext n (λ i, sum.ext n (λ j, biFormSwapInner K inst.symm c d x i j))
end

/-- 非負の項の有限和は非負: 0 ≤ f i（∀i）なら 0 ≤ Σf -/
hott lemma sumNonneg (n : ℕ) (f : ℕ → ℝ) (p : Π i, R.ρ 0 (f i)) : R.ρ 0 (sum n f) :=
begin
  induction n with
  | zero => apply @reflexive.refl R.κ
  | succ n ih =>
    exact Equiv.transport (λ z, R.ρ z (sum n f + f n)) (R.τ.addZero (0 : ℝ))
      (ineqAdd R ih (p n))
end

/-- 双線型形式は第1引数について加法性: B(c+d, e) = B(c,e) + B(d,e) -/
hott lemma biFormAddLeft {α : Type u} (K : α → α → ℝ) (n : ℕ) (c d e : ℕ → ℝ) (x : ℕ → α) :
  biForm K n (λ i, c i + d i) e x = biForm K n c e x + biForm K n d e x :=
begin
  unfold biForm;
  exact calc sum n (λ i, sum n (λ j, ((c i + d i) * e j) * K (x i) (x j)))
       = sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j) + (d i * e j) * K (x i) (x j))) : sum.ext n (λ i, sum.ext n (λ j,
           calc ((c i + d i) * e j) * K (x i) (x j)
                = (c i * e j + d i * e j) * K (x i) (x j) : ap (· * K (x i) (x j)) (@ring.distribRight R.τ _ (c i) (d i) (e j)),
                = (c i * e j) * K (x i) (x j) + (d i * e j) * K (x i) (x j) : @ring.distribRight R.τ _ (c i * e j) (d i * e j) (K (x i) (x j)))),
       = sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j)) + sum n (λ j, (d i * e j) * K (x i) (x j))) : sum.ext n (λ i, Id.symm (sumAdd n (λ j, (c i * e j) * K (x i) (x j)) (λ j, (d i * e j) * K (x i) (x j)))),
       = sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))) + sum n (λ i, sum n (λ j, (d i * e j) * K (x i) (x j))) : Id.symm (sumAdd n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))) (λ i, sum n (λ j, (d i * e j) * K (x i) (x j))))
end

/-- 双線型形式は第2引数について加法性: B(c, d+e) = B(c,d) + B(c,e) -/
hott lemma biFormAddRight {α : Type u} (K : α → α → ℝ) (n : ℕ) (c d e : ℕ → ℝ) (x : ℕ → α) :
  biForm K n c (λ i, d i + e i) x = biForm K n c d x + biForm K n c e x :=
begin
  unfold biForm;
  exact calc sum n (λ i, sum n (λ j, (c i * (d j + e j)) * K (x i) (x j)))
       = sum n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j) + (c i * e j) * K (x i) (x j))) : sum.ext n (λ i, sum.ext n (λ j,
           calc (c i * (d j + e j)) * K (x i) (x j)
                = (c i * d j + c i * e j) * K (x i) (x j) : ap (· * K (x i) (x j)) (@ring.distribLeft R.τ _ (c i) (d j) (e j)),
                = (c i * d j) * K (x i) (x j) + (c i * e j) * K (x i) (x j) : @ring.distribRight R.τ _ (c i * d j) (c i * e j) (K (x i) (x j)))),
       = sum n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j)) + sum n (λ j, (c i * e j) * K (x i) (x j))) : sum.ext n (λ i, Id.symm (sumAdd n (λ j, (c i * d j) * K (x i) (x j)) (λ j, (c i * e j) * K (x i) (x j)))),
       = sum n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j))) + sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))) : Id.symm (sumAdd n (λ i, sum n (λ j, (c i * d j) * K (x i) (x j))) (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))))
end

/-- 双線型形式は第1引数について斉次: B(t·c, e) = t·B(c,e) -/
hott lemma biFormMulLeft {α : Type u} (K : α → α → ℝ) (n : ℕ) (t : ℝ) (c e : ℕ → ℝ) (x : ℕ → α) :
  biForm K n (λ i, t * c i) e x = t * biForm K n c e x :=
begin
  unfold biForm;
  exact calc sum n (λ i, sum n (λ j, ((t * c i) * e j) * K (x i) (x j)))
       = sum n (λ i, sum n (λ j, t * ((c i * e j) * K (x i) (x j)))) : sum.ext n (λ i, sum.ext n (λ j,
           calc ((t * c i) * e j) * K (x i) (x j)
                = (t * (c i * e j)) * K (x i) (x j) : ap (· * K (x i) (x j)) (@ring.assoc.mulAssoc R.τ _ t (c i) (e j)),
                = t * ((c i * e j) * K (x i) (x j)) : @ring.assoc.mulAssoc R.τ _ t (c i * e j) (K (x i) (x j)))),
       = sum n (λ i, t * sum n (λ j, (c i * e j) * K (x i) (x j))) : sum.ext n (λ i, Id.symm (mulSum t n (λ j, (c i * e j) * K (x i) (x j)))),
       = t * sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))) : Id.symm (mulSum t n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))))
end

/-- 双線型形式は第2引数について斉次: B(c, t·e) = t·B(c,e) -/
hott lemma biFormMulRight {α : Type u} (K : α → α → ℝ) (n : ℕ) (t : ℝ) (c e : ℕ → ℝ) (x : ℕ → α) :
  biForm K n c (λ i, t * e i) x = t * biForm K n c e x :=
begin
  unfold biForm;
  exact calc sum n (λ i, sum n (λ j, (c i * (t * e j)) * K (x i) (x j)))
       = sum n (λ i, sum n (λ j, t * ((c i * e j) * K (x i) (x j)))) : sum.ext n (λ i, sum.ext n (λ j,
           calc (c i * (t * e j)) * K (x i) (x j)
                = (t * (c i * e j)) * K (x i) (x j) : ap (· * K (x i) (x j))
                    (calc c i * (t * e j) = (c i * t) * e j : Id.symm (@ring.assoc.mulAssoc R.τ _ (c i) t (e j)),
                         = (t * c i) * e j : ap (· * e j) (@ring.comm.mulComm R.τ _ (c i) t),
                         = t * (c i * e j) : @ring.assoc.mulAssoc R.τ _ t (c i) (e j)),
                = t * ((c i * e j) * K (x i) (x j)) : @ring.assoc.mulAssoc R.τ _ t (c i * e j) (K (x i) (x j)))),
       = sum n (λ i, t * sum n (λ j, (c i * e j) * K (x i) (x j))) : sum.ext n (λ i, Id.symm (mulSum t n (λ j, (c i * e j) * K (x i) (x j)))),
       = t * sum n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))) : Id.symm (mulSum t n (λ i, sum n (λ j, (c i * e j) * K (x i) (x j))))
end

/-- 順序体: 平方は非負 0 ≤ s·s（全順序を場合分け + leOverMul） -/
hott lemma sqrNonneg (s : ℝ) : R.ρ 0 (s * s) :=
begin
  match R.total 0 s with
  | Sum.inl p => { exact orfield.leOverMul s s p p }
  | Sum.inr q => {
      apply Equiv.transport (R.ρ 0);
      exact @ring.mulNeg R.τ _ (-s) s ⬝ ap (λ z, -z) (@ring.negMul R.τ _ s s) ⬝ @Group.invInv R.τ⁺ (s * s);
      apply orfield.leOverMul (-s) (-s);
      apply R.zeroGeImplZeroLeMinus q.2;
      apply R.zeroGeImplZeroLeMinus q.2 }
end

/-- 2-ノルムの平方: normSq n v = Σᵢ vᵢ·vᵢ -/
hott definition normSq (n : ℕ) (v : ℕ → ℝ) : ℝ := sum n (λ i, v i * v i)

/-- 二乗ノルムは非負: 0 ≤ ‖v‖² -/
hott lemma normSqNonneg (n : ℕ) (v : ℕ → ℝ) : R.ρ 0 (normSq n v) :=
sumNonneg n (λ i, v i * v i) (λ i, sqrNonneg (v i))

/-- 1 - (1 - t) = t -/
hott lemma oneSubSub (t : ℝ) : 1 - (1 - t) = t :=
calc 1 - (1 - t) = 1 + (-(1 + -t)) : by reflexivity,
     = 1 + ((-1) + t) : ap (1 + ·) (negAdd (1 : ℝ) (-t) ⬝ ap ((-1 : ℝ) + ·) (@Group.invInv R.τ⁺ t)),
     = (1 + (-1)) + t : Id.symm (R.τ.addAssoc (1 : ℝ) (-1 : ℝ) t),
     = 0 + t : ap (· + t) (R.τ.addComm (1 : ℝ) (-1 : ℝ) ⬝ R.τ.addLeftNeg (1 : ℝ)),
     = t : R.τ.zeroAdd t

/-- t + (1 - t) = 1 -/
hott lemma addSubSelf (t : ℝ) : t + (1 - t) = 1 :=
calc t + (1 - t) = t + (1 + (-t)) : by reflexivity,
     = (t + 1) + (-t) : Id.symm (R.τ.addAssoc t (1 : ℝ) (-t)),
     = (1 + t) + (-t) : ap (· + (-t)) (R.τ.addComm t (1 : ℝ)),
     = 1 + (t + (-t)) : R.τ.addAssoc (1 : ℝ) t (-t),
     = 1 + 0 : ap (1 + ·) (R.τ.addComm t (-t) ⬝ R.τ.addLeftNeg t),
     = 1 : R.τ.addZero (1 : ℝ)

/-- 係数: t - t·t = t·(1-t) -/
hott lemma subSq (t : ℝ) : t - t * t = t * (1 - t) :=
calc t - t * t = t * 1 - t * t : ap (· - t * t) (Id.symm (@ring.monoid.mulOne R.τ _ t)),
     = t * (1 - t) : Id.symm (@ring.subDistribLeft R.τ _ t (1 : ℝ) t)

/-- 係数: (1-t) - (1-t)·(1-t) = t·(1-t) -/
hott lemma subSqOne (t : ℝ) : (1 - t) - (1 - t) * (1 - t) = t * (1 - t) :=
calc (1 - t) - (1 - t) * (1 - t) = (1 - t) * 1 - (1 - t) * (1 - t) : ap (· - (1 - t) * (1 - t)) (Id.symm (@ring.monoid.mulOne R.τ _ ((1 : ℝ) - t))),
     = (1 - t) * (1 - (1 - t)) : Id.symm (@ring.subDistribLeft R.τ _ ((1 : ℝ) - t) (1 : ℝ) ((1 : ℝ) - t)),
     = (1 - t) * t : ap (((1 : ℝ) - t) * ·) (oneSubSub t),
     = t * (1 - t) : @ring.comm.mulComm R.τ _ ((1 : ℝ) - t) t

/-- 分配展開: (x + y)² = x² + y² + (xy + yx) -/
hott lemma squareSum (x y : ℝ) :
  (x + y) * (x + y) = x * x + y * y + (x * y + y * x) :=
calc (x + y) * (x + y) = x * (x + y) + y * (x + y) : @ring.distribRight R.τ _ x y (x + y),
     = (x * x + x * y) + (y * (x + y)) : ap (· + y * (x + y)) (@ring.distribLeft R.τ _ x x y),
     = (x * x + x * y) + (y * x + y * y) : ap ((x * x + x * y) + ·) (@ring.distribLeft R.τ _ y x y),
     = (x * x + x * y) + (y * y + y * x) : ap ((x * x + x * y) + ·) (R.τ.addComm (y * x) (y * y)),
     = x * x + y * y + (x * y + y * x) : addRearr (x * x) (x * y) (y * y) (y * x)

/-- (x - z) - (y - w) = x - z - y + w（negAdd の再グループ化） -/
hott lemma subSubAdd (x z y w : ℝ) : (x - z) - (y - w) = x - z - y + w :=
calc (x - z) - (y - w) = (x + -z) + (-(y + -w)) : by reflexivity,
     = (x + -z) + (-y + -(-w)) : ap ((x + -z) + ·) (negAdd y (-w)),
     = (x + -z) + (-y + w) : ap ((x + -z) + ·) (ap (-y + ·) (@Group.invInv R.τ⁺ w)),
     = ((x + -z) + -y) + w : Id.symm (R.τ.addAssoc (x + -z) (-y) w),
     = x - z - y + w : by reflexivity

/-- 差の二乗の展開: (a - b)² = a² - ab - ab + b² -/
hott lemma squareDiff (a b : ℝ) : (a - b) * (a - b) = a * a - a * b - a * b + b * b :=
calc (a - b) * (a - b) = a * (a - b) - b * (a - b) : @ring.subDistribRight R.τ _ a b (a - b),
     = (a * a - a * b) - b * (a - b) : ap (· - b * (a - b)) (@ring.subDistribLeft R.τ _ a a b),
     = (a * a - a * b) - (b * a - b * b) : ap ((a * a - a * b) - ·) (@ring.subDistribLeft R.τ _ b a b),
     = a * a - a * b - b * a + b * b : subSubAdd (a * a) (a * b) (b * a) (b * b),
     = a * a - a * b - a * b + b * b : ap (λ w, (a * a - a * b + w) + b * b) (ap (λ z, -z) (@ring.comm.mulComm R.τ _ b a))

/-- 割線の二乗の展開: (t·a + (1-t)·b)² = t²·a² + (1-t)²·b² + t(1-t)·(ab + ab)
   ※ hott の +/* は型レベル（Coproduct/Product）ともオーバーロードされるため、
     交叉項の `+` には ( : ℝ) 注釈が必要（numeral 1 が含まれる式で発動）。 -/
hott lemma squareTA (t a b : ℝ) :
  (t * a + (1 - t) * b) * (t * a + (1 - t) * b) =
  (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) +
  ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ) :=
begin
  exact calc (t * a + (1 - t) * b) * (t * a + (1 - t) * b)
       = (t * a) * (t * a) + ((1 - t) * b) * ((1 - t) * b) + ((t * a) * ((1 - t) * b) + ((1 - t) * b) * (t * a) : ℝ) : squareSum (t * a) ((1 - t) * b),
       = (t * t) * (a * a) + ((1 - t) * b) * ((1 - t) * b) + ((t * a) * ((1 - t) * b) + ((1 - t) * b) * (t * a) : ℝ) : ap (fun u : ℝ => u + ((1 - t) * b) * ((1 - t) * b) + ((t * a) * ((1 - t) * b) + ((1 - t) * b) * (t * a) : ℝ)) (middleFour t a t a),
       = (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + ((t * a) * ((1 - t) * b) + ((1 - t) * b) * (t * a) : ℝ) : ap (fun v : ℝ => (t * t) * (a * a) + v + ((t * a) * ((1 - t) * b) + ((1 - t) * b) * (t * a) : ℝ)) (middleFour ((1 : ℝ) - t) b ((1 : ℝ) - t) b),
       = (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + ((t * (1 - t)) * (a * b) + ((1 - t) * b) * (t * a) : ℝ) : ap (fun w : ℝ => (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + (w + ((1 - t) * b) * (t * a) : ℝ)) (middleFour t a ((1 : ℝ) - t) b),
       = (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ) : ap (fun z : ℝ => (t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + ((t * ((1 : ℝ) - t)) * (a * b) + z : ℝ))
           (calc ((1 - t) * b) * (t * a) = (((1 : ℝ) - t) * t) * (b * a) : middleFour ((1 : ℝ) - t) b t a,
                = (((1 : ℝ) - t) * t) * (a * b) : ap (λ q, (((1 : ℝ) - t) * t) * q) (@ring.comm.mulComm R.τ _ b a),
                = (t * ((1 : ℝ) - t)) * (a * b) : ap (λ q, q * (a * b)) (@ring.comm.mulComm R.τ _ ((1 : ℝ) - t) t))
end

/-- 括弧の分配: a - (b + c) = a - b - c -/
hott lemma subAddSub (a b c : ℝ) : a - (b + c) = a - b - c :=
calc a - (b + c) = a + (-(b + c)) : by reflexivity,
     = a + (-b + -c) : ap (a + ·) (negAdd b c),
     = (a + (-b)) + (-c) : Id.symm (R.τ.addAssoc a (-b) (-c)),
     = a - b - c : by reflexivity

/-- 差の再グループ化: a + b - c - d = (a - c) + (b - d) -/
hott lemma subRegroup4 (a b c d : ℝ) : a + b - c - d = (a - c) + (b - d) :=
calc a + b - c - d = ((a + b) + (-c)) + (-d) : by reflexivity,
     = (a + b) + (-c + -d) : R.τ.addAssoc (a + b) (-c) (-d),
     = (a + (-c)) + (b + (-d)) : addRearr a b (-c) (-d),
     = (a - c) + (b - d) : by reflexivity

/-- 差の再グループ化（6項）: a + b - c - d - e - f = (a - c) + (b - d) - e - f -/
hott lemma subRegroup6 (a b c d e f : ℝ) :
  a + b - c - d - e - f = (a - c) + (b - d) - e - f :=
ap (λ z, z - e - f) (subRegroup4 a b c d)

/-- (x - z) + (y - z) = x - z - z + y -/
hott lemma addSubSub2 (x z y : ℝ) : (x - z) + (y - z) = x - z - z + y :=
calc (x - z) + (y - z) = (x + -z) + (y + -z) : by reflexivity,
     = (x + y) + (-z + -z) : addRearr x (-z) y (-z),
     = x + (y + (-z + -z)) : R.τ.addAssoc x y (-z + -z),
     = x + ((-z + -z) + y) : ap (x + ·) (R.τ.addComm y (-z + -z)),
     = (x + (-z + -z)) + y : Id.symm (R.τ.addAssoc x (-z + -z) y),
     = ((x + -z) + -z) + y : ap (· + y) (Id.symm (R.τ.addAssoc x (-z) (-z))),
     = x - z - z + y : by reflexivity

/-- 和と符号: Σ (-f i) = -Σ f i -/
hott lemma sumNeg (n : ℕ) (f : ℕ → ℝ) : sum n (λ i, -f i) = -(sum n f) :=
calc sum n (λ i, -f i) = sum n (λ i, f i * (-1)) : sum.ext n (λ i, Id.symm (@ring.mulNeg R.τ _ (f i) (1 : ℝ) ⬝ ap (λ z, -z) (@ring.monoid.mulOne R.τ _ (f i)))),
     = (sum n f) * (-1) : sumMul n f (-1 : ℝ),
     = -(sum n f) : @ring.mulNeg R.τ _ (sum n f) (1 : ℝ) ⬝ ap (λ z, -z) (@ring.monoid.mulOne R.τ _ (sum n f))

/-- 和の差: Σ (f - g) = Σf - Σg -/
hott lemma sumSub (n : ℕ) (f g : ℕ → ℝ) : sum n (λ i, f i - g i) = sum n f - sum n g :=
calc sum n (λ i, f i - g i) = sum n (λ i, f i + -g i) : by reflexivity,
     = sum n f + sum n (λ i, -g i) : Id.symm (sumAdd n f (λ i, -g i)),
     = sum n f - sum n g : ap (sum n f + ·) (sumNeg n g)

/-- スカラー凸性恒等式: t·a² + (1-t)·b² - (t·a + (1-t)·b)² = t(1-t)·(a-b)² -/
hott lemma scalarDiff (t a b : ℝ) :
  t * (a * a) + (1 - t) * (b * b) - (t * a + (1 - t) * b) * (t * a + (1 - t) * b) =
  t * (1 - t) * ((a - b) * (a - b)) :=
begin
  exact calc t * (a * a) + (1 - t) * (b * b) - (t * a + (1 - t) * b) * (t * a + (1 - t) * b)
       = t * (a * a) + (1 - t) * (b * b) - ((t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b) + ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ)) : ap (fun u : ℝ => t * (a * a) + (1 - t) * (b * b) - u) (squareTA t a b),
       = t * (a * a) + (1 - t) * (b * b) - (t * t) * (a * a) - ((1 - t) * (1 - t)) * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) :            (calc t * (a * a) + (1 - t) * (b * b) - (((t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b)) + ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ))
                 = t * (a * a) + (1 - t) * (b * b) - ((t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b)) - ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ) : subAddSub (t * (a * a) + (1 - t) * (b * b)) ((t * t) * (a * a) + ((1 - t) * (1 - t)) * (b * b)) ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b)),
                 = t * (a * a) + (1 - t) * (b * b) - (t * t) * (a * a) - ((1 - t) * (1 - t)) * (b * b) - ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ) : ap (fun w : ℝ => w - ((t * (1 - t)) * (a * b) + (t * (1 - t)) * (a * b) : ℝ)) (subAddSub (t * (a * a) + (1 - t) * (b * b)) ((t * t) * (a * a)) (((1 - t) * (1 - t)) * (b * b))),
                 = t * (a * a) + (1 - t) * (b * b) - (t * t) * (a * a) - ((1 - t) * (1 - t)) * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : subAddSub (t * (a * a) + (1 - t) * (b * b) - (t * t) * (a * a) - ((1 - t) * (1 - t)) * (b * b)) ((t * (1 - t)) * (a * b)) ((t * (1 - t)) * (a * b))),
       = (t * (a * a) - (t * t) * (a * a)) + ((1 - t) * (b * b) - ((1 - t) * (1 - t)) * (b * b)) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : subRegroup6 (t * (a * a)) ((1 - t) * (b * b)) ((t * t) * (a * a)) (((1 - t) * (1 - t)) * (b * b)) ((t * (1 - t)) * (a * b)) ((t * (1 - t)) * (a * b)),        = (t - t * t) * (a * a) + ((1 - t) * (b * b) - ((1 - t) * (1 - t)) * (b * b)) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : ap (fun u : ℝ => u + ((1 - t) * (b * b) - ((1 - t) * (1 - t)) * (b * b)) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b)) (Id.symm (@ring.subDistribRight R.τ _ t (t * t) (a * a))),
        = (t - t * t) * (a * a) + ((1 - t) - (1 - t) * (1 - t)) * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : ap (fun v : ℝ => (t - t * t) * (a * a) + v - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b)) (Id.symm (@ring.subDistribRight R.τ _ ((1 : ℝ) - t) (((1 : ℝ) - t) * ((1 : ℝ) - t)) (b * b))),
        = (t * (1 - t)) * (a * a) + (((1 : ℝ) - t) - ((1 : ℝ) - t) * ((1 : ℝ) - t)) * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : ap (fun u : ℝ => u * (a * a) + (((1 : ℝ) - t) - ((1 : ℝ) - t) * ((1 : ℝ) - t)) * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b)) (subSq t),
        = (t * (1 - t)) * (a * a) + ((t * (1 - t)) * (b * b) : ℝ) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b) : ap (fun v : ℝ => (t * (1 - t)) * (a * a) + v * (b * b) - (t * (1 - t)) * (a * b) - (t * (1 - t)) * (a * b)) (subSqOne t),
        = ((t * (1 - t)) * (a * a) - (t * (1 - t)) * (a * b)) + ((t * (1 - t)) * (b * b) - (t * (1 - t)) * (a * b)) : subRegroup4 ((t * (1 - t)) * (a * a)) ((t * (1 - t)) * (b * b)) ((t * (1 - t)) * (a * b)) ((t * (1 - t)) * (a * b)),
        = (t * (1 - t)) * (a * a - a * b) + (t * (1 - t)) * (b * b - a * b) :
            ap ((t * ((1 : ℝ) - t)) * (a * a) - (t * ((1 : ℝ) - t)) * (a * b) + ·) (Id.symm (@ring.subDistribLeft R.τ _ (t * ((1 : ℝ) - t)) (b * b) (a * b))) ⬝
            ap (· + (t * ((1 : ℝ) - t)) * (b * b - a * b)) (Id.symm (@ring.subDistribLeft R.τ _ (t * ((1 : ℝ) - t)) (a * a) (a * b))),
        = (t * (1 - t)) * ((a * a - a * b) + (b * b - a * b)) : Id.symm (@ring.distribLeft R.τ _ (t * ((1 : ℝ) - t)) (a * a - a * b) (b * b - a * b)),
        = (t * (1 - t)) * (a * a - a * b - a * b + b * b) : ap ((t * (1 - t)) * ·) (addSubSub2 (a * a) (a * b) (b * b)),
        = t * (1 - t) * ((a - b) * (a - b)) : ap ((t * (1 - t)) * ·) (Id.symm (squareDiff a b))
end

/-- 二乗ノルムの差の分解: t·‖a‖² + (1-t)·‖b‖² - ‖t·a + (1-t)·b‖² = t(1-t)·‖a-b‖² -/
hott lemma normSqDiff (n : ℕ) (t : ℝ) (a b : ℕ → ℝ) :
  t * normSq n a + (1 - t) * normSq n b - normSq n (λ i, t * a i + (1 - t) * b i) =
  t * (1 - t) * normSq n (λ i, a i - b i) :=
begin
  unfold normSq;
  exact calc t * sum n (λ i, a i * a i) + (1 - t) * sum n (λ i, b i * b i) - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i))
       = sum n (λ i, t * (a i * a i) + (1 - t) * (b i * b i) - (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)) :
           Id.symm (calc sum n (λ i, t * (a i * a i) + (1 - t) * (b i * b i) - (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i))
                = sum n (λ i, t * (a i * a i) + (1 - t) * (b i * b i)) - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)) : sumSub n (λ i, t * (a i * a i) + (1 - t) * (b i * b i)) (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)),                 = (sum n (λ i, t * (a i * a i)) + sum n (λ i, (1 - t) * (b i * b i))) - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)) : ap (· - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i))) (Id.symm (sumAdd n (λ i, t * (a i * a i)) (λ i, (1 - t) * (b i * b i)))),
                = (t * sum n (λ i, a i * a i) + sum n (λ i, (1 - t) * (b i * b i))) - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)) : ap (· - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i))) (ap (· + sum n (λ i, (1 - t) * (b i * b i))) (Id.symm (mulSum t n (λ i, a i * a i)))),
                = (t * sum n (λ i, a i * a i) + (1 - t) * sum n (λ i, b i * b i)) - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i)) : ap (· - sum n (λ i, (t * a i + (1 - t) * b i) * (t * a i + (1 - t) * b i))) (ap (t * sum n (λ i, a i * a i) + ·) (Id.symm (mulSum (1 - t) n (λ i, b i * b i))))),
       = sum n (λ i, t * (1 - t) * ((a i - b i) * (a i - b i))) : sum.ext n (λ i, scalarDiff t (a i) (b i)),
       = t * (1 - t) * sum n (λ i, (a i - b i) * (a i - b i)) : Id.symm (mulSum (t * (1 - t)) n (λ i, (a i - b i) * (a i - b i)))
end

/-- 二乗ノルムの凸性: 0 ≤ t ≤ 1 なら ‖t·a + (1-t)·b‖² ≤ t·‖a‖² + (1-t)·‖b‖² -/
hott lemma normSqConvex (n : ℕ) (t : ℝ) (a b : ℕ → ℝ) (ht0 : R.ρ 0 t) (ht1 : R.ρ t 1) :
  R.ρ (normSq n (λ i, t * a i + (1 - t) * b i)) (t * normSq n a + (1 - t) * normSq n b) :=
begin
  apply leIfSubGeZero R;
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (normSqDiff n t a b);
  apply orfield.leOverMul;
  apply orfield.leOverMul; exact ht0; apply subGeZeroIfLe R; exact ht1;
  apply normSqNonneg
end

/-- 加法群の単位は 0（Prering.additive を展開すると定義的に一致） -/
hott lemma additiveUnit : R.τ⁺.e = (0 : ℝ) := by unfold Prering.additive; reflexivity

/-- 狭義の 0 < 1 -/
hott lemma zeroLtOne : 0 < (1 : ℝ) :=
⟨λ p, @field.nontrivial R.τ _ (Id.symm p ⬝ Id.symm additiveUnit), oneGtZero R⟩

/-- 狭義の 0 < 1 + 1 -/
hott lemma zeroLtTwo : 0 < (1 + 1 : ℝ) :=
begin
  apply Equiv.transport (· < (1 + 1 : ℝ));
  exact R.τ.addZero (0 : ℝ);
  apply strictIneqAdd R <;> exact zeroLtOne
end

/-- 1 + 1 ≠ 0 -/
hott lemma onePlusOneNeqZero : (1 + 1 : ℝ) ≠ (0 : ℝ) :=
λ p, (zeroLtTwo).1 (Id.symm p)

/-- 1 + 1 は加法群の意味で proper（逆元を取れる） -/
hott lemma twoProper : @Prering.isproper R.τ _ (1 + 1 : ℝ) :=
begin
  unfold Prering.isproper Group.isproper;
  intro p;
  apply onePlusOneNeqZero;
  exact p ⬝ additiveUnit
end

/-- 2 の逆元（⁻¹ 表記はパスの逆元と競合するため明示） -/
hott definition twoInv : ℝ := @ring.hasInv.inv R.τ _ (1 + 1 : ℝ)

/-- 逆元の2倍: twoInv + twoInv = 1 -/
hott lemma twoInvAdd : (twoInv + twoInv : ℝ) = (1 : ℝ) :=
calc (twoInv + twoInv : ℝ) = ((1 + 1 : ℝ) * twoInv : ℝ) :
      Id.symm (calc ((1 + 1 : ℝ) * twoInv : ℝ) = ((1 : ℝ) * twoInv + (1 : ℝ) * twoInv : ℝ) :
        @ring.distribRight R.τ _ (1 : ℝ) (1 : ℝ) twoInv,
        = (twoInv + (1 : ℝ) * twoInv : ℝ) :
          ap (· + (1 : ℝ) * twoInv) (@ring.monoid.oneMul R.τ _ twoInv),
        = (twoInv + twoInv : ℝ) :
          ap (twoInv + ·) (@ring.monoid.oneMul R.τ _ twoInv)),
    = (1 : ℝ) : @ring.comm.mulComm R.τ _ (1 + 1 : ℝ) twoInv ⬝
          @ring.divisible.mulLeftInv R.τ _ (1 + 1 : ℝ) twoProper

/-- 2等分: z·twoInv + z·twoInv = z -/
hott lemma halve (z : ℝ) : (z * twoInv + z * twoInv : ℝ) = z :=
calc (z * twoInv + z * twoInv : ℝ) = (z * (twoInv + twoInv) : ℝ) :
      Id.symm (@ring.distribLeft R.τ _ z twoInv twoInv),
    = (z * (1 : ℝ) : ℝ) : ap (z * ·) twoInvAdd,
    = z : @ring.monoid.mulOne R.τ _ z

/-- exp の非負性: exp z = exp(z/2)² ≥ 0
    （expAdd + 平方非負性 + 体の2等分から導出可能。exp が公理でも不等式は得られる） -/
hott theorem expNonneg (z : ℝ) : R.ρ 0 (exp z) :=
begin
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (expAdd (z * twoInv) (z * twoInv)) ⬝ ap exp (halve z);
  apply sqrNonneg
end

/-- ガウスカーネルの成分は点ごとに非負: 0 ≤ exp(-ε²r²)（expNonneg の直接の帰結）
    ※ 成分の非負性は正定値性（2次形式の非負性）よりずっと弱い -/
hott corollary gaussEntryNonneg (ε r : ℝ) : R.ρ 0 (exp (-(ε * ε * (r * r)))) :=
expNonneg (-(ε * ε * (r * r)))

/-- ランク1カーネルの2次形式は平方:
    Σᵢⱼ (cᵢ·cⱼ)·(f(xᵢ)·f(xⱼ)) = (Σᵢ cᵢ·f(xᵢ))² -/
hott lemma quadFormRankOne {α : Type u} (f : α → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → α) :
  quadForm (λ x y, f x * f y) n c x = (sum n (λ i, c i * f (x i))) * (sum n (λ i, c i * f (x i))) :=
calc sum n (λ i, sum n (λ j, (c i * c j) * (f (x i) * f (x j))))
     = sum n (λ i, sum n (λ j, (c i * f (x i)) * (c j * f (x j)))) :
       sum.ext n (λ i, sum.ext n (λ j, middleFour (c i) (c j) (f (x i)) (f (x j)))),
     = sum n (λ i, sum n (λ j, (c j * f (x j)) * (c i * f (x i)))) :
       sum.ext n (λ i, sum.ext n (λ j, @ring.comm.mulComm R.τ _ (c i * f (x i)) (c j * f (x j)))),
     = sum n (λ i, (sum n (λ j, c j * f (x j))) * (c i * f (x i))) :
       sum.ext n (λ i, sumMul n (λ j, c j * f (x j)) (c i * f (x i))),
     = (sum n (λ j, c j * f (x j))) * (sum n (λ i, c i * f (x i))) :
       Id.symm (mulSum (sum n (λ j, c j * f (x j))) n (λ i, c i * f (x i)))

/-- ランク1カーネル K(x,y) = f x · f y は正半定値 -/
hott theorem psdRankOne {α : Type u} (f : α → ℝ) : PSD (λ x y, f x * f y) :=
begin
  unfold PSD;
  intro n c x;
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (quadFormRankOne f n c x);
  apply sqrNonneg
end

/-- 2次形式はカーネルの + に分配する -/
hott lemma quadFormAdd {α : Type u} (K₁ K₂ : α → α → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → α) :
  quadForm (λ x y, K₁ x y + K₂ x y) n c x = quadForm K₁ n c x + quadForm K₂ n c x :=
calc sum n (λ i, sum n (λ j, (c i * c j) * (K₁ (x i) (x j) + K₂ (x i) (x j))))
     = sum n (λ i, sum n (λ j, (c i * c j) * K₁ (x i) (x j) + (c i * c j) * K₂ (x i) (x j))) :
       sum.ext n (λ i, sum.ext n (λ j, @ring.distribLeft R.τ _ (c i * c j) (K₁ (x i) (x j)) (K₂ (x i) (x j)))),
     = sum n (λ i, sum n (λ j, (c i * c j) * K₁ (x i) (x j)) + sum n (λ j, (c i * c j) * K₂ (x i) (x j))) :
       sum.ext n (λ i, Id.symm (sumAdd n (λ j, (c i * c j) * K₁ (x i) (x j)) (λ j, (c i * c j) * K₂ (x i) (x j)))),
     = sum n (λ i, sum n (λ j, (c i * c j) * K₁ (x i) (x j))) + sum n (λ i, sum n (λ j, (c i * c j) * K₂ (x i) (x j))) :
       Id.symm (sumAdd n (λ i, sum n (λ j, (c i * c j) * K₁ (x i) (x j))) (λ i, sum n (λ j, (c i * c j) * K₂ (x i) (x j))))

/-- PSD は + で閉じている: 正定値カーネルの有限和は正定値 -/
hott theorem psdAdd {α : Type u} {K₁ K₂ : α → α → ℝ} (p₁ : PSD K₁) (p₂ : PSD K₂) :
  PSD (λ x y, K₁ x y + K₂ x y) :=
begin
  unfold PSD;
  intro n c x;
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (quadFormAdd K₁ K₂ n c x);
  apply Equiv.transport (λ z, R.ρ z (quadForm K₁ n c x + quadForm K₂ n c x));
  exact R.τ.addZero (0 : ℝ);
  apply ineqAdd R (p₁ n c x) (p₂ n c x)
end

  /-
    ============================================================================
    追記評価: 級数分解公理 expSeries とガウス PSD
    ============================================================================

    ライブラリ (Reals.lean) に追加した部品:
      rpow (tⁿ) / fac (n!) / rdiv (a/b) / infiniteSum / infiniteSum.ext /
      expSeries (exp t = Σₙ tⁿ/n!)

    完全に証明できたもの:
      · rpowMul: (x·y)ⁿ = xⁿ·yⁿ  → 1次元の多項式カーネルはランク1カーネル
      · polyKernelPsd: (x·y)ⁿ は PSD（ランク1 + 平方非負性）
      · 係数 cₙ = (2ε²)ⁿ/n! の非負性（順序体の基本補題群から導出）
      · taylorPsd: 有限テイラー切断 Σₙ₌₀ᴺ cₙ(x·y)ⁿ は PSD
      · gaussTruncPsd: exp(-ε²x²)·T_N·exp(-ε²y²) も PSD（ランク1因子は PSD を保つ）
      · gaussDecomp: exp(-ε²(x-y)²) = exp(-ε²x²)·exp(2ε²xy)·exp(-ε²y²)
      · expMid: exp(2ε²xy) = Σₙ cₙ(x·y)ⁿ（expSeries + rpowMul + 無限和の外延性）

    残りのブロッカー（2つの実解析公理で代用 — 下の infSumNonneg /
    infSumFinSwap を参照）:
      infiniteSum は不透明な公理記号であり、以下は収束論（単調収束・級数の
      線型性）がなければ導けない:
        (1) 各項が非負 → 無限和も非負          (infSumNonneg に相当)
        (2) 有限和（2次形式）と無限和の交換   (infSumFinSwap に相当)
      この2つを公理として追加し、gaussPsd（ガウス PSD の完成）に到達した。
      これらは HoTT の問題ではなく実解析（級数・収束の理論）の内容である。
    ============================================================================
  -/

  /-- 冪の乗法性: (x·y)ⁿ = xⁿ·yⁿ -/
  hott lemma rpowMul (x y : ℝ) : Π (n : ℕ), rpow (x * y) n = rpow x n * rpow y n :=
  begin
    intro n; induction n with
    | zero => exact Id.symm (@ring.monoid.oneMul R.τ _ (1 : ℝ))
    | succ n ih => exact (ap (· * (x * y)) ih ⬝ middleFour (rpow x n) (rpow y n) x y)
  end

  /-- 多項式カーネル (x·y)ⁿ は正半定値（ランク1に帰着） -/
  hott theorem polyKernelPsd (n : ℕ) : PSD (λ x y, rpow (x * y) n) :=
  begin
    unfold PSD; intro m c x;
    apply Equiv.transport (R.ρ 0);
    exact Id.symm (sum.ext m (λ i, sum.ext m (λ j,
      ap (λ z, (c i * c j) * z) (rpowMul (x i) (x j) n))));
    exact psdRankOne (λ z, rpow z n) m c x
  end

  /-- 1 は非負: 0 ≤ 1 -/
  hott lemma oneNonneg : R.ρ 0 (1 : ℝ) := zeroLeOne

  /-- 非負同士の積は非負 -/
  hott lemma mulNonneg {a b : ℝ} (p : R.ρ 0 a) (q : R.ρ 0 b) : R.ρ 0 (a * b) :=
  orfield.leOverMul a b p q

  /-- 非負数の冪は非負 -/
  hott lemma rpowNonneg {t : ℝ} (p : R.ρ 0 t) : Π (n : ℕ), R.ρ 0 (rpow t n) :=
  begin
    intro n; induction n with
    | zero => exact oneNonneg
    | succ n ih => exact mulNonneg ih p
  end

  /-- 自然数の埋め込みは非負: 0 ≤ N.incl n -/
  hott lemma N.inclNonneg : Π (n : ℕ), R.ρ 0 (N.incl n) :=
  begin
    intro n; induction n with
    | zero => exact @reflexive.refl R.κ _ (0 : ℝ)
    | succ n ih => apply Equiv.transport (R.ρ · (N.incl n + 1)); apply R.τ.addZero (0 : ℝ); apply ineqAdd R; exact ih; exact oneNonneg
  end

  /-- 自然数の埋め込みは正: 0 < N.incl (n+1) -/
  hott lemma N.inclPos (n : ℕ) : 0 < N.incl (Nat.succ n) :=
  begin
    apply Equiv.transport (· < N.incl n + 1); apply R.τ.addZero (0 : ℝ);
    apply strictIneqAddLeft R (N.inclNonneg n) zeroLtOne
  end

  /-- 正×正は正 -/
  hott lemma mulPos {a b : ℝ} (p : 0 < a) (q : 0 < b) : 0 < a * b :=
  begin
    apply Prod.mk;
    { intro r; exact (field.properMul (λ s, p.1 (Id.symm s)) (λ s, q.1 (Id.symm s))) (Id.symm r) };
    { apply orfield.leOverMul; exact p.2; exact q.2 }
  end

  /-- 階乗は正: 0 < n! -/
  hott lemma facPos : Π (n : ℕ), 0 < fac n :=
  begin
    intro n; induction n with
    | zero => exact zeroLtOne
    | succ n ih => exact mulPos ih (N.inclPos n)
  end

  /-- 正数の逆数は非負: 0 < a → 0 ≤ a⁻¹ -/
  hott lemma invPos {a : ℝ} (p : 0 < a) : R.ρ 0 (@ring.hasInv.inv R.τ _ a) :=
  begin
    apply Equiv.transport (R.ρ 0);
    exact Id.symm (calc @ring.hasInv.inv R.τ _ a
          = R.τ.ψ (1 : ℝ) (@ring.hasInv.inv R.τ _ a) :
            Id.symm (@ring.monoid.oneMul R.τ _ (@ring.hasInv.inv R.τ _ a)),
          = R.τ.ψ (R.τ.ψ a (@ring.hasInv.inv R.τ _ a)) (@ring.hasInv.inv R.τ _ a) :
            ap (λ y, R.τ.ψ y (@ring.hasInv.inv R.τ _ a))
               (Id.symm (@field.mulRightInv R.τ _ a (λ s, p.1 (Id.symm s)))),
          = R.τ.ψ a (R.τ.ψ (@ring.hasInv.inv R.τ _ a) (@ring.hasInv.inv R.τ _ a)) :
            @ring.assoc.mulAssoc R.τ _ a (@ring.hasInv.inv R.τ _ a) (@ring.hasInv.inv R.τ _ a));
    apply orfield.leOverMul; exact p.2; apply sqrNonneg
  end

  /-- 級数の係数: cₙ = (2ε²)ⁿ/n! -/
  hott definition coeff (ε : ℝ) (n : ℕ) : ℝ :=
  R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) (@ring.hasInv.inv R.τ _ (fac n))

  /-- 係数は非負: 0 ≤ cₙ -/
  hott lemma coeffNonneg (ε : ℝ) : Π (n : ℕ), R.ρ 0 (coeff ε n) :=
  begin
    intro n;
    exact mulNonneg (rpowNonneg (mulNonneg zeroLtTwo.2 (sqrNonneg ε)) n) (invPos (facPos n))
  end

  /-- (a·b)·(c·d) = c·((a·b)·d)（定数くくり出しの準備） -/
  hott lemma ringScale (a b c d : ℝ) : (a * b) * (c * d) = c * ((a * b) * d) :=
  calc (a * b) * (c * d) = ((a * b) * c) * d : Id.symm (@ring.assoc.mulAssoc R.τ _ (a * b) c d),
       = (c * (a * b)) * d : ap (· * d) (@ring.comm.mulComm R.τ _ (a * b) c),
       = c * ((a * b) * d) : @ring.assoc.mulAssoc R.τ _ c (a * b) d

  /-- Σᵢⱼ (cᵢcⱼ)·(s·K(xᵢ,xⱼ)) = s·Σᵢⱼ (cᵢcⱼ)·K(xᵢ,xⱼ) -/
  hott lemma quadFormScale {K : ℝ → ℝ → ℝ} (s : ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → ℝ) :
    quadForm (λ x y, s * K x y) n c x = s * quadForm K n c x :=
  calc sum n (λ i, sum n (λ j, (c i * c j) * (s * K (x i) (x j))))
       = sum n (λ i, sum n (λ j, s * ((c i * c j) * K (x i) (x j)))) :
         sum.ext n (λ i, sum.ext n (λ j, ringScale (c i) (c j) s (K (x i) (x j)))),
       = sum n (λ i, s * sum n (λ j, (c i * c j) * K (x i) (x j))) :
         sum.ext n (λ i, Id.symm (mulSum s n (λ j, (c i * c j) * K (x i) (x j)))),
       = s * sum n (λ i, sum n (λ j, (c i * c j) * K (x i) (x j))) :
         Id.symm (mulSum s n (λ i, sum n (λ j, (c i * c j) * K (x i) (x j))))

  /-- PSD カーネルを非負定数でスケールしても PSD -/
  hott theorem psdScale {K : ℝ → ℝ → ℝ} (p : PSD K) {s : ℝ} (hs : R.ρ 0 s) :
    PSD (λ x y, s * K x y) :=
  begin
    unfold PSD; intro n c x;
    apply Equiv.transport (R.ρ 0);
    exact Id.symm (quadFormScale s n c x);
    apply orfield.leOverMul; exact hs; exact p n c x
  end

  /-- ランク1因子の準備: (a·b)·(u·K·v) = ((a·u)·(b·v))·K -/
  hott lemma rank1ScalePair (a b u v K : ℝ) : (a * b) * (u * K * v) = ((a * u) * (b * v)) * K :=
  Id.symm (@ring.assoc.mulAssoc R.τ _ (a * b) (u * K) v) ⬝
  ap (· * v) (middleFour a b u K) ⬝
  @ring.assoc.mulAssoc R.τ _ (a * u) (b * K) v ⬝
  ap ((a * u) * ·) (@ring.assoc.mulAssoc R.τ _ b K v) ⬝
  ap ((a * u) * ·) (ap (b * ·) (@ring.comm.mulComm R.τ _ K v)) ⬝
  ap ((a * u) * ·) (Id.symm (@ring.assoc.mulAssoc R.τ _ b v K)) ⬝
  Id.symm (@ring.assoc.mulAssoc R.τ _ (a * u) (b * v) K)

  /-- f(x)·K(x,y)·f(y) の2次形式は係数の置換に等しい -/
  hott lemma quadFormRank1Scale {K : ℝ → ℝ → ℝ} (f : ℝ → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → ℝ) :
    quadForm (λ x y, f x * K x y * f y) n c x = quadForm K n (λ i, c i * f (x i)) x :=
  sum.ext n (λ i, sum.ext n (λ j,
    rank1ScalePair (c i) (c j) (f (x i)) (f (x j)) (K (x i) (x j))))

  /-- ランク1因子 f(x)f(y) を掛けても PSD を保つ -/
  hott theorem psdRank1Scale {K : ℝ → ℝ → ℝ} (p : PSD K) (f : ℝ → ℝ) :
    PSD (λ x y, f x * K x y * f y) :=
  begin
    unfold PSD; intro n c x;
    apply Equiv.transport (R.ρ 0);
    exact Id.symm (quadFormRank1Scale f n c x);
    apply p
  end

  /-- 有限テイラー切断: T_N(x,y) = Σₙ₌₀ᴺ cₙ(x·y)ⁿ -/
  hott definition taylorKernel (ε : ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  sum N (λ n, coeff ε n * rpow (x * y) n)


  /-- 零カーネルの2次形式は 0 -/
  hott lemma quadFormZero (n : ℕ) (c : ℕ → ℝ) (x : ℕ → ℝ) : quadForm (λ x y, 0) n c x = 0 :=
  calc sum n (λ i, sum n (λ j, (c i * c j) * 0))
       = sum n (λ i, sum n (λ j, 0)) : sum.ext n (λ i, sum.ext n (λ j, @ring.mulZero R.τ _ (c i * c j))),
       = sum n (λ i, 0) : sum.ext n (λ i, sumZero n),
       = 0 : sumZero n

  /-- 零カーネルは PSD -/
  hott theorem psdZero : PSD (λ (x y : ℝ), 0) :=
  begin
    unfold PSD; intro n c x;
    apply Equiv.transport (R.ρ 0);
    exact Id.symm (quadFormZero n c x);
    apply @reflexive.refl R.κ
  end

  /-- 平方: sqr a = a·a -/
  hott definition sqr (a : ℝ) : ℝ := a * a

  /-- 有限テイラー切断は PSD: T_N = Σₙ₌₀ᴺ cₙ(x·y)ⁿ -/
  hott theorem taylorPsd (ε : ℝ) : Π (N : ℕ), PSD (λ x y, taylorKernel ε N x y) :=
  begin
    intro N; induction N with
    | zero => exact psdZero
    | succ N ih => exact psdAdd ih (psdScale (polyKernelPsd N) (coeffNonneg ε N))
  end

  /-- 切断ガウス: exp(-ε²x²)·T_N(x,y)·exp(-ε²y²) -/
  hott definition gaussTrunc (ε : ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  exp (-((ε * ε) * sqr x)) * taylorKernel ε N x y * exp (-((ε * ε) * sqr y))

  /-- 切断ガウスカーネルは PSD（ランク1因子は PSD を保つ） -/
  hott theorem gaussTruncPsd (ε : ℝ) (N : ℕ) : PSD (λ x y, gaussTrunc ε N x y) :=
  psdRank1Scale (taylorPsd ε N) (λ z, exp (-((ε * ε) * sqr z)))

  /-- (1+1)·a = a + a -/
  hott lemma twoMul (a : ℝ) : ((1 + 1 : ℝ) * a) = a + a :=
  calc ((1 + 1 : ℝ) * a) = ((1 : ℝ) * a + (1 : ℝ) * a) : @ring.distribRight R.τ _ (1 : ℝ) (1 : ℝ) a,
       = (a + a) : ap (· + (1 : ℝ) * a) (@ring.monoid.oneMul R.τ _ a) ⬝
                    ap (a + ·) (@ring.monoid.oneMul R.τ _ a)

  /-- (-a) + (-a) = -((1+1)·a) -/
  hott lemma twoProd (a : ℝ) : (-a) + (-a) = -(((1 + 1 : ℝ) * a)) :=
  Id.symm (negAdd a a) ⬝ ap (λ z, -z) (Id.symm (twoMul a))

  /-- (-x)·(-y) = x·y -/
  hott lemma negMulNeg (x y : ℝ) : (-x) * (-y) = x * y :=
  calc (-x) * (-y) = -((-x) * y) : @ring.mulNeg R.τ _ (-x) y,
       = -(-(x * y)) : ap (λ z, -z) (@ring.negMul R.τ _ x y),
       = x * y : @Group.invInv R.τ⁺ (x * y)

  /-- (x-y)² = x² - 2xy + y² -/
  hott lemma distSquare (x y : ℝ) :
    sqr (x - y) = sqr x + (-(((1 + 1) * (x * y)))) + sqr y :=
  calc sqr (x - y)
     = x * (x - y) + (-y) * (x - y) : @ring.distribRight R.τ _ x (-y) (x - y),
     = (x * x + x * (-y)) + ((-y) * x + (-y) * (-y)) :
         ap (· + (-y) * (x - y)) (@ring.distribLeft R.τ _ x x (-y)) ⬝
         ap ((x * x + x * (-y)) + ·) (@ring.distribLeft R.τ _ (-y) x (-y)),
     = (x * x + -(x * y)) + (-(y * x) + y * y) :
         ap (· + ((-y) * x + (-y) * (-y))) (ap (x * x + ·) (@ring.mulNeg R.τ _ x y)) ⬝
         ap ((x * x + -(x * y)) + ·)
            (ap (· + (-y) * (-y)) (@ring.negMul R.τ _ y x) ⬝
             ap (-(y * x) + ·) (negMulNeg y y)),
     = (x * x + -(x * y)) + (-(x * y) + y * y) :
         ap ((x * x + -(x * y)) + ·) (ap (· + y * y) (ap (λ z, -z) (@ring.comm.mulComm R.τ _ y x))),
     = (x * x + (-(x * y) + -(x * y))) + y * y :
         Id.symm (R.τ⁺.mulAssoc (x * x + -(x * y)) (-(x * y)) (y * y)) ⬝
         ap (· + y * y) (R.τ⁺.mulAssoc (x * x) (-(x * y)) (-(x * y))),
     = sqr x + (-(((1 + 1) * (x * y)))) + sqr y :
         ap (· + sqr y) (ap (sqr x + ·) (twoProd (x * y)))

  /-- c·((1+1)·(x·y)) = ((1+1)·c)·(x·y) -/
  hott lemma cScale (c x y : ℝ) : c * (((1 + 1) * (x * y))) = ((1 + 1) * c) * (x * y) :=
  calc c * ((1 + 1) * (x * y)) = (c * (1 + 1)) * (x * y) : Id.symm (@ring.assoc.mulAssoc R.τ _ c (1 + 1) (x * y)),
       = ((1 + 1) * c) * (x * y) : ap (· * (x * y)) (@ring.comm.mulComm R.τ _ c (1 + 1))

  /-- c·(x-y)² = c·x² - ((1+1)·c)·(x·y) + c·y² -/
  hott lemma mulDistSquare (c x y : ℝ) :
    c * sqr (x - y) = c * sqr x + (-(((1 + 1) * c) * (x * y))) + c * sqr y :=
  calc c * sqr (x - y)
     = c * (sqr x + (-(((1 + 1) * (x * y)))) + sqr y) : ap (c * ·) (distSquare x y),
     = c * (sqr x + (-(((1 + 1) * (x * y))))) + c * sqr y :
         @ring.distribLeft R.τ _ c (sqr x + (-(((1 + 1 : ℝ) * (x * y))))) (sqr y),
     = (c * sqr x + c * (-(((1 + 1) * (x * y))))) + c * sqr y :
         ap (· + c * sqr y) (@ring.distribLeft R.τ _ c (sqr x) (-(((1 + 1 : ℝ) * (x * y))))),
     = (c * sqr x + -(c * (((1 + 1) * (x * y))))) + c * sqr y :
         ap (· + c * sqr y) (ap (c * sqr x + ·) (@ring.mulNeg R.τ _ c (((1 + 1 : ℝ) * (x * y))))),
     = c * sqr x + (-(((1 + 1) * c) * (x * y))) + c * sqr y :
         ap (· + c * sqr y) (ap (c * sqr x + ·) (ap (λ z, -z) (cScale c x y)))

  /-- -(a + b + c) = -a + -b + -c -/
  hott lemma negTriple (a b c : ℝ) : -(a + b + c) = -a + -b + -c :=
  calc -(a + b + c) = -(a + b) + -c : negAdd (a + b) c,
       = (-a + -b) + -c : ap (· + -c) (negAdd a b)


  hott lemma expSummand (ε x y : ℝ) (n : ℕ) :
    rdiv (rpow (((1 + 1) * (ε * ε)) * (x * y)) n) (fac n) =
    coeff ε n * rpow (x * y) n :=
  calc rdiv (rpow (((1 + 1) * (ε * ε)) * (x * y)) n) (fac n)
     = R.τ.ψ (rpow (((1 + 1) * (ε * ε)) * (x * y)) n) (@ring.hasInv.inv R.τ _ (fac n)) : by reflexivity,
     = R.τ.ψ (R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) (rpow (x * y) n)) (@ring.hasInv.inv R.τ _ (fac n)) :
         ap (λ y, R.τ.ψ y (@ring.hasInv.inv R.τ _ (fac n))) (rpowMul ((1 + 1) * (ε * ε)) (x * y) n),
     = R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) (R.τ.ψ (rpow (x * y) n) (@ring.hasInv.inv R.τ _ (fac n))) :
         @ring.assoc.mulAssoc R.τ _ (rpow ((1 + 1) * (ε * ε)) n) (rpow (x * y) n) (@ring.hasInv.inv R.τ _ (fac n)),
     = R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) (R.τ.ψ (@ring.hasInv.inv R.τ _ (fac n)) (rpow (x * y) n)) :
         ap (λ y, R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) y)
            (@ring.comm.mulComm R.τ _ (rpow (x * y) n) (@ring.hasInv.inv R.τ _ (fac n))),
     = R.τ.ψ (R.τ.ψ (rpow ((1 + 1) * (ε * ε)) n) (@ring.hasInv.inv R.τ _ (fac n))) (rpow (x * y) n) :
         Id.symm (@ring.assoc.mulAssoc R.τ _ (rpow ((1 + 1) * (ε * ε)) n) (@ring.hasInv.inv R.τ _ (fac n)) (rpow (x * y) n)),
     = coeff ε n * rpow (x * y) n : by reflexivity

  hott definition gaussKernel (ε x y : ℝ) : ℝ :=
  exp (-((ε * ε) * sqr (x - y)))

  hott axiom infSumNonneg (g : ℕ → ℝ) : (Π n, R.ρ 0 (g n)) → R.ρ 0 (infiniteSum g)

  /-
    追記評価4（歴史的記録）: 交換則 infSumFinSwap は公理ではなく「極限の
    線型性」infSumLin から導出される定理であることが示された。ただし
    追記評価14 で infSumLin も含めこのチェーン全体が削除され、D ワールドの
    conv 仮説版（infSumFinSwapConv / sumSwapInfConv 等）が現在の標準。
    詳細は末尾の追記評価4・追記評価10・追記評価14を参照。
  -/

  /-
    ============================================================================
    追記評価6（統合済み）: コーシー列・極限の最小理論
    ============================================================================
    プローブ /tmp/probe_lim.lean の内容を統合（#print axioms で検証済み）:
      · convAdd / absMul は実解析の新公理ゼロ（既存の Classical.choice には依存）
      · infSumLinD（線型性の吸収）= {infSumIsLim} のみ
      · cauchyProductLim（コーシー積の定理化）= {infSumIsLim, mertens}

    構成:
      · abs 理論の完成: subSelf / diffAddCombine / absTriangle / absDiffTri
      · conv（ε-N 収束）: conv / convConst / convAdd（ε/2 分割 = twoInv/halve）
      · 最小公理: infSumIsLim（無限和は極限）・ mertens（絶対収束版コーシー積）
      · cauchyProductLim: 旧公理 cauchyProduct を定理化
      · infSumLinD: 線型性（収束仮定付き）を {infSumIsLim} のみから定理化

    重要な制約: infSumIsLim の方向は「部分和が L に収束 → infiniteSum f = L」で
    あり、逆方向は任意の列では導けない。したがって無条件形の infSumLin（下の
    公理）はこの理論からは導出できず、gaussPsd の依存公理の削減（目標
    {infSumNonneg, infSumIsLim, mertens}）は exp の級数再定義
    （追記評価5）とガウス級数の収束仮定の検証（絶対収束理論）を待つ
    （expZero は追記評価9 で BinomTaylor.expZeroD として定理化済み）。
    ============================================================================
  -/


/- ============================================================
   Stage A: abs 理論の完成（三角不等式）
   ライブラリには abs の符号分解（abs.pos/abs.neg）、上下界
   （abs.ge/abs.le/abs.leIfMinusLeAndLe）が既にある。
   三角不等式はここから全て導出できる（公理不要）。
   ============================================================ -/

/-- 自己差: x - x = 0 -/
hott lemma subSelf (x : ℝ) : x - x = 0 :=
calc x - x = x + (-x) : by reflexivity,
     = (-x) + x : R.τ.addComm x (-x),
     = 0 : R.τ.addLeftNeg x

/-- 差の合成: (a - c) + (b - d) = (a + b) - (c + d) -/
hott lemma diffAddCombine (a b c d : ℝ) : (a - c) + (b - d) = (a + b) - (c + d) :=
calc (a - c) + (b - d)
     = (a + (-c)) + (b + (-d)) : by reflexivity,
     = a + ((-c) + (b + (-d))) : R.τ.addAssoc a (-c) (b + (-d)),
     = a + (((-c) + b) + (-d)) : ap (a + ·) (Id.symm (R.τ.addAssoc (-c) b (-d))),
     = a + ((b + (-c)) + (-d)) : ap (a + ·) (ap (· + (-d)) (R.τ.addComm (-c) b)),
     = a + (b + ((-c) + (-d))) : ap (a + ·) (R.τ.addAssoc b (-c) (-d)),
     = (a + b) + ((-c) + (-d)) : Id.symm (R.τ.addAssoc a b ((-c) + (-d))),
     = (a + b) + (-(c + d)) : ap ((a + b) + ·) (Id.symm (negAdd c d)),
     = (a + b) - (c + d) : by reflexivity

/-- 三角不等式: |x + y| ≤ |x| + |y| -/
hott lemma absTriangle (x y : ℝ) : R.ρ (abs (x + y)) (abs x + abs y) :=
begin
  apply abs.leIfMinusLeAndLe (abs x + abs y) (x + y);
  { apply Equiv.transport (R.ρ · (x + y));
    symmetry; apply negAdd (abs x) (abs y);
    apply ineqAdd R <;> apply abs.le };
  { apply ineqAdd R <;> apply abs.ge }
end

/-- 三角不等式（差版）: |(a+b) - (c+d)| ≤ |a - c| + |b - d| -/
hott lemma absDiffTri (a b c d : ℝ) : R.ρ (abs ((a + b) - (c + d))) (abs (a - c) + abs (b - d)) :=
  Equiv.transport (λ w, R.ρ (abs w) (abs (a - c) + abs (b - d))) (diffAddCombine a b c d)
    (absTriangle (a - c) (b - d))

/- ============================================================
   Stage B: conv（ε-N 収束）の定義と自明な性質
   ============================================================ -/

/-- ε-N 収束: 列 a は L に収束する（N ≤ n はライブラリの max ベースの le） -/
hott definition conv (a : ℕ → ℝ) (L : ℝ) : Type :=
  Π (ε : ℝ), 0 < ε → Σ (N : ℕ), Π (n : ℕ), N ≤ n → R.ρ (abs (a n - L)) ε

/-- 定数列は収束する -/
hott lemma convConst (x : ℝ) : conv (λ n, x) x :=
begin
  intro ε p;
  exact ⟨0, λ n q,
    Equiv.transport (λ w, R.ρ w ε) (Id.symm (ap abs (subSelf x) ⬝ abs.zero)) p.2⟩
end

/- ============================================================
   Stage C: ε/2 分割（twoInv / halve の再利用）と convAdd
   ============================================================ -/

/-- 2 の逆元は正: 0 < twoInv -/
hott lemma twoInvPos : 0 < twoInv :=
⟨λ p, (zeroLtOne).1 (Id.symm (calc (1 : ℝ) = twoInv + twoInv : Id.symm twoInvAdd,
     = 0 + 0 : Id.symm (ap (· + twoInv) p) ⬝ Id.symm (ap (0 + ·) p),
     = 0 : R.τ.addZero (0 : ℝ))), invPos zeroLtTwo⟩

/-- ε の半分は正: 0 < ε → 0 < ε·twoInv -/
hott lemma halfPos {ε : ℝ} (p : 0 < ε) : 0 < ε * twoInv :=
  mulPos p twoInvPos

/-- ε·twoInv は非負 -/
hott lemma halfNonneg {ε : ℝ} (p : 0 < ε) : R.ρ 0 (ε * twoInv) :=
  mulNonneg p.2 (invPos zeroLtTwo)

/-- 半分は全体以下: ε·twoInv ≤ ε -/
hott lemma halfLe {ε : ℝ} (p : 0 < ε) : R.ρ (ε * twoInv) ε :=
  Equiv.transport (λ w, R.ρ (ε * twoInv) w) (halve ε)
    (Equiv.transport (λ w, R.ρ w (ε * twoInv + ε * twoInv)) (R.τ.addZero (ε * twoInv))
       (ineqAdd R (@reflexive.refl R.κ _ (ε * twoInv)) (halfNonneg p)))

/-- 極限の加法性: aₙ → A, bₙ → B なら aₙ + bₙ → A + B -/
hott lemma convAdd (a b : ℕ → ℝ) (A B : ℝ) (ha : conv a A) (hb : conv b B) :
  conv (λ n, a n + b n) (A + B) :=
begin
  intro ε p;
  exact ⟨GroundZero.Theorems.Nat.max (ha (ε * twoInv) (halfPos p)).1 (hb (ε * twoInv) (halfPos p)).1, λ n r,
    Equiv.transport (λ w, R.ρ (abs ((a n + b n) - (A + B))) w) (halve ε)
      (@transitive.trans R.κ _ _ _ _ (absDiffTri (a n) (b n) A B)
        (ineqAdd R ((ha (ε * twoInv) (halfPos p)).2 n (le.trans (le.max (ha (ε * twoInv) (halfPos p)).1 (hb (ε * twoInv) (halfPos p)).1) r))
                   ((hb (ε * twoInv) (halfPos p)).2 n (le.trans                     (Equiv.transport (λ w, (hb (ε * twoInv) (halfPos p)).1 ≤ w) (max.comm (hb (ε * twoInv) (halfPos p)).1 (ha (ε * twoInv) (halfPos p)).1) (le.max (hb (ε * twoInv) (halfPos p)).1 (ha (ε * twoInv) (halfPos p)).1)) r))))⟩
end

/- ============================================================
   Stage D: infiniteSum の極限同定 → cauchyProduct の定理化
   ============================================================ -/

/-- infiniteSum は極限と一致する（新しい最小公理） -/
hott axiom infSumIsLim (f : ℕ → ℝ) (L : ℝ) :
  conv (λ n, sum (Nat.succ n) f) L → infiniteSum f = L

/-- 絶対収束版コーシー積（Mertens）: Σ|A| 収束 ∧ ΣA → SA ∧ ΣB → SB なら
    畳み込み級数 cₙ = Σₖ₌₀ⁿ Aₖ·Bₙ₋ₖ の部分和は SA·SB に収束する -/
hott axiom mertens (A B : ℕ → ℝ) (SA SB Aabs : ℝ)
  (hS : conv (λ n, sum (Nat.succ n) A) SA)
  (hT : conv (λ n, sum (Nat.succ n) B) SB)
  (hAbs : conv (λ n, sum (Nat.succ n) (λ k, abs (A k))) Aabs) :
  conv (λ n, sum (Nat.succ n) (λ i, sum (Nat.succ i) (λ k, A k * B (i - k)))) (SA * SB)

/-- cauchyProduct の定理化: 収束仮定下で
    infiniteSum A · infiniteSum B = infiniteSum (Σₖ₌₀ⁿ Aₖ·Bₙ₋ₖ) -/
hott theorem cauchyProductLim (A B : ℕ → ℝ) (SA SB Aabs : ℝ)
  (hS : conv (λ n, sum (Nat.succ n) A) SA)
  (hT : conv (λ n, sum (Nat.succ n) B) SB)
  (hAbs : conv (λ n, sum (Nat.succ n) (λ k, abs (A k))) Aabs) :
  infiniteSum A * infiniteSum B = infiniteSum (λ n, sum (Nat.succ n) (λ k, A k * B (n - k))) :=
calc
  infiniteSum A * infiniteSum B
     = SA * SB : ap (· * infiniteSum B) (infSumIsLim A SA hS) ⬝ ap (SA * ·) (infSumIsLim B SB hT),
     = infiniteSum (λ n, sum (Nat.succ n) (λ k, A k * B (n - k))) :
         Id.symm (infSumIsLim (λ n, sum (Nat.succ n) (λ k, A k * B (n - k))) (SA * SB)
                   (mertens A B SA SB Aabs hS hT hAbs))

/- ============================================================
   Stage D′: expD と指数級数の収束仮説 — BinomTaylor から移設（追記評価11）
   ============================================================
   expD / expDSeries / convExpD / convAbsExpD はもともと BinomTaylor.lean に
   あったが、gaussPsd（exp ワールド）の conv 仮説版張り替え（棚卸しの除去
   経路①）には PosDef 側に必要。BinomTaylor は open PosDef で短縮名参照する。
   移設で expD の透明度・定義は不変（rdiv a b ≡ a · rin b、expD t ≡ Σₙ tⁿ/n!）
   のため、BinomTaylor 側の by reflexivity ステップは壊れない。#print axioms
   上の依存公理名は BinomTaylor.convExpD → PosDef.convExpD に移る。 -/

/-- exp の級数再定義: expD t := Σₙ tⁿ/n! -/
hott def expD (t : ℝ) : ℝ :=
infiniteSum (λ n, rdiv (rpow t n) (fac n))

/-- expDSeries: expD t = Σₙ tⁿ/n!（定義より rfl） -/
hott lemma expDSeries (t : ℝ) : expD t = infiniteSum (λ n, rdiv (rpow t n) (fac n)) :=
by reflexivity

/-- 指数級数の収束（追記評価7 の conv 仮説・評価公理）: 部分和 Σₖ aᵏ/k! は
    expD a に収束する。現行公理からは導出不能（infSumIsLim は conv → 極限
    同定の一方向のみ、比較判定・比率判定の理論が無い）。TODO: 実解析理論の
    完成で導出。 -/
hott axiom convExpD (a : ℝ) :
  conv (λ n, sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k))) (expD a)

/-- 指数級数の絶対収束（追記評価7 の conv 仮説・評価公理）: Σₖ |a|ᵏ/k! は
    収束する（mertens の hAbs 仮説に必要）。 -/
hott axiom convAbsExpD (a : ℝ) :
  Σ Aabs : ℝ, conv (λ n, sum (Nat.succ n) (λ k, abs (rdiv (rpow a k) (fac k)))) Aabs

/- ============================================================
   Stage E: ボーナス — 線型性公理の吸収
   convScale（積の極限・スカラー版）が証明できれば、極限理論は
   infSumLin（追記評価4 の公理）も定理として吸収する。
   鍵は absMul（|x·y| = |x|·|y|）と符号×積の順序補題。
   ============================================================ -/

/-- 非負×非正は非正: 0 ≤ x → y ≤ 0 → x·y ≤ 0 -/
hott lemma mulLeZero {x y : ℝ} (p : R.ρ 0 x) (q : R.ρ y 0) : R.ρ (x * y) 0 :=
  R.zeroLeMinusImplZeroGe (Equiv.transport (λ w, R.ρ 0 w) (@ring.mulNeg R.τ _ x y)
    (mulNonneg p (R.zeroGeImplZeroLeMinus q)))

/-- 非正×非正は非負: x ≤ 0 → y ≤ 0 → 0 ≤ x·y -/
hott lemma mulGeZero {x y : ℝ} (p : R.ρ x 0) (q : R.ρ y 0) : R.ρ 0 (x * y) :=
  Equiv.transport (λ w, R.ρ 0 w)
    (@ring.negMul R.τ _ x (-y) ⬝ ap (λ z, -z) (@ring.mulNeg R.τ _ x y) ⬝ @Group.invInv R.τ⁺ (x * y))
    (mulNonneg (R.zeroGeImplZeroLeMinus p) (R.zeroGeImplZeroLeMinus q))

/-- スカラー差: c·a - c·b = c·(a - b) -/
hott lemma distMul (c a b : ℝ) : c * a - c * b = c * (a - b) :=
calc c * a - c * b = c * a + (-(c * b)) : by reflexivity,
     = c * a + c * (-b) : ap (c * a + ·) (Id.symm (@ring.mulNeg R.τ _ c b)),
     = c * (a + (-b)) : Id.symm (@ring.distribLeft R.τ _ c a (-b)),
     = c * (a - b) : by reflexivity

/-- 非負スカラー倍は順序を保つ: u ≤ v → 0 ≤ w → w·u ≤ w·v -/
hott lemma mulLeMono {u v w : ℝ} (r : R.ρ u v) (s : R.ρ 0 w) : R.ρ (w * u) (w * v) :=
  leIfSubGeZero R (Equiv.transport (λ t, R.ρ 0 t) (Id.symm (distMul w v u))
    (mulNonneg s (subGeZeroIfLe R r)))

/-- 絶対値の積: |x·y| = |x|·|y| -/
hott lemma absMulCase1 (x y : ℝ) (p : R.ρ 0 x) (q : R.ρ 0 y) : abs (x * y) = abs x * abs y :=
calc abs (x * y) = x * y : abs.pos (mulNonneg p q),
     = abs x * abs y : Id.symm (ap (· * abs y) (abs.pos p) ⬝ ap (x * ·) (abs.pos q))

hott lemma absMulCase2 (x y : ℝ) (p : R.ρ 0 x) (q : 0 > y) : abs (x * y) = abs x * abs y :=
calc abs (x * y) = -(x * y) : abs.neg (mulLeZero p q.2),
     = x * (-y) : Id.symm (@ring.mulNeg R.τ _ x y),
     = abs x * abs y : Id.symm (ap (· * abs y) (abs.pos p) ⬝ ap (x * ·) (abs.neg q.2))

hott lemma absMulCase3 (x y : ℝ) (p : 0 > x) (q : R.ρ 0 y) : abs (x * y) = abs x * abs y :=
calc abs (x * y) = -(x * y) :
       abs.neg (Equiv.transport (λ w, R.ρ w 0) (@ring.comm.mulComm R.τ _ y x) (mulLeZero q p.2)),
     = (-x) * y : Id.symm (@ring.negMul R.τ _ x y),
     = abs x * abs y : Id.symm (ap (· * abs y) (abs.neg p.2) ⬝ ap ((-x) * ·) (abs.pos q))

hott lemma absMulCase4 (x y : ℝ) (p : 0 > x) (q : 0 > y) : abs (x * y) = abs x * abs y :=
calc abs (x * y) = x * y : abs.pos (mulGeZero p.2 q.2),
     = (-x) * (-y) : Id.symm (@ring.negMul R.τ _ x (-y) ⬝ ap (λ z, -z) (@ring.mulNeg R.τ _ x y) ⬝ @Group.invInv R.τ⁺ (x * y)),
     = abs x * abs y : Id.symm (ap (· * abs y) (abs.neg p.2) ⬝ ap ((-x) * ·) (abs.neg q.2))

hott lemma absMul (x y : ℝ) : abs (x * y) = abs x * abs y :=
begin
  match R.total 0 x, R.total 0 y with
  | Sum.inl p, Sum.inl q => { exact absMulCase1 x y p q }
  | Sum.inl p, Sum.inr q => { exact absMulCase2 x y p q }
  | Sum.inr p, Sum.inl q => { exact absMulCase3 x y p q }
  | Sum.inr p, Sum.inr q => { exact absMulCase4 x y p q }
end

/-- c ≠ 0 なら 0 < |c| -/
hott lemma absPos {c : ℝ} (nz : c ≠ 0) : 0 < abs c :=
⟨λ r, nz (abs.zeroIf c (Id.symm r)), abs.geZero c⟩

/-- 正数の逆元も正 -/
hott lemma invPosStr {a : ℝ} (p : 0 < a) : 0 < @ring.hasInv.inv R.τ _ a :=
⟨λ r, @field.propInv R.τ _ a (λ s, p.1 (Id.symm s)) (Id.symm r), invPos p⟩

/-- ε·|c|⁻¹ は正 -/
hott definition absInv (c : ℝ) : ℝ := @ring.hasInv.inv R.τ _ (abs c)

hott lemma epsAbsPos {c ε : ℝ} (p : 0 < ε) (nz : c ≠ 0) : 0 < ε * absInv c :=
  mulPos p (invPosStr (absPos nz))

/-- 逆元キャンセル: |c|·(ε·|c|⁻¹) = ε -/
hott lemma invCancel {c ε : ℝ} (nz : c ≠ 0) :
  abs c * (ε * absInv c) = ε :=
calc abs c * (ε * absInv c)
     = (abs c * ε) * absInv c :
         Id.symm (@ring.assoc.mulAssoc R.τ _ (abs c) ε (absInv c)),
     = (ε * abs c) * absInv c :
         ap (· * absInv c) (@ring.comm.mulComm R.τ _ (abs c) ε),
     = ε * (abs c * absInv c) :
         @ring.assoc.mulAssoc R.τ _ ε (abs c) (absInv c),
     = ε * 1 : ap (ε * ·) (@field.mulRightInv R.τ _ (abs c) (λ r, nz (abs.zeroIf c r))),
     = ε : @ring.monoid.mulOne R.τ _ ε

/-- 極限の外延性: 点別に等しい列の conv は交換できる -/
hott lemma subCongEq (x y L : ℝ) (p : x = y) : x - L = y - L := ap (· + (-L)) p

hott lemma convExt (a b : ℕ → ℝ) (L : ℝ) (p : Π n, a n = b n) (h : conv a L) : conv b L :=
λ ε q, ⟨(h ε q).1, λ n s, Equiv.transport (λ w, R.ρ w ε) (ap abs (subCongEq (a n) (b n) L (p n))) ((h ε q).2 n s)⟩
/-- c = 0 のとき c·x = 0 -/
hott lemma mulZeroEq {c : ℝ} (z : c = 0) (x : ℝ) : c * x = 0 :=
  ap (· * x) z ⬝ @ring.zeroMul R.τ _ x

/-- c = 0 のとき conv (λ n, c·aₙ) (c·A)（transport ベース） -/
hott lemma convScaleZero (c : ℝ) (a : ℕ → ℝ) (A : ℝ) (z : c = 0) : conv (λ n, c * a n) (c * A) :=
  Equiv.transport (λ L, conv (λ n, c * a n) L) (Id.symm (mulZeroEq z A))
    (convExt (λ n, 0) (λ n, c * a n) 0 (λ n, Id.symm (mulZeroEq z (a n))) (convConst 0))

hott lemma convScale (c : ℝ) (a : ℕ → ℝ) (A : ℝ) (ha : conv a A) : conv (λ n, c * a n) (c * A) :=
begin
  intro ε p;
  match @GroundZero.Theorems.Classical.lem _ (c = 0) (R.hset _ _) with
  | Sum.inl z => exact convScaleZero c a A z ε p
  | Sum.inr nz => exact ⟨(ha (ε * absInv c) (epsAbsPos p nz)).1, λ n r,
      Equiv.transport (λ w, R.ρ (abs (c * a n - c * A)) w) (invCancel nz)
        (Equiv.transport (λ w, R.ρ w (abs c * (ε * absInv c)))
          (Id.symm (ap abs (distMul c (a n) A) ⬝ absMul c (a n - A)))
          (mulLeMono ((ha (ε * absInv c) (epsAbsPos p nz)).2 n r) (abs.geZero c)))⟩
end

/-- 部分和の線型結合は conv する（convAdd + convScale の合成） -/
hott lemma convLin (a b : ℝ) (f g : ℕ → ℝ) (SF SG : ℝ)
  (hF : conv (λ n, sum (Nat.succ n) f) SF)
  (hG : conv (λ n, sum (Nat.succ n) g) SG) :
  conv (λ n, sum (Nat.succ n) (λ m, a * f m + b * g m)) (a * SF + b * SG) :=
convExt (λ n, a * sum (Nat.succ n) f + b * sum (Nat.succ n) g)
        (λ n, sum (Nat.succ n) (λ m, a * f m + b * g m))
        (a * SF + b * SG)
        (λ n, Id.symm (calc sum (Nat.succ n) (λ m, a * f m + b * g m)
              = sum (Nat.succ n) (λ m, a * f m) + sum (Nat.succ n) (λ m, b * g m) :
                  Id.symm (sumAdd (Nat.succ n) (λ m, a * f m) (λ m, b * g m)),
              = a * sum (Nat.succ n) f + sum (Nat.succ n) (λ m, b * g m) :
                  ap (· + sum (Nat.succ n) (λ m, b * g m)) (Id.symm (mulSum a (Nat.succ n) f)),
              = a * sum (Nat.succ n) f + b * sum (Nat.succ n) g :
                  ap (a * sum (Nat.succ n) f + ·) (Id.symm (mulSum b (Nat.succ n) g))))
        (convAdd (λ n, a * sum (Nat.succ n) f) (λ n, b * sum (Nat.succ n) g) (a * SF) (b * SG)
          (convScale a (λ n, sum (Nat.succ n) f) SF hF)
          (convScale b (λ n, sum (Nat.succ n) g) SG hG))

/-- 線型性公理 infSumLin の定理化: 極限理論は線型性を吸収する -/
hott theorem infSumLinD (a b : ℝ) (f g : ℕ → ℝ) (SF SG : ℝ)
  (hF : conv (λ n, sum (Nat.succ n) f) SF)
  (hG : conv (λ n, sum (Nat.succ n) g) SG) :
  infiniteSum (λ m, a * f m + b * g m) = a * infiniteSum f + b * infiniteSum g :=
calc
  infiniteSum (λ m, a * f m + b * g m)
     = a * SF + b * SG : infSumIsLim (λ m, a * f m + b * g m) (a * SF + b * SG)
                           (convLin a b f g SF SG hF hG),     = a * infiniteSum f + b * infiniteSum g :
         ap (a * SF + ·) (ap (b * ·) (Id.symm (infSumIsLim g SG hG))) ⬝
         ap (· + b * infiniteSum g) (ap (a * ·) (Id.symm (infSumIsLim f SF hF)))

  /-- 自己テスト（AIPROVER §8.7 の規約）: conv の基本性質がビルド時に検証される -/
  hott example : conv (λ n, (1 : ℝ)) (1 : ℝ) := convConst 1

  /-- 自己テスト: infSumLinD を SF = infiniteSum f で適用する形（収束仮定は仮定のまま）。
      型検査が通ること + infSumLinD の公理依存（{infSumIsLim}）がビルドに固定される -/
  hott example (a b : ℝ) (f g : ℕ → ℝ) :
    conv (λ n, sum (Nat.succ n) f) (infiniteSum f) →
    conv (λ n, sum (Nat.succ n) g) (infiniteSum g) →
    infiniteSum (λ m, a * f m + b * g m) = a * infiniteSum f + b * infiniteSum g :=
  infSumLinD a b f g (infiniteSum f) (infiniteSum g)



  /-
    ============================================================================
    追記評価10（統合済み）: conv 仮説付き有限 Fubini — infSumLin 公理の吸収
    ============================================================================
    目的: infSumFinSwap が依存する「極限の線型性」公理 infSumLin を、
    収束仮定（conv 仮説）付きの定理版（infSumLinD ベース）に置き換え、
    gaussPsdD から infSumLin を吸収する。

    追加した部品（すべて infSumIsLim + conv 理論から導出、公理ゼロ追加）:
      · convEq          収束の極限は外延的（conv a L → L = M → conv a M）
      · convAddFin      convAdd の有限閉包（各行の収束 → n 行の和の収束）
      · infSumZeroLim   infiniteSum (λ m, 0) = 0（infSumZero は infSumLin 公理
                        由来のため、infSumIsLim から独立に導出）
      · infSumScaleConv スカラーの無限和内外移動（収束仮定付き）
      · infSumAddConv   無限和の加法性（収束仮定付き）
      · infSumScale2Conv infSumScale2 の収束仮定付き版
      · convScaleSum    スカラー倍級数の収束
      · scalarPullR     (a·(b·d))·t = a·(b·t·d)（行変換のリング補題）
      · sumSwapInfConv  有限 Fubini（各行の級数収束を仮定）— infSumLin 非依存
      · infSumFinSwapConv 有限2次形式と無限和の交換（hK 仮説付き）
                        #print axioms = {infSumIsLim, ...} — infSumLin 消滅

    gaussPsdD は infSumFinSwapConv に張り替え、conv 仮説 hK を convExpD
    （既存公理）から供給する → gaussPsdD の依存から infSumLin が消える。

    追記評価10 補遺（infSumLin 使用箇所の棚卸し — #print axioms 実測）:
    infSumLin に依存する宣言は以下に限られる（2026-08-11 実測）:
      · 本ファイル内の派生チェーン 6 件: infSumAdd / infSumScale /
        infSumZero / sumSwapInf / infSumScale2 / infSumFinSwap —
        すべて本セクションの conv 仮説版（infSumAddConv / infSumScaleConv /
        infSumZeroLim / sumSwapInfConv / infSumScale2Conv /
        infSumFinSwapConv、{infSumIsLim} のみ依存）で置換可能。ただし
        これらは互いと gaussPsd にしか使われていない内部補題であり、
        置換しても公理面は変化しない。
      · 外部の唯一の入口: gaussPsd（exp ワールド、{exp, expAdd, expSeries,
        infSumNonneg, infSumLin} 依存）。conv 仮説版への張り替えは追記評価11
        までは PosDef↔BinomTaylor の依存循環で不可能だった（convExpD / expD が
        BinomTaylor 側にあり、PosDef は BinomTaylor を import できない）。
        追記評価11 で expD / expDSeries / convExpD / convAbsExpD を本ファイルの
        Stage D′ へ移設し、追記評価12 で binomTaylor チェーン + expAddD + D ワールド
        群も本ファイルへ統合したため循環は完全に解消。D ワールド清浄版
        gaussPsdD は本ファイル内（追記評価12 セクション、{convExpD, convAbsExpD,
        infSumIsLim, mertens, infSumNonneg}）が担う。
      · 推移的利用: KernelLearn.gramNonneg / rbfPsd（gaussPsd 経由）。
      · 非依存を確認: KernelUniversal（exp / expAdd のみ）、BinomTaylor チェーン、
        RBF / Sample / Bad（infiniteSum 不使用）。
    完全除去の経路: (1) ✅ 済（追記評価11）: expD / expDSeries / convExpD /
    convAbsExpD を PosDef へ移設（Stage D′ セクション。部品 rpow / fac /
    rdiv / infiniteSum / conv / sum は Reals.lean または PosDef 内にあり移設
    可能）。依存循環は解消し、BinomTaylor は open PosDef で短縮名参照する。
    #print axioms 実測で gaussPsdD の 5 公理 {convExpD, convAbsExpD,
    infSumIsLim, mertens, infSumNonneg} は不変（公理名のみ PosDef. 接頭辞に
    移動）。→ (2) ✅ 済（追記評価12）: binomTaylor チェーン + expAddD + D ワールド
    群（gaussKernelD / expTripleD / gaussDecompD / expMidD / gaussKernelDSeries /
    gaussPsdD）を本ファイルへ統合し、gaussPsdD が PosDef 層で再証明された
    （#print axioms 実測: {convExpD, convAbsExpD, infSumIsLim, mertens,
    infSumNonneg} の 5 公理。exp ブロック・infSumLin に非依存）。→ (3)(4) ✅ 済
    （追記評価14）: expEqExpD（expSeries + expDSeries から導出、公理ゼロ追加なし）
    と gaussPsdDE（exp 版 gaussKernel の PSD、gaussPsdD から点別転送）を追加し、
    KernelLearn.gramNonneg / rbfPsd を gaussPsdDE に切替。これにより infSumLin
    公理と派生チェーン 6 件（infSumAdd / infSumScale / infSumZero / sumSwapInf /
    infSumScale2 / infSumFinSwap）、および exp ワールド gaussPsd は削除された
    （#print axioms 実測: gaussPsdDE は {convExpD, convAbsExpD, infSumIsLim,
    mertens, infSumNonneg, exp, expAdd, expSeries}、infSumLin はライブラリから消滅）。
    expSummand / gaussKernel は残存（D ワールド expMidD / KernelLearn が使用）。
  -/


  /-- 収束の極限は外延的: conv a L と L = M から conv a M -/
  hott lemma convEq (a : ℕ → ℝ) (L M : ℝ) (p : L = M) (h : conv a L) : conv a M :=
  Equiv.transport (λ X, conv a X) p h

  /-- convAdd の有限閉包: 各行が収束すれば、各 k ごとの n 行の和も収束する -/
  hott lemma convAddFin (n : ℕ) (a : ℕ → ℕ → ℝ) (L : ℕ → ℝ)
    (h : Π i, conv (λ k, a i k) (L i)) : conv (λ k, sum n (λ i, a i k)) (sum n L) :=
  begin
    induction n with
    | zero =>
        exact convExt (λ k, (0 : ℝ)) (λ k, sum 0 (λ i, a i k)) 0 (λ k, by reflexivity) (convConst 0)
    | succ n ih =>
        have hstep : conv (λ k, sum n (λ i, a i k) + a n k) (sum n L + L n) :=
          convAdd (λ k, sum n (λ i, a i k)) (λ k, a n k) (sum n L) (L n) ih (h n)
        exact convEq (λ k, sum (Nat.succ n) (λ i, a i k)) (sum n L + L n) (sum (Nat.succ n) L)
          (by reflexivity)
          (convExt (λ k, sum n (λ i, a i k) + a n k) (λ k, sum (Nat.succ n) (λ i, a i k))
            (sum n L + L n) (λ k, by reflexivity) hstep)
  end

  /-- 零列の無限和: infiniteSum (λ m, 0) = 0（infSumIsLim のみから導出。
      infSumZero は infSumLin 公理由来なので使わない） -/
  hott lemma infSumZeroLim : infiniteSum (λ m, (0 : ℝ)) = 0 :=
  infSumIsLim (λ m, (0 : ℝ)) 0
    (convExt (λ n, (0 : ℝ)) (λ n, sum (Nat.succ n) (λ m, (0 : ℝ))) 0
      (λ n, Id.symm (sumZero (Nat.succ n))) (convConst 0))

  /-- スカラーを無限和の外へ（収束仮定付き）: infiniteSum (λ m, a * f m) = a * infiniteSum f。
    追記評価10: これは infSumLin 公理由来の infSumScale の「収束仮定付き・公理ゼロ」版。
    D ワールドではこちらを使うこと（infSumScale に戻すと infSumLin が再流入する）。 -/
  hott theorem infSumScaleConv (a : ℝ) (f : ℕ → ℝ) (SF : ℝ)
    (hF : conv (λ n, sum (Nat.succ n) f) SF) :
    infiniteSum (λ m, a * f m) = a * infiniteSum f :=
  calc infiniteSum (λ m, a * f m)
       = infiniteSum (λ m, a * f m + (0 : ℝ) * f m) :
           Id.symm (infiniteSum.ext (λ m, a * f m + (0 : ℝ) * f m) (λ m, a * f m)
             (λ m, calc a * f m + (0 : ℝ) * f m = a * f m + 0 : ap (a * f m + ·) (@ring.zeroMul R.τ _ (f m)),
                      = a * f m : R.τ.addZero (a * f m))),
       = a * infiniteSum f + (0 : ℝ) * infiniteSum f : infSumLinD a (0 : ℝ) f f SF SF hF hF,
       = a * infiniteSum f :
           calc a * infiniteSum f + (0 : ℝ) * infiniteSum f = a * infiniteSum f + 0 : ap (a * infiniteSum f + ·) (@ring.zeroMul R.τ _ (infiniteSum f)),
                = a * infiniteSum f : R.τ.addZero (a * infiniteSum f)

  /-- 無限和の加法性（収束仮定付き）: infiniteSum (f + g) = infiniteSum f + infiniteSum g -/
  hott lemma infSumAddConv (f g : ℕ → ℝ) (SF SG : ℝ)
    (hF : conv (λ n, sum (Nat.succ n) f) SF)
    (hG : conv (λ n, sum (Nat.succ n) g) SG) :
    infiniteSum (λ m, f m + g m) = infiniteSum f + infiniteSum g :=
  calc infiniteSum (λ m, f m + g m)
       = infiniteSum (λ m, (1 : ℝ) * f m + (1 : ℝ) * g m) :
           Id.symm (infiniteSum.ext (λ m, (1 : ℝ) * f m + (1 : ℝ) * g m) (λ m, f m + g m)
             (λ m, calc (1 : ℝ) * f m + (1 : ℝ) * g m = f m + (1 : ℝ) * g m : ap (· + (1 : ℝ) * g m) (@ring.monoid.oneMul R.τ _ (f m)),
                      = f m + g m : ap (f m + ·) (@ring.monoid.oneMul R.τ _ (g m)))),
       = (1 : ℝ) * infiniteSum f + (1 : ℝ) * infiniteSum g : infSumLinD (1 : ℝ) (1 : ℝ) f g SF SG hF hG,
       = infiniteSum f + infiniteSum g :
           calc (1 : ℝ) * infiniteSum f + (1 : ℝ) * infiniteSum g = infiniteSum f + (1 : ℝ) * infiniteSum g : ap (· + (1 : ℝ) * infiniteSum g) (@ring.monoid.oneMul R.τ _ (infiniteSum f)),
                = infiniteSum f + infiniteSum g : ap (infiniteSum f + ·) (@ring.monoid.oneMul R.τ _ (infiniteSum g))

  /-- 定数スカラーのくくり出し（収束仮定付き）: a·(b·infiniteSum h·t) = infiniteSum (λ m, a·(b·h m·t)) -/
  hott lemma infSumScale2Conv (a b t : ℝ) (h : ℕ → ℝ)
    (hconv : conv (λ k, sum (Nat.succ k) h) (infiniteSum h)) :
    a * (b * infiniteSum h * t) = infiniteSum (λ m, a * (b * h m * t)) :=
  calc a * (b * infiniteSum h * t)
       = (a * (b * t)) * infiniteSum h :
           (calc a * (b * infiniteSum h * t) = a * ((b * infiniteSum h) * t) : by reflexivity,
                = (a * (b * infiniteSum h)) * t : Id.symm (@ring.assoc.mulAssoc R.τ _ a (b * infiniteSum h) t),
                = ((a * b) * infiniteSum h) * t : ap (· * t) (Id.symm (@ring.assoc.mulAssoc R.τ _ a b (infiniteSum h))),
                = ((a * b) * t) * infiniteSum h :
                    (calc ((a * b) * infiniteSum h) * t = (a * b) * (infiniteSum h * t) : @ring.assoc.mulAssoc R.τ _ (a * b) (infiniteSum h) t,
                         = (a * b) * (t * infiniteSum h) : ap ((a * b) * ·) (@ring.comm.mulComm R.τ _ (infiniteSum h) t),
                         = ((a * b) * t) * infiniteSum h : Id.symm (@ring.assoc.mulAssoc R.τ _ (a * b) t (infiniteSum h))),
                = (a * (b * t)) * infiniteSum h : ap (· * infiniteSum h) (@ring.assoc.mulAssoc R.τ _ a b t)),
       = infiniteSum (λ m, (a * (b * t)) * h m) : Id.symm (infSumScaleConv (a * (b * t)) h (infiniteSum h) hconv),
       = infiniteSum (λ m, a * (b * h m * t)) :
           infiniteSum.ext (λ m, (a * (b * t)) * h m) (λ m, a * (b * h m * t))
             (λ m, calc (a * (b * t)) * h m = a * ((b * t) * h m) : @ring.assoc.mulAssoc R.τ _ a (b * t) (h m),
                      = a * (b * (t * h m)) : ap (a * ·) (@ring.assoc.mulAssoc R.τ _ b t (h m)),
                      = a * (b * (h m * t)) : ap (a * ·) (ap (b * ·) (@ring.comm.mulComm R.τ _ t (h m))),
                      = a * ((b * h m) * t) : ap (a * ·) (Id.symm (@ring.assoc.mulAssoc R.τ _ b (h m) t)),
                      = a * (b * h m * t) : by reflexivity)

  /-- スカラー倍された級数の収束（hK から）: Σ (s·K) は infiniteSum (s·K) に収束 -/
  hott lemma convScaleSum (s : ℝ) (K : ℕ → ℝ)
    (hK : conv (λ k, sum (Nat.succ k) K) (infiniteSum K)) :
    conv (λ k, sum (Nat.succ k) (λ m, s * K m)) (infiniteSum (λ m, s * K m)) :=
  convEq (λ k, sum (Nat.succ k) (λ m, s * K m))
    (s * infiniteSum K) (infiniteSum (λ m, s * K m))
    (Id.symm (infSumScaleConv s K (infiniteSum K) hK))
    (convExt (λ k, s * sum (Nat.succ k) K) (λ k, sum (Nat.succ k) (λ m, s * K m))
      (s * infiniteSum K)
      (λ k, mulSum s (Nat.succ k) K)
      (convScale s (λ k, sum (Nat.succ k) K) (infiniteSum K) hK))

  /-- 有限 Fubini（収束仮定付き）: Σⱼ infiniteSum g j = infiniteSum (λ m, Σⱼ g j m)。
      infSumLinD（{infSumIsLim} のみ）から導出。 -/
  hott theorem sumSwapInfConv (n : ℕ) (g : ℕ → ℕ → ℝ)
    (hG : Π j, conv (λ k, sum (Nat.succ k) (λ m, g j m)) (infiniteSum (λ m, g j m))) :
    sum n (λ j, infiniteSum (λ m, g j m)) = infiniteSum (λ m, sum n (λ j, g j m)) :=
  begin
    induction n with
    | zero =>
        exact calc sum 0 (λ j, infiniteSum (λ m, g j m)) = 0 : by reflexivity,
             = infiniteSum (λ m, (0 : ℝ)) : Id.symm infSumZeroLim,
             = infiniteSum (λ m, sum 0 (λ j, g j m)) : Id.symm (infiniteSum.ext (λ m, (0 : ℝ)) (λ m, sum 0 (λ j, g j m)) (λ m, by reflexivity))
    | succ n ih =>
        -- 収束仮説 hA の極限は ih（帰納仮説）で同定する。conv 仮説は任意の
        -- 極限値を持つ命題なので、これは循環ではなく健全な構成。
        have hA : conv (λ k, sum (Nat.succ k) (λ m, sum n (λ j, g j m)))
                       (infiniteSum (λ m, sum n (λ j, g j m))) :=
          convEq (λ k, sum (Nat.succ k) (λ m, sum n (λ j, g j m)))
            (sum n (λ j, infiniteSum (λ m, g j m))) (infiniteSum (λ m, sum n (λ j, g j m))) ih
            (convExt (λ k, sum n (λ j, sum (Nat.succ k) (λ m, g j m)))
                     (λ k, sum (Nat.succ k) (λ m, sum n (λ j, g j m)))
                     (sum n (λ j, infiniteSum (λ m, g j m)))
                     (λ k, sumSwap n (Nat.succ k) (λ j m, g j m))
                     (convAddFin n (λ j k, sum (Nat.succ k) (λ m, g j m))
                                 (λ j, infiniteSum (λ m, g j m)) hG))
        exact calc sum (Nat.succ n) (λ j, infiniteSum (λ m, g j m))
               = sum n (λ j, infiniteSum (λ m, g j m)) + infiniteSum (λ m, g n m) : by reflexivity,
             = infiniteSum (λ m, sum n (λ j, g j m)) + infiniteSum (λ m, g n m) : ap (· + infiniteSum (λ m, g n m)) ih,
             = infiniteSum (λ m, sum n (λ j, g j m) + g n m) :
                 Id.symm (infSumAddConv (λ m, sum n (λ j, g j m)) (λ m, g n m)
                   (infiniteSum (λ m, sum n (λ j, g j m))) (infiniteSum (λ m, g n m)) hA (hG n)),
             = infiniteSum (λ m, sum (Nat.succ n) (λ j, g j m)) :
                 infiniteSum.ext (λ m, sum n (λ j, g j m) + g n m) (λ m, sum (Nat.succ n) (λ j, g j m)) (λ m, by reflexivity)
  end

  /-- リング再配置: (a·(b·d))·t = a·(b·t·d)（hrow の行変換に使用） -/
  hott lemma scalarPullR (a b t d : ℝ) : (a * (b * d)) * t = a * (b * t * d) :=
  calc (a * (b * d)) * t = ((a * b) * d) * t : ap (· * t) (Id.symm (@ring.assoc.mulAssoc R.τ _ a b d)),
       = (a * b) * (d * t) : @ring.assoc.mulAssoc R.τ _ (a * b) d t,
       = (a * b) * (t * d) : ap ((a * b) * ·) (@ring.comm.mulComm R.τ _ d t),
       = a * (b * (t * d)) : @ring.assoc.mulAssoc R.τ _ a b (t * d),
       = a * ((b * t) * d) : ap (a * ·) (Id.symm (@ring.assoc.mulAssoc R.τ _ b t d)),
       = a * (b * t * d) : by reflexivity

  /-- 有限2次形式と無限和の交換（収束仮定付き）: 各行 K m (x i) (x j) の級数が収束すれば、
      infSumLin（公理）を使わず infSumLinD（{infSumIsLim} のみ）から導出できる -/
  hott theorem infSumFinSwapConv (f : ℝ → ℝ) (K : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (c : ℕ → ℝ) (x : ℕ → ℝ)
    (hK : Π i j, conv (λ k, sum (Nat.succ k) (λ m, K m (x i) (x j))) (infiniteSum (λ m, K m (x i) (x j)))) :
    quadForm (λ x y, f x * infiniteSum (λ m, K m x y) * f y) n c x =
    infiniteSum (λ m, quadForm (λ x y, f x * K m x y * f y) n c x) :=
  begin
    unfold quadForm;
    have hrow : Π i j, conv (λ k, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
                            (infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))) :=
    begin
      intro i j;
      let s : ℝ := (c i * c j) * (f (x i) * f (x j));
      have hpt : Π m, s * K m (x i) (x j) = (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)) :=
        λ m, scalarPullR (c i * c j) (f (x i)) (K m (x i) (x j)) (f (x j));
      exact convEq (λ k, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
        (infiniteSum (λ m, s * K m (x i) (x j)))
        (infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
        (infiniteSum.ext (λ m, s * K m (x i) (x j)) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))) hpt)
        (convExt (λ k, sum (Nat.succ k) (λ m, s * K m (x i) (x j)))
                 (λ k, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
                 (infiniteSum (λ m, s * K m (x i) (x j)))
                 (λ k, sum.ext (Nat.succ k) (λ m, hpt m))
                 (convScaleSum s (λ m, K m (x i) (x j)) (hK i j)))
    end;
    have hrow2 : Π i, conv (λ k, sum (Nat.succ k) (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
                           (infiniteSum (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))) :=
    begin
      intro i;
      have hbase : conv (λ k, sum n (λ j, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
                        (sum n (λ j, infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))) :=
        convAddFin n (λ j k, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
                    (λ j, infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))) (hrow i);
      exact convEq (λ k, sum (Nat.succ k) (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
        (sum n (λ j, infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
        (infiniteSum (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
        (sumSwapInfConv n (λ j m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))) (hrow i))
        (convExt (λ k, sum n (λ j, sum (Nat.succ k) (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
                 (λ k, sum (Nat.succ k) (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
                 (sum n (λ j, infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))))
                 (λ k, sumSwap n (Nat.succ k) (λ j m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))
                 hbase)
    end;
    exact calc sum n (λ i, sum n (λ j, (c i * c j) * (f (x i) * infiniteSum (λ m, K m (x i) (x j)) * f (x j))))
         = sum n (λ i, sum n (λ j, infiniteSum (λ m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))) :
             sum.ext n (λ i, sum.ext n (λ j,
               infSumScale2Conv (c i * c j) (f (x i)) (f (x j)) (λ m, K m (x i) (x j)) (hK i j))),
         = sum n (λ i, infiniteSum (λ m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))) :
             sum.ext n (λ i, sumSwapInfConv n (λ j m, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))) (hrow i)),
         = infiniteSum (λ m, sum n (λ i, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j))))) :
             sumSwapInfConv n (λ i m, sum n (λ j, (c i * c j) * (f (x i) * K m (x i) (x j) * f (x j)))) hrow2
  end

  /-- 定数スカラーのくくり出し: a·(b·c)·d = b·(a·c·d) -/
  hott lemma scalarPull (a b c d : ℝ) : a * (b * c) * d = b * (a * c * d) :=
  calc a * (b * c) * d = ((a * b) * c) * d : ap (· * d) (Id.symm (@ring.assoc.mulAssoc R.τ _ a b c)),
       = ((b * a) * c) * d : ap (· * d) (ap (· * c) (@ring.comm.mulComm R.τ _ a b)),
       = (b * (a * c)) * d : ap (· * d) (@ring.assoc.mulAssoc R.τ _ b a c),
       = b * ((a * c) * d) : @ring.assoc.mulAssoc R.τ _ b (a * c) d


/- ============================================================
   追記評価12: binomTaylor チェーンと gaussPsdD の PosDef 統合（除去経路②）
   ============================================================
   BinomTaylor.lean にあった二項定理チェーン（nCr ... binomTaylor）・
   expAddD・D ワールドのガウスカーネル群（gaussKernelD / expTripleD /
   gaussDecompD / expMidD / gaussKernelDSeries / gaussPsdD）を本ファイルへ
   移設した。追記評価11 の expD / convExpD / convAbsExpD と合わせ、
   gaussPsd の D ワールド版 gaussPsdD が PosDef 層に揃う（#print axioms
   実測: {convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg} の
   5 公理。exp ブロック {exp, expAdd, expSeries} と infSumLin に非依存）。
   KernelLearn 等は PosDef を import するだけで gaussPsdD を利用できる。
   注意: チェーンの Nat 補題 subSelf（n - n = 0）は本ファイル既存の ℝ 版
   subSelf（x - x = 0）と衝突するため nSubSelf に改名した。 -/

/-- 二項係数（Pascal 再帰）: k ≤ n では n!/(k!(n-k)!)、それ以外は 0 -/
hott definition nCr : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, Nat.succ k => 0
  | Nat.succ n, 0 => 1
  | Nat.succ n, Nat.succ k => nCr n k + nCr n (Nat.succ k)

/-- Pascal: nCr (n+1) (k+1) = nCr n k + nCr n (k+1)（定義より rfl） -/
hott lemma nCrSuccSucc (n k : ℕ) :
  nCr (Nat.succ n) (Nat.succ k) = nCr n k + nCr n (Nat.succ k) := by reflexivity

/-- nCr n 0 = 1 -/
hott lemma nCrZero (n : ℕ) : nCr n 0 = 1 :=
begin
  induction n with
  | zero => reflexivity
  | succ n => reflexivity
end

/-- 0 + n = n（ℕ） -/
hott lemma zeroAddNat (n : ℕ) : 0 + n = n :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih =>
    exact calc 0 + Nat.succ n = Nat.succ (0 + n) : by reflexivity,
         = Nat.succ n : ap Nat.succ ih
end

/-- succ n + k = succ (n + k)（k 帰納法） -/
hott lemma succAdd (n k : ℕ) : Nat.succ n + k = Nat.succ (n + k) :=
begin
  induction k with
  | zero => reflexivity
  | succ k ih =>
    exact calc Nat.succ n + Nat.succ k = Nat.succ (Nat.succ n + k) : by reflexivity,
         = Nat.succ (Nat.succ (n + k)) : ap Nat.succ ih,
         = Nat.succ (n + Nat.succ k) : by reflexivity
end

/-- n + 0 = n -/
hott lemma addZero (n : ℕ) : n + 0 = n :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih => exact ap Nat.succ ih
end

/-- (n+1) - (k+1) = n - k（k 帰納法） -/
hott lemma succSubSucc (n k : ℕ) : Nat.succ n - Nat.succ k = n - k :=
begin
  induction k with
  | zero => reflexivity
  | succ k ih =>
    exact calc Nat.succ n - Nat.succ (Nat.succ k) = Nat.pred (Nat.succ n - Nat.succ k) : by reflexivity,
         = Nat.pred (n - k) : ap Nat.pred ih,
         = n - Nat.succ k : by reflexivity
end

/-- n - n = 0 -/
hott lemma nSubSelf (n : ℕ) : n - n = 0 :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih =>
    exact calc Nat.succ n - Nat.succ n = n - n : succSubSucc n n,
         = 0 : ih
end

/-- succ (succ n + k) = succ n + succ k -/
hott lemma succAddSucc (n k : ℕ) : Nat.succ (Nat.succ n + k) = Nat.succ n + Nat.succ k := by reflexivity

/-- 範囲外: nCr n (n+1+k) = 0 -/
hott lemma nCrAbove (n : ℕ) : Π (k : ℕ), nCr n (Nat.succ n + k) = 0 :=
begin
  induction n with
  | zero =>
    intro k
    induction k with
    | zero => reflexivity
    | succ k ihk => reflexivity
  | succ n ih =>
    intro k
    exact ap (nCr (Nat.succ n)) (succAdd (Nat.succ n) k) ⬝
      nCrSuccSucc n (Nat.succ n + k) ⬝
      ap (λ z, z + nCr n (Nat.succ (Nat.succ n + k))) (ih k) ⬝
      ap (0 + ·) (ap (nCr n) (succAddSucc n k) ⬝ ih (Nat.succ k)) ⬝
      (by reflexivity)
end

/-- nCr n (n+1) = 0（nCrAbove から k=0 を補正） -/
hott lemma nCrAboveSelf (n : ℕ) : nCr n (Nat.succ n) = 0 :=
ap (nCr n) (Id.symm (succAdd n 0 ⬝ ap Nat.succ (addZero n))) ⬝ nCrAbove n 0

/-- 対角: nCr n n = 1 -/
hott lemma nCrDiag (n : ℕ) : nCr n n = 1 :=
begin
  induction n with
  | zero => reflexivity
  | succ n ih =>
    exact nCrSuccSucc n n ⬝
      ap (λ z, z + nCr n (Nat.succ n)) ih ⬝
      ap (1 + ·) (nCrAboveSelf n) ⬝
      (by reflexivity)
end

/-- k ≤ n → k ≤ n+1（ライブラリ le.step を直接使用; n+1 ≡ Nat.succ n） -/
hott lemma leSuccRight (k n : ℕ) (ρ : k ≤ n) : k ≤ Nat.succ n :=
le.step k n ρ

/-- k ≤ n → (n+1) - k = (n - k) + 1。
    定義的パターンマッチ（ライブラリ流）で h を破壊せずに進める。
    これは cases タクティクがパス仮説に Eq.rec を導入するのを避けるため。 -/
hott lemma succSubLe : Π (n k : ℕ), k ≤ n → Nat.succ n - k = Nat.succ (n - k)
  | Nat.zero,   Nat.zero,   _ => idp _
  | Nat.zero,   Nat.succ k', h => explode (max.neZero h)
  | Nat.succ n, Nat.zero,   _ => idp _
  | Nat.succ n, Nat.succ k', h => succSubSucc (Nat.succ n) k' ⬝ succSubLe n k' (le.inj k' n h) ⬝ ap Nat.succ (Id.symm (succSubSucc n k'))

/-- sum (n+1) f = f 0 + sum n (λ k, f (k+1))（先頭を剥がす） -/
hott lemma sumShift (n : ℕ) (f : ℕ → ℝ) : sum (Nat.succ n) f = f 0 + sum n (λ k, f (Nat.succ k)) :=
begin
  induction n with
  | zero =>
    exact calc sum 1 f = 0 + f 0 : by reflexivity,
         = f 0 : R.τ⁺.oneMul (f 0),
         = f 0 + sum 0 (λ k, f (Nat.succ k)) : Id.symm (R.τ.addZero (f 0))
  | succ n ih =>
    exact calc sum (Nat.succ (Nat.succ n)) f
             = sum (Nat.succ n) f + f (Nat.succ n) : by reflexivity,
         = (f 0 + sum n (λ k, f (Nat.succ k))) + f (Nat.succ n) : ap (· + f (Nat.succ n)) ih,
         = f 0 + (sum n (λ k, f (Nat.succ k)) + f (Nat.succ n)) : R.τ⁺.mulAssoc (f 0) (sum n (λ k, f (Nat.succ k))) (f (Nat.succ n)),
         = f 0 + sum (Nat.succ n) (λ k, f (Nat.succ k)) : by reflexivity
end

/-- sumLe: 範囲制限付き ext。Π k, k ≤ n → f k = g k なら sum (n+1) f = sum (n+1) g -/
hott lemma sumLe (n : ℕ) {f g : ℕ → ℝ} (p : Π (k : ℕ), k ≤ n → f k = g k) :
  sum (Nat.succ n) f = sum (Nat.succ n) g :=
begin
  induction n with
  | zero =>
    exact calc sum 1 f = 0 + f 0 : by reflexivity,
         = f 0 : R.τ⁺.oneMul (f 0),
         = g 0 : p 0 (max.zeroLeft 0),
         = 0 + g 0 : Id.symm (R.τ⁺.oneMul (g 0)),
         = sum 1 g : by reflexivity
  | succ n ih =>
    exact calc sum (Nat.succ (Nat.succ n)) f
             = sum (Nat.succ n) f + f (Nat.succ n) : by reflexivity,
         = sum (Nat.succ n) g + g (Nat.succ n) : ap (sum (Nat.succ n) f + ·) (p (Nat.succ n) (max.refl (Nat.succ n))) ⬝ ap (· + g (Nat.succ n)) (ih (λ k hk, p k (leSuccRight k n hk))),
         = sum (Nat.succ (Nat.succ n)) g : by reflexivity
end

/-- (a+b) + (c+d) = (c + (a+d)) + b -/
hott lemma addRearr2 (a b c d : ℝ) : (a + b) + (c + d) = (c + (a + d)) + b :=
calc (a + b) + (c + d) = (a + c) + (b + d) : addRearr a b c d,
     = (c + a) + (b + d) : ap (λ z, z + (b + d)) (R.τ.addComm a c),
     = (c + a) + (d + b) : ap ((c + a) + ·) (R.τ.addComm b d),
     = ((c + a) + d) + b : Id.symm (R.τ⁺.mulAssoc (c + a) d b),
     = (c + (a + d)) + b : ap (λ z, z + b) (R.τ⁺.mulAssoc c a d)

/-- a·(b·c) = b·(a·c) -/
hott lemma swapInner (a b c : ℝ) : a * (b * c) = b * (a * c) :=
calc a * (b * c) = (a * b) * c : Id.symm (@ring.assoc.mulAssoc R.τ _ a b c),
     = (b * a) * c : ap (· * c) (@ring.comm.mulComm R.τ _ a b),
     = b * (a * c) : @ring.assoc.mulAssoc R.τ _ b a c

/-- (x·y·z)·a = (x·(y·a))·z -/
hott lemma mulAssocShift (x y z a : ℝ) : (x * y * z) * a = (x * (y * a)) * z :=
calc (x * y * z) * a = (x * y) * (z * a) : @ring.assoc.mulAssoc R.τ _ (x * y) z a,
     = x * (y * (z * a)) : @ring.assoc.mulAssoc R.τ _ x y (z * a),
     = x * ((y * a) * z) : ap (x * ·) (swapInner y z a ⬝ @ring.comm.mulComm R.τ _ z (y * a)),
     = (x * (y * a)) * z : Id.symm (@ring.assoc.mulAssoc R.τ _ x (y * a) z)

/-- (x·y·z)·b = x·(y·(z·b)) -/
hott lemma mulAssocShift2 (x y z b : ℝ) : (x * y * z) * b = x * (y * (z * b)) :=
calc (x * y * z) * b = (x * y) * (z * b) : @ring.assoc.mulAssoc R.τ _ (x * y) z b,
     = x * (y * (z * b)) : @ring.assoc.mulAssoc R.τ _ x y (z * b)

/-- 指数の succ 則: t^(n+1) = tⁿ · t（rpow の定義より rfl） -/
hott lemma rpowSucc (t : ℝ) (n : ℕ) : rpow t (Nat.succ n) = rpow t n * t := by reflexivity

/-- x·1 = x（変数経由で ring.monoid.mulOne を呼ぶ） -/
hott lemma mulOneL (x : ℝ) : x * 1 = x := @ring.monoid.mulOne R.τ _ x

/-- 1·x = x -/
hott lemma oneMulL (x : ℝ) : 1 * x = x := @ring.monoid.oneMul R.τ _ x

/-- N.incl 1 = 1 -/
hott lemma inclOne : N.incl 1 = 1 := R.τ⁺.oneMul (1 : ℝ)

/-- a 側の指数繰り込み: (c·aᵏ·bⁿ⁻ᵏ)·a = c·aᵏ⁺¹·bⁿ⁻ᵏ -/
hott lemma perA (n k : ℕ) (a b : ℝ) :
  (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a
  = N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k) :=
calc (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a
     = (N.incl (nCr n k) * (rpow a k * a)) * rpow b (n - k) : mulAssocShift (N.incl (nCr n k)) (rpow a k) (rpow b (n - k)) a,
     = (N.incl (nCr n k) * rpow a (Nat.succ k)) * rpow b (n - k) : ap (λ w, (N.incl (nCr n k) * w) * rpow b (n - k)) (Id.symm (rpowSucc a k)),
     = N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k) : by reflexivity

/-- b 側の指数繰り込み: (c·aᵏ·bⁿ⁻ᵏ)·b = c·aᵏ·b^(n+1-k)（k ≤ n） -/
hott lemma perB (n k : ℕ) (a b : ℝ) (hk : k ≤ n) :
  (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b
  = N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k) :=
calc (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b
     = N.incl (nCr n k) * (rpow a k * (rpow b (n - k) * b)) : mulAssocShift2 (N.incl (nCr n k)) (rpow a k) (rpow b (n - k)) b,
     = N.incl (nCr n k) * (rpow a k * rpow b (Nat.succ (n - k))) : ap (λ w, N.incl (nCr n k) * (rpow a k * w)) (Id.symm (rpowSucc b (n - k))),
     = N.incl (nCr n k) * (rpow a k * rpow b (Nat.succ n - k)) : ap (λ w, N.incl (nCr n k) * (rpow a k * w)) (Id.symm (ap (rpow b) (succSubLe n k hk))),
     = N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k) : Id.symm (@ring.assoc.mulAssoc R.τ _ (N.incl (nCr n k)) (rpow a k) (rpow b (Nat.succ n - k)))

/-- 中央項の合成: g(k+1) + h(k+1) = c(k+1)（Pascal + N.incl.add） -/
hott lemma perC (n k : ℕ) (a b : ℝ) :
  N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)
    + N.incl (nCr n (Nat.succ k)) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)
  = N.incl (nCr (Nat.succ n) (Nat.succ k)) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k) :=
calc N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)
       + N.incl (nCr n (Nat.succ k)) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)
     = N.incl (nCr n k) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k))
         + N.incl (nCr n (Nat.succ k)) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k))
         : ap (· + (N.incl (nCr n (Nat.succ k)) * rpow a (Nat.succ k)) * rpow b (Nat.succ n - Nat.succ k)) (@ring.assoc.mulAssoc R.τ _ (N.incl (nCr n k)) (rpow a (Nat.succ k)) (rpow b (Nat.succ n - Nat.succ k))) ⬝ ap (N.incl (nCr n k) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)) + ·) (@ring.assoc.mulAssoc R.τ _ (N.incl (nCr n (Nat.succ k))) (rpow a (Nat.succ k)) (rpow b (Nat.succ n - Nat.succ k))),
     = (N.incl (nCr n k) + N.incl (nCr n (Nat.succ k))) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)) : Id.symm (@ring.distribRight R.τ _ (N.incl (nCr n k)) (N.incl (nCr n (Nat.succ k))) (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k))),
     = N.incl (nCr n k + nCr n (Nat.succ k)) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)) : ap (λ w, w * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k))) (Id.symm (N.incl.add (nCr n k) (nCr n (Nat.succ k)))),
     = N.incl (nCr (Nat.succ n) (Nat.succ k)) * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k)) : ap (λ w, w * (rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k))) (ap N.incl (Id.symm (nCrSuccSucc n k))),
     = N.incl (nCr (Nat.succ n) (Nat.succ k)) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k) : Id.symm (@ring.assoc.mulAssoc R.τ _ (N.incl (nCr (Nat.succ n) (Nat.succ k))) (rpow a (Nat.succ k)) (rpow b (Nat.succ n - Nat.succ k)))

/-- g(k+1) の指数書き換え: A k = g (succ k)（k ≤ n） -/
hott lemma perG (n k : ℕ) (a b : ℝ) (hk : k ≤ n) :
  N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k)
  = N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (Nat.succ n - Nat.succ k) :=
ap (λ z, N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b z) (Id.symm (succSubSucc n k))

/-- 境界: h 0 = c 0（両辺 = b^(n+1)） -/
hott lemma h0Eq (n : ℕ) (a b : ℝ) :
  N.incl (nCr n 0) * rpow a 0 * rpow b (Nat.succ n - 0)
  = N.incl (nCr (Nat.succ n) 0) * rpow a 0 * rpow b (Nat.succ n - 0) :=
ap (λ z, N.incl z * rpow a 0 * rpow b (Nat.succ n - 0)) (nCrZero n ⬝ Id.symm (nCrZero (Nat.succ n)))

/-- 境界: g (n+1) = c (n+1)（両辺 = a^(n+1)） -/
hott lemma gNp1Eq (n : ℕ) (a b : ℝ) :
  N.incl (nCr n ((Nat.succ n) - 1)) * rpow a (Nat.succ n) * rpow b (Nat.succ n - Nat.succ n)
  = N.incl (nCr (Nat.succ n) (Nat.succ n)) * rpow a (Nat.succ n) * rpow b (Nat.succ n - Nat.succ n) :=
calc N.incl (nCr n ((Nat.succ n) - 1)) * rpow a (Nat.succ n) * rpow b (Nat.succ n - Nat.succ n)
     = N.incl (nCr n n) * rpow a (Nat.succ n) * rpow b (n - n) : ap (λ z, N.incl (nCr n n) * rpow a (Nat.succ n) * rpow b z) (succSubSucc n n),
     = N.incl (nCr (Nat.succ n) (Nat.succ n)) * rpow a (Nat.succ n) * rpow b (n - n) : ap (λ z, z * rpow a (Nat.succ n) * rpow b (n - n)) (ap N.incl (nCrDiag n)) ⬝ ap (λ z, z * rpow a (Nat.succ n) * rpow b (n - n)) (Id.symm (ap N.incl (nCrDiag (Nat.succ n)))),
     = N.incl (nCr (Nat.succ n) (Nat.succ n)) * rpow a (Nat.succ n) * rpow b (Nat.succ n - Nat.succ n) : Id.symm (ap (λ z, N.incl (nCr (Nat.succ n) (Nat.succ n)) * rpow a (Nat.succ n) * rpow b z) (succSubSucc n n))

/-- 二項定理: (a+b)ⁿ = Σ_{k=0}^{n} nCr n k · aᵏ · bⁿ⁻ᵏ -/
hott theorem binom (a b : ℝ) (n : ℕ) :
  rpow (a + b) n = sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (n - k)) :=
begin
  induction n with
  | zero =>
    exact calc rpow (a + b) 0 = 1 : by reflexivity,
         = N.incl (nCr 0 0) * rpow a 0 * rpow b (0 - 0) : Id.symm (calc (N.incl 1 * 1) * 1 = N.incl 1 * 1 : ap (· * 1) (mulOneL (N.incl 1)), = N.incl 1 : mulOneL (N.incl 1), = 1 : inclOne),
         = sum 1 (λ k, N.incl (nCr 0 k) * rpow a k * rpow b (0 - k)) : Id.symm (calc sum 1 (λ k, N.incl (nCr 0 k) * rpow a k * rpow b (0 - k)) = 0 + (N.incl (nCr 0 0) * rpow a 0 * rpow b (0 - 0)) : by reflexivity, = N.incl (nCr 0 0) * rpow a 0 * rpow b (0 - 0) : R.τ⁺.oneMul (N.incl (nCr 0 0) * rpow a 0 * rpow b (0 - 0)))
  | succ n ih =>
    let g : ℕ → ℝ := λ j, N.incl (nCr n (j - 1)) * rpow a j * rpow b (Nat.succ n - j)
    let h : ℕ → ℝ := λ k, N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k)
    let c : ℕ → ℝ := λ j, N.incl (nCr (Nat.succ n) j) * rpow a j * rpow b (Nat.succ n - j)
    have dist : rpow (a + b) (Nat.succ n) =
        sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a)
        + sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b) :=
    calc rpow (a + b) (Nat.succ n)
         = rpow (a + b) n * (a + b) : by reflexivity,
         = (sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (n - k))) * (a + b) : ap (· * (a + b)) ih,
         = sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * (a + b)) : Id.symm (sumMul (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (n - k)) (a + b)),
         = sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a + (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b) : sum.ext (Nat.succ n) (λ k, @ring.distribLeft R.τ _ (N.incl (nCr n k) * rpow a k * rpow b (n - k)) a b),
         = sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a) + sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b) : Id.symm (sumAdd (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * a) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b))
    have sumA : rpow (a + b) (Nat.succ n) =
        sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k))
        + sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k)) :=
    dist ⬝
      ap (λ x, x + sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * b))
         (sum.ext (Nat.succ n) (λ k, perA n k a b)) ⬝
      ap (sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k)) + ·)
         (sumLe n (λ k hk, perB n k a b hk))
    have split2 : sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k))
        = h 0 + sum n (λ k, h (Nat.succ k)) := sumShift n h
    have split1 : sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k))
        = sum n (λ k, g (Nat.succ k)) + g (Nat.succ n) :=
    calc sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a (Nat.succ k) * rpow b (n - k))
         = sum (Nat.succ n) (λ k, g (Nat.succ k)) : sumLe n (λ k hk, perG n k a b hk),
         = sum n (λ k, g (Nat.succ k)) + g (Nat.succ n) : by reflexivity
    have asm : rpow (a + b) (Nat.succ n) = (c 0 + sum n (λ k, c (Nat.succ k))) + c (Nat.succ n) :=
    calc rpow (a + b) (Nat.succ n)
         = (sum n (λ k, g (Nat.succ k)) + g (Nat.succ n)) + (h 0 + sum n (λ k, h (Nat.succ k))) : sumA ⬝ ap (λ x, x + sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (Nat.succ n - k))) split1 ⬝ ap ((sum n (λ k, g (Nat.succ k)) + g (Nat.succ n)) + ·) split2,
         = (h 0 + (sum n (λ k, g (Nat.succ k)) + sum n (λ k, h (Nat.succ k)))) + g (Nat.succ n) : addRearr2 (sum n (λ k, g (Nat.succ k))) (g (Nat.succ n)) (h 0) (sum n (λ k, h (Nat.succ k))),
         = (h 0 + sum n (λ k, g (Nat.succ k) + h (Nat.succ k))) + g (Nat.succ n) : ap (λ z, (h 0 + z) + g (Nat.succ n)) (sumAdd n (λ k, g (Nat.succ k)) (λ k, h (Nat.succ k))),
         = (h 0 + sum n (λ k, c (Nat.succ k))) + g (Nat.succ n) : ap (λ z, (h 0 + z) + g (Nat.succ n)) (sum.ext n (λ k, perC n k a b)),
         = (c 0 + sum n (λ k, c (Nat.succ k))) + c (Nat.succ n) : ap (λ z, (z + sum n (λ k, c (Nat.succ k))) + g (Nat.succ n)) (h0Eq n a b) ⬝ ap (λ z, (c 0 + sum n (λ k, c (Nat.succ k))) + z) (gNp1Eq n a b)
    exact asm ⬝ Id.symm (calc sum (Nat.succ (Nat.succ n)) c
             = sum (Nat.succ n) c + c (Nat.succ n) : by reflexivity,
         = (c 0 + sum n (λ k, c (Nat.succ k))) + c (Nat.succ n) : ap (· + c (Nat.succ n)) (sumShift n c))
end

/-==============================================================================
  階乗正規化: nCr n k · k! · (n-k)! = n!（k ≤ n）の証明
  =============================================================================-/

/-- k ≤ n なら k + (n - k) = n -/
hott lemma plusMinus : Π (n k : ℕ), k ≤ n → k + (n - k) = n
  | Nat.zero, Nat.zero, _ => by reflexivity
  | Nat.zero, Nat.succ k', h => explode (max.neZero h)
  | Nat.succ n, Nat.zero, _ =>
    calc 0 + (Nat.succ n - 0) = 0 + Nat.succ n : by reflexivity,
         = Nat.succ n : zeroAddNat (Nat.succ n)
  | Nat.succ n, Nat.succ k', h =>
    calc Nat.succ k' + (Nat.succ n - Nat.succ k') = Nat.succ k' + (n - k') : ap (Nat.succ k' + ·) (succSubSucc n k'),
         = Nat.succ (k' + (n - k')) : succAdd k' (n - k'),
         = Nat.succ n : ap Nat.succ (plusMinus n k' (le.inj k' n h))

/-- succ k ≤ n なら n - k = succ (n - succ k) -/
hott lemma subSuccSplit : Π (n k : ℕ), Nat.succ k ≤ n → n - k = Nat.succ (n - Nat.succ k)
  | Nat.zero, Nat.zero, h => explode (max.neZero h)
  | Nat.zero, Nat.succ k', h => explode (max.neZero h)
  | Nat.succ n, Nat.zero, h => by reflexivity
  | Nat.succ n, Nat.succ k', h =>
    calc (Nat.succ n) - (Nat.succ k') = n - k' : succSubSucc n k',
         = Nat.succ (n - Nat.succ k') : subSuccSplit n k' (le.inj (Nat.succ k') n h),
         = Nat.succ (Nat.succ n - Nat.succ (Nat.succ k')) : ap Nat.succ (Id.symm (succSubSucc n (Nat.succ k')))

/-- succ k ≤ n なら succ k + (n - k) = succ n -/
hott lemma plusMinusSucc (n k : ℕ) (hk : Nat.succ k ≤ n) :
  Nat.succ k + (n - k) = Nat.succ n :=
calc Nat.succ k + (n - k) = Nat.succ k + Nat.succ (n - Nat.succ k) : ap (Nat.succ k + ·) (subSuccSplit n k hk),
     = Nat.succ (Nat.succ k + (n - Nat.succ k)) : by reflexivity,
     = Nat.succ n : ap Nat.succ (plusMinus n (Nat.succ k) hk)

/-- k ≤ n の二分割: 対角 (k = n) か内部 (succ k ≤ n) -/
hott lemma leDich : Π (n k : ℕ), k ≤ n → Coproduct (k = n) (Nat.succ k ≤ n)
  | Nat.zero, Nat.zero, h => Sum.inl (idp Nat.zero)
  | Nat.zero, Nat.succ k', h => explode (max.neZero h)
  | Nat.succ n, Nat.zero, h => Sum.inr (by reflexivity ⬝ ap Nat.succ (max.zeroLeft n))
  | Nat.succ n, Nat.succ k', h =>
  begin
    induction (leDich n k' (le.inj k' n h)) with
    | inl heq => exact Sum.inl (ap Nat.succ heq)
    | inr hint => exact Sum.inr (by reflexivity ⬝ ap Nat.succ hint)
  end

/-- (x·(y·z))·w = ((x·y)·w)·z（結合・交換の整理） -/
hott lemma mulShiftRight (x y z w : ℝ) : (x * (y * z)) * w = ((x * y) * w) * z :=
calc (x * (y * z)) * w = x * ((y * z) * w) : @ring.assoc.mulAssoc R.τ _ x (y * z) w,
     = x * (y * (z * w)) : ap (x * ·) (@ring.assoc.mulAssoc R.τ _ y z w),
     = x * (y * (w * z)) : ap (x * ·) (ap (y * ·) (@ring.comm.mulComm R.τ _ z w)),
     = x * ((y * w) * z) : ap (x * ·) (Id.symm (@ring.assoc.mulAssoc R.τ _ y w z)),
     = (x * (y * w)) * z : Id.symm (@ring.assoc.mulAssoc R.τ _ x (y * w) z),
     = ((x * y) * w) * z : ap (· * z) (Id.symm (@ring.assoc.mulAssoc R.τ _ x y w))

/-- succ k ≤ n なら fac (n - k) = fac (n - succ k) · N.incl (n - k) -/
hott lemma facSubSplit (n k : ℕ) (hk : Nat.succ k ≤ n) :
  fac (n - k) = fac (n - Nat.succ k) * N.incl (n - k) :=
calc fac (n - k) = fac (Nat.succ (n - Nat.succ k)) : ap fac (subSuccSplit n k hk),
     = fac (n - Nat.succ k) * N.incl (Nat.succ (n - Nat.succ k)) : by reflexivity,
     = fac (n - Nat.succ k) * N.incl (n - k) : ap (λ z, fac (n - Nat.succ k) * N.incl z) (Id.symm (subSuccSplit n k hk))

/-- 対角: nCr n n · n! · 0! = n! -/
hott lemma nCrFacDiag (n : ℕ) : (N.incl (nCr n n) * fac n) * fac (n - n) = fac n :=
ap (λ z, (N.incl z * fac n) * fac (n - n)) (nCrDiag n) ⬝
ap (λ z, (N.incl 1 * fac n) * z) (ap fac (nSubSelf n)) ⬝
ap (λ z, (z * fac n) * 1) inclOne ⬝
ap (· * 1) (oneMulL (fac n)) ⬝
mulOneL (fac n)

/-- 階乗正規化: nCr n k · k! · (n-k)! = n!（k ≤ n） -/
hott lemma nCrFac : Π (n k : ℕ), k ≤ n → (N.incl (nCr n k) * fac k) * fac (n - k) = fac n
  | Nat.zero, Nat.zero, h =>
    (by reflexivity : (N.incl (nCr 0 0) * fac 0) * fac (0 - 0) = (N.incl 1 * 1) * 1) ⬝
    ap (λ z, (z * 1) * 1) inclOne ⬝
    ap (· * 1) (oneMulL (1 : ℝ)) ⬝
    mulOneL (1 : ℝ)
  | Nat.zero, Nat.succ k', h => explode (max.neZero h)
  | Nat.succ n, Nat.zero, h =>
    (by reflexivity : (N.incl (nCr (Nat.succ n) 0) * fac 0) * fac (Nat.succ n - 0) = (N.incl 1 * 1) * fac (Nat.succ n)) ⬝
    ap (λ z, (z * 1) * fac (Nat.succ n)) inclOne ⬝
    ap (· * fac (Nat.succ n)) (oneMulL (1 : ℝ)) ⬝
    oneMulL (fac (Nat.succ n))
  | Nat.succ n, Nat.succ k', h =>
  begin
    induction (leDich n k' (le.inj k' n h)) with
    | inl heq =>
        exact Equiv.transport (λ m, (N.incl (nCr (Nat.succ n) (Nat.succ m)) * fac (Nat.succ m)) * fac (Nat.succ n - Nat.succ m) = fac (Nat.succ n)) (Id.symm heq) (nCrFacDiag (Nat.succ n))
    | inr hint =>
        let X : ℝ := N.incl (nCr n k')
        let Y : ℝ := N.incl (nCr n (Nat.succ k'))
        let M : ℝ := fac k' * N.incl (Nat.succ k')
        let D : ℝ := fac (n - k')
        have ih1 : (X * fac k') * D = fac n := nCrFac n k' (le.inj k' n h)
        have ih2 : (Y * fac (Nat.succ k')) * fac (n - Nat.succ k') = fac n := nCrFac n (Nat.succ k') hint
        have term1 : (X * M) * D = fac n * N.incl (Nat.succ k') :=
        calc (X * M) * D = ((X * fac k') * D) * N.incl (Nat.succ k') : mulShiftRight X (fac k') (N.incl (Nat.succ k')) D,
             = fac n * N.incl (Nat.succ k') : ap (· * N.incl (Nat.succ k')) ih1
        have term2 : (Y * M) * D = fac n * N.incl (n - k') :=
        calc (Y * M) * D = (Y * fac (Nat.succ k')) * fac (n - k') : by reflexivity,
             = (Y * fac (Nat.succ k')) * (fac (n - Nat.succ k') * N.incl (n - k')) : ap (λ z, (Y * fac (Nat.succ k')) * z) (facSubSplit n k' hint),
             = ((Y * fac (Nat.succ k')) * fac (n - Nat.succ k')) * N.incl (n - k') : Id.symm (@ring.assoc.mulAssoc R.τ _ (Y * fac (Nat.succ k')) (fac (n - Nat.succ k')) (N.incl (n - k'))),
             = fac n * N.incl (n - k') : ap (· * N.incl (n - k')) ih2
        exact calc (N.incl (nCr (Nat.succ n) (Nat.succ k')) * fac (Nat.succ k')) * fac (Nat.succ n - Nat.succ k')
             = (N.incl (nCr n k' + nCr n (Nat.succ k')) * (fac k' * N.incl (Nat.succ k'))) * fac (Nat.succ n - Nat.succ k') : by reflexivity,
             = (N.incl (nCr n k' + nCr n (Nat.succ k')) * (fac k' * N.incl (Nat.succ k'))) * fac (n - k') : ap (λ z, (N.incl (nCr n k' + nCr n (Nat.succ k')) * (fac k' * N.incl (Nat.succ k'))) * fac z) (succSubSucc n k'),
             = ((N.incl (nCr n k') + N.incl (nCr n (Nat.succ k'))) * (fac k' * N.incl (Nat.succ k'))) * fac (n - k') : ap (λ z, (z * (fac k' * N.incl (Nat.succ k'))) * fac (n - k')) (N.incl.add (nCr n k') (nCr n (Nat.succ k'))),
             = ((X * M + Y * M) * D) : ap (· * D) (@ring.distribRight R.τ _ (N.incl (nCr n k')) (N.incl (nCr n (Nat.succ k'))) M),
             = (X * M) * D + (Y * M) * D : @ring.distribRight R.τ _ (X * M) (Y * M) D,
             = fac n * N.incl (Nat.succ k') + fac n * N.incl (n - k') : ap (· + (Y * M) * D) term1 ⬝ ap (fac n * N.incl (Nat.succ k') + ·) term2,
             = fac n * (N.incl (Nat.succ k') + N.incl (n - k')) : Id.symm (@ring.distribLeft R.τ _ (fac n) (N.incl (Nat.succ k')) (N.incl (n - k'))),
             = fac n * N.incl (Nat.succ k' + (n - k')) : ap (fac n * ·) (Id.symm (N.incl.add (Nat.succ k') (n - k'))),
             = fac n * N.incl (Nat.succ n) : ap (fac n * ·) (ap N.incl (plusMinusSucc n k' hint)),
             = fac (Nat.succ n) : by reflexivity
  end

/-==============================================================================
  除法セクション: 階乗の可逆性・逆元の一意性・二項定理の階乗正規化
  =============================================================================-/

/-- 逆元（型を ℝ に揃えるためのラッパー。ℝ 表記と R.τ.carrier の
    型クラス解決のズレを回避する） -/
hott def rin (x : ℝ) : ℝ :=
@ring.hasInv.inv R.τ _ x

/-- 0 < a なら a は可逆（isproper） -/
hott lemma posProper (a : ℝ) (p : 0 < a) : @Prering.isproper R.τ _ a :=
λ s, p.1 (Id.symm s)

/-- 階乗は可逆: isproper (fac n) -/
hott lemma facProper (n : ℕ) : @Prering.isproper R.τ _ (fac n) :=
posProper (fac n) (facPos n)

/-- x·y = 1 かつ x 可逆なら y = x⁻¹（逆元の一意性） -/
hott lemma invEqOfMulEqOne {x y : ℝ} (p : @Prering.isproper R.τ _ x) (h : x * y = 1) :
  y = @ring.hasInv.inv R.τ _ x :=
calc y = 1 * y : Id.symm (@ring.monoid.oneMul R.τ _ y),
     = (rin x * x) * y : ap (· * y) (Id.symm (@ring.divisible.mulLeftInv R.τ _ x p)),
     = rin x * (x * y) : @ring.assoc.mulAssoc R.τ _ (rin x) x y,
     = rin x * 1 : ap (rin x * ·) h,
     = rin x : @ring.monoid.mulOne R.τ _ (rin x)

/-- (c·A·B)·F = A·(B·(c·F))（可換環の並べ替え） -/
hott lemma divRearr (c A B F : ℝ) : (c * A * B) * F = A * (B * (c * F)) :=
calc (c * A * B) * F = c * (A * (B * F)) : mulAssocShift2 c A B F,
     = A * (c * (B * F)) : swapInner c A (B * F),
     = A * (B * (c * F)) : ap (A * ·) (swapInner c B F)

/-- A·(B·(X·Y)) = (A·X)·(B·Y)（middleFour の変種） -/
hott lemma mulInvSwap (A X B Y : ℝ) : A * (B * (X * Y)) = (A * X) * (B * Y) :=
calc A * (B * (X * Y)) = (A * B) * (X * Y) : Id.symm (@ring.assoc.mulAssoc R.τ _ A B (X * Y)),
     = (A * X) * (B * Y) : middleFour A B X Y

/-- 係数分解 L: (k!·(n-k)!)·(nCr·(n!)⁻¹) = 1（逆元の一意性用の左式） -/
hott lemma nCrDivL (n k : ℕ) (hk : k ≤ n) :
  (fac k * fac (n - k)) * (N.incl (nCr n k) * rin (fac n)) = 1 :=
calc (fac k * fac (n - k)) * (N.incl (nCr n k) * rin (fac n))
     = ((fac k * fac (n - k)) * N.incl (nCr n k)) * rin (fac n) : Id.symm (@ring.assoc.mulAssoc R.τ _ (fac k * fac (n - k)) (N.incl (nCr n k)) (rin (fac n))),
     = (N.incl (nCr n k) * (fac k * fac (n - k))) * rin (fac n) : ap (· * rin (fac n)) (@ring.comm.mulComm R.τ _ (fac k * fac (n - k)) (N.incl (nCr n k))),
     = ((N.incl (nCr n k) * fac k) * fac (n - k)) * rin (fac n) : ap (· * rin (fac n)) (Id.symm (@ring.assoc.mulAssoc R.τ _ (N.incl (nCr n k)) (fac k) (fac (n - k)))),
     = fac n * rin (fac n) : ap (· * rin (fac n)) (nCrFac n k hk),
     = 1 : @field.mulRightInv R.τ _ (fac n) (facProper n)

/-- 係数分解 R: (k!·(n-k)!)·((k!)⁻¹·((n-k)!)⁻¹) = 1（逆元の一意性用の右式） -/
hott lemma nCrDivR (n k : ℕ) (hk : k ≤ n) :
  (fac k * fac (n - k)) * (rin (fac k) * rin (fac (n - k))) = 1 :=
calc (fac k * fac (n - k)) * (rin (fac k) * rin (fac (n - k)))
     = fac k * (fac (n - k) * (rin (fac k) * rin (fac (n - k)))) : @ring.assoc.mulAssoc R.τ _ (fac k) (fac (n - k)) (rin (fac k) * rin (fac (n - k))),
     = (fac k * rin (fac k)) * (fac (n - k) * rin (fac (n - k))) : mulInvSwap (fac k) (rin (fac k)) (fac (n - k)) (rin (fac (n - k))),
     = 1 : ap (· * (fac (n - k) * rin (fac (n - k)))) (@field.mulRightInv R.τ _ (fac k) (facProper k)) ⬝ ap ((1 : ℝ) * ·) (@field.mulRightInv R.τ _ (fac (n - k)) (facProper (n - k))) ⬝ oneMulL (1 : ℝ)

/-- 係数分解: nCr n k · (n!)⁻¹ = (k!)⁻¹ · ((n-k)!)⁻¹（k ≤ n） -/
hott lemma nCrDiv (n k : ℕ) (hk : k ≤ n) :
  N.incl (nCr n k) * rin (fac n) = rin (fac k) * rin (fac (n - k)) :=
invEqOfMulEqOne (field.properMul (facProper k) (facProper (n - k))) (nCrDivL n k hk) ⬝
Id.symm (invEqOfMulEqOne (field.properMul (facProper k) (facProper (n - k))) (nCrDivR n k hk))

/-- 点別の階乗正規化: 生の二項項 · (n!)⁻¹ = aᵏ/k! · bⁿ⁻ᵏ/(n-k)!（k ≤ n） -/
hott lemma binomTaylorPw (a b : ℝ) (n k : ℕ) (hk : k ≤ n) :
  (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * rin (fac n)
  = rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k)) :=
calc (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * rin (fac n)
     = rpow a k * (rpow b (n - k) * (N.incl (nCr n k) * rin (fac n))) : divRearr (N.incl (nCr n k)) (rpow a k) (rpow b (n - k)) (rin (fac n)),
     = rpow a k * (rpow b (n - k) * (rin (fac k) * rin (fac (n - k)))) : ap (λ z, rpow a k * (rpow b (n - k) * z)) (nCrDiv n k hk),
     = (rpow a k * rin (fac k)) * (rpow b (n - k) * rin (fac (n - k))) : mulInvSwap (rpow a k) (rin (fac k)) (rpow b (n - k)) (rin (fac (n - k))),
     = rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k)) : by reflexivity

/-- 二項定理の階乗正規化形（binomTaylor）: (a+b)ⁿ/n! = Σₖ aᵏ/k! · bⁿ⁻ᵏ/(n-k)! -/
hott theorem binomTaylor (a b : ℝ) (n : ℕ) :
  rdiv (rpow (a + b) n) (fac n) =
  sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k))) :=
begin
  exact calc rdiv (rpow (a + b) n) (fac n)
       = rpow (a + b) n * rin (fac n) : by reflexivity,
       = (sum (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (n - k))) * rin (fac n) : ap (· * rin (fac n)) (binom a b n),
       = sum (Nat.succ n) (λ k, (N.incl (nCr n k) * rpow a k * rpow b (n - k)) * rin (fac n)) : Id.symm (sumMul (Nat.succ n) (λ k, N.incl (nCr n k) * rpow a k * rpow b (n - k)) (rin (fac n))),
       = sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k))) : sumLe n (λ k hk, binomTaylorPw a b n k hk)
end

/- ============================================================
   追記評価5（続き）: exp の級数再定義 — expD と expAddD
   ============================================================

   expD t := Σₙ tⁿ/n! を定義し、加法性 expAddD を
   binomTaylor + cauchyProductLim（定理）+ conv 仮説から導出する。
   旧版は cauchyProduct（公理）を使っていたが、追記評価7 で conv 仮説
   （convExpD / convAbsExpD）を整備し、公理を削除して定理に張り替えた。

   公理検証（#print axioms 実測）:
     expAddD = {convExpD, convAbsExpD, infSumIsLim, mertens, infiniteSum,
                infiniteSum.ext, R, R.dedekind, Quot.sound, GroundZero}
   → exp ブロックの公理 {exp, expZero, expAdd, expSeries} も cauchyProduct
     公理も expAddD に不要。
   gaussPsd の expD 張り替え（下の gaussPsdD）で実測: exp 3公理と
   cauchyProduct が消滅し、依存は {convExpD, convAbsExpD, infSumIsLim,
   mertens, infSumLin, infSumNonneg} に収束。
   infSumLin → infSumLinD の置換は収束仮説が必要（TODO）。 -/

/-- expAddD: expD (a+b) = expD a · expD b
    （binomTaylor + cauchyProductLim（定理）+ conv 仮説から導出。
      cauchyProduct 公理は追記評価7 で削除済み） -/
hott theorem expAddD (a b : ℝ) : expD (a + b) = expD a * expD b :=
calc expD (a + b)
     = infiniteSum (λ n, rdiv (rpow (a + b) n) (fac n)) : expDSeries (a + b),
     = infiniteSum (λ n, sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k)))) :
         infiniteSum.ext (λ n, rdiv (rpow (a + b) n) (fac n))
                         (λ n, sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k))))
                         (binomTaylor a b),
     = expD a * expD b :
         Id.symm (cauchyProductLim (λ k, rdiv (rpow a k) (fac k)) (λ l, rdiv (rpow b l) (fac l))
                            (expD a) (expD b) (convAbsExpD a).1 (convExpD a) (convExpD b) (convAbsExpD a).2)
/- ============================================================
   追記評価5（完結）: gaussPsd の expD 張り替え — gaussPsdD
   ============================================================

   PosDef.gaussPsd（exp 公理ベース）を expD ベースのガウスカーネル
   gaussKernelD に張り替えた gaussPsdD を証明する。gaussDecompD /
   expMidD / gaussKernelDSeries は exp 公理の代わりに expAddD /
   expDSeries（定理）を使う。

   公理検証（#print axioms 実測）:
     gaussPsdD = {GroundZero, convExpD, convAbsExpD, uaweak, uaweakβ,
                  infSumIsLim, infSumNonneg, mertens, Quot.sound,
                  R, infiniteSum, R.dedekind, infiniteSum.ext, choice}
   → exp ブロック {exp, expAdd, expSeries} の 3公理・cauchyProduct 公理・
      infSumLin 公理は完全に消滅（現行の実測値。追記評価7 の張り替え時点では
      infSumLin が残っていたが、追記評価10 で infSumFinSwapConv への張り替えに
      より吸収、追記評価12 で本ファイルへ統合）。
      （uaweak / uaweakβ / choice は PSD 機械由来の既存公理、infSumNonneg は
        PosDef の既存公理、infSumIsLim / mertens は追記評価6 の公理。追記評価7
        の張り替えで新たに加わったのは convExpD / convAbsExpD。）

   目標セット {expZero, infSumNonneg, infSumIsLim, mertens} との差分:
     convExpD / convAbsExpD の定理化（比較判定・比率判定、追記評価8）で
     {infSumNonneg, infSumLin} への完全縮減が可能（TODO）。 -/

/-- ガウスカーネル（expD 版）: K(x,y) = expD(-ε²(x-y)²) -/
hott definition gaussKernelD (ε x y : ℝ) : ℝ :=
expD (-((ε * ε) * sqr (x - y)))

/-- expD(a+b+c) = expD a·expD b·expD c（expTriple の expD 版） -/
hott lemma expTripleD (a b c : ℝ) : expD (a + b + c) = expD a * expD b * expD c :=
calc expD (a + b + c) = expD (a + b) * expD c : expAddD (a + b) c,
     = (expD a * expD b) * expD c : ap (· * expD c) (expAddD a b)

/-- ガウスの分解（expD 版）: expD(-ε²(x-y)²) = expD(-ε²x²)·expD(2ε²xy)·expD(-ε²y²) -/
hott lemma gaussDecompD (ε x y : ℝ) :
  expD (-((ε * ε) * sqr (x - y))) =
  expD (-((ε * ε) * sqr x)) * expD (((1 + 1) * (ε * ε)) * (x * y)) * expD (-((ε * ε) * sqr y)) :=
calc expD (-((ε * ε) * sqr (x - y)))
   = expD (-((ε * ε) * sqr x + (-(((1 + 1) * (ε * ε)) * (x * y))) + (ε * ε) * sqr y)) :
       ap expD (ap (λ z, -z) (mulDistSquare (ε * ε) x y)),
   = expD (-((ε * ε) * sqr x) + (-(-(((1 + 1) * (ε * ε)) * (x * y)))) + -((ε * ε) * sqr y)) :
       ap expD (negTriple ((ε * ε) * sqr x) (-(((1 + 1) * (ε * ε)) * (x * y))) ((ε * ε) * sqr y)),
   = expD (-((ε * ε) * sqr x) + (((1 + 1) * (ε * ε)) * (x * y)) + -((ε * ε) * sqr y)) :
       ap expD (ap (λ z, -((ε * ε) * sqr x) + z + -((ε * ε) * sqr y))
                  (@Group.invInv R.τ⁺ (((1 + 1) * (ε * ε)) * (x * y)))),
   = expD (-((ε * ε) * sqr x)) * expD (((1 + 1) * (ε * ε)) * (x * y)) * expD (-((ε * ε) * sqr y)) :
       expTripleD (-((ε * ε) * sqr x)) (((1 + 1) * (ε * ε)) * (x * y)) (-((ε * ε) * sqr y))

/-- expD(2ε²xy) = Σₙ cₙ·(xy)ⁿ（expDSeries + expSummand + 無限和の外延性） -/
hott lemma expMidD (ε x y : ℝ) :
  expD (((1 + 1) * (ε * ε)) * (x * y)) = infiniteSum (λ n, coeff ε n * rpow (x * y) n) :=
calc expD (((1 + 1) * (ε * ε)) * (x * y))
   = infiniteSum (λ n, rdiv (rpow (((1 + 1) * (ε * ε)) * (x * y)) n) (fac n)) :
     expDSeries (((1 + 1) * (ε * ε)) * (x * y)),
   = infiniteSum (λ n, coeff ε n * rpow (x * y) n) :
     infiniteSum.ext (λ n, rdiv (rpow (((1 + 1) * (ε * ε)) * (x * y)) n) (fac n))
                     (λ n, coeff ε n * rpow (x * y) n) (λ n, expSummand ε x y n)

/-- ガウスカーネル（expD 版）の級数表現 -/
hott lemma gaussKernelDSeries (ε x y : ℝ) :
  gaussKernelD ε x y =
  expD (-((ε * ε) * sqr x)) * infiniteSum (λ n, coeff ε n * rpow (x * y) n) * expD (-((ε * ε) * sqr y)) :=
calc gaussKernelD ε x y
   = expD (-((ε * ε) * sqr x)) * expD (((1 + 1) * (ε * ε)) * (x * y)) * expD (-((ε * ε) * sqr y)) :
     gaussDecompD ε x y,
   = expD (-((ε * ε) * sqr x)) * infiniteSum (λ n, coeff ε n * rpow (x * y) n) * expD (-((ε * ε) * sqr y)) :
     ap (λ z, expD (-((ε * ε) * sqr x)) * z * expD (-((ε * ε) * sqr y))) (expMidD ε x y)

/-- ガウスカーネル（expD 版）の PSD — PosDef.gaussPsd の expD 張り替え版。
    追記評価10: infSumFinSwap を infSumFinSwapConv（収束仮定付き）に張り替え、
    conv 仮説 hK を convExpD（既存公理）から供給 → 依存から infSumLin が消える。 -/
hott theorem gaussPsdD (ε : ℝ) : PSD (λ x y, gaussKernelD ε x y) :=
begin
  unfold PSD; intro n c x;
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (sum.ext n (λ i, sum.ext n (λ j,
    ap (λ z, (c i * c j) * z) (gaussKernelDSeries ε (x i) (x j)))));
  let f : ℝ → ℝ := λ z, expD (-((ε * ε) * sqr z));
  have hK : Π i j, conv (λ k, sum (Nat.succ k) (λ m, coeff ε m * rpow ((x i) * (x j)) m))
                        (infiniteSum (λ m, coeff ε m * rpow ((x i) * (x j)) m)) :=
    (λ i j, convEq (λ k, sum (Nat.succ k) (λ m, coeff ε m * rpow ((x i) * (x j)) m))
      (expD (((1 + 1) * (ε * ε)) * ((x i) * (x j))))
      (infiniteSum (λ m, coeff ε m * rpow ((x i) * (x j)) m))
      (expMidD ε (x i) (x j))
      (convExt (λ k, sum (Nat.succ k) (λ m, rdiv (rpow (((1 + 1) * (ε * ε)) * ((x i) * (x j))) m) (fac m)))
               (λ k, sum (Nat.succ k) (λ m, coeff ε m * rpow ((x i) * (x j)) m))
               (expD (((1 + 1) * (ε * ε)) * ((x i) * (x j))))
               (λ k, sum.ext (Nat.succ k) (λ m, expSummand ε (x i) (x j) m))
               (convExpD (((1 + 1) * (ε * ε)) * ((x i) * (x j))))));
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (infSumFinSwapConv f (λ m x y, coeff ε m * rpow (x * y) m) n c x hK);
  apply infSumNonneg; intro m;
  apply Equiv.transport (R.ρ 0);
  exact Id.symm (calc quadForm (λ x y, f x * (coeff ε m * rpow (x * y) m) * f y) n c x
     = quadForm (λ x y, coeff ε m * (f x * rpow (x * y) m * f y)) n c x :
         sum.ext n (λ i, sum.ext n (λ j,
           ap (λ z, (c i * c j) * z)
              (scalarPull (f (x i)) (coeff ε m) (rpow ((x i) * (x j)) m) (f (x j))))),
     = coeff ε m * quadForm (λ x y, f x * rpow (x * y) m * f y) n c x :
         quadFormScale (coeff ε m) n c x,
     = coeff ε m * quadForm (λ x y, rpow (x * y) m) n (λ i, c i * f (x i)) x :
         ap (coeff ε m * ·) (quadFormRank1Scale f n c x));
  apply orfield.leOverMul;
  exact coeffNonneg ε m;
  apply polyKernelPsd m n (λ i, c i * f (x i)) x
end

  /-
    ============================================================================
    追記評価2: 2つの実解析公理を sup（Dedekind 完備性）から導出できるか
    ============================================================================

    前節の gaussPsd は残りの解析的内容を2つの公理（infSumNonneg, infSumFinSwap）
    に還元して完成した。本節では、これら2公理をライブラリ既存の
    sup / inf（Dedekind 完備性）ベースの級数理論から導出できるかを評価する。
    （追記評価4 との関係: 本節の結論は「sup からの導出は不能」であり、
    線型性公理 infSumLin を追加すれば交換則は定理になる — 末尾の追記評価4参照。
    両者は矛盾しない: sup は順序構造、infSumLin は線型構造という異なる公理
    からの話である。）

    結論（先に）:
      · infSumNonneg の「sup 版」は導出可能（下の infSumNonnegSup）。
        sup { sum n g | n } が非負であることは、0 = sum 0 g が部分和集合に
        含まれることから sup.lawful だけで閉じる（順序論的に自明）。
      · しかしこれは公理 infSumNonneg（infiniteSum についての主張）を
        導出しない。infiniteSum は sup と無関係な未解釈の公理記号であり、
        両者の同一視は証明なしに仮定できない（下の結論コメント参照）。
      · infSumFinSwap は導出不能（supNegDuality と反例 negSupNotSwapClosed
        が根拠）。sup は単調な操作（加法・非負スカラー倍）とのみ交換し、
        符号付きの線形汎関数（有限2次形式は cᵢcⱼ により符号を持つ）とは
        交換しない。正しい双対性は -(sup φ) = inf (Neg φ) であり inf が現れる。
        交換則の導出には sup ではなく「極限の線型性」（コーシー列・絶対収束
        の理論）が必要で、これはライブラリに未整備である。
    ============================================================================
  -/

  /-
    追記評価14（除去経路④）: exp ワールド gaussPsd と infSumLin チェーンを削除。
    gaussPsd の役割は gaussPsdDE（gaussPsdD からのブリッジ）が引き継いだ。
    exp と expD の一致（expEqExpD）は expSeries（Reals 公理）と expDSeries
    （定義）から公理なしで導出でき、PSD は点別一致で転送できる。
    ※ 追記評価17（追記評価16 (A) の実装）: KernelLearn.gram 系が gaussKernelD
      （D ワールド）に切替わったため gaussPsdDE は削除した。PSD は
      KernelLearn.gramNonneg が gaussPsdD を直接適用して担う。
  -/
  /-- exp と expD（級数再定義）の一致: expSeries + expDSeries から導出。
      追記評価17: gaussPsdDE 削除後も RBF ブリッジ（gaussKernelEqD → rbfGaussEqD）
      が使用するため残置。
      追記評価18: gaussKernelEqD / rbfGaussEqD は RBF 名義 PSD の D 化
      （gaussianRbfD）に伴い不要化し削除。本補題は exp と expD の接続
      （exp = 級数和）を述べる基本補題として保持（現在の使用箇所なし）。 -/
  hott lemma expEqExpD (a : ℝ) : exp a = expD a :=
  calc exp a = infiniteSum (λ n, rdiv (rpow a n) (fac n)) : expSeries a,
       = expD a : Id.symm (expDSeries a)

  /-
    ============================================================================
    追記評価15: gaussPsdDE の依存から expSeries を外せるか（評価）
    ============================================================================
    結論: 外せない。expSeries は「exp と級数の接続」として不可欠であり、
    conv 仮説（convExpD 等）への置換は公理数の削減にならない。

    現状の依存（#print axioms 実測）:
      · gaussPsdDE = {exp, expAdd, expSeries, infSumNonneg, convExpD,
        convAbsExpD, infSumIsLim, mertens}（8 実解析公理）
      · expEqExpD = {exp, expSeries, infiniteSum}（+ インフラ）
      · gaussPsdD  = {convExpD, convAbsExpD, infSumIsLim, mertens,
        infSumNonneg}（5 公理、exp 系ゼロ）— こちらは既に清浄。

    なぜ外せないか（構造的理由）:
      expEqExpD : exp a = expD a は「exp の級数分解」そのものの言い換えである。
      Reals の exp 公理は {expZero, expAdd, expSeries} の 3 つで、
      expZero + expAdd だけでは exp は決定されない（f(a+b) = f a · f b,
      f 0 = 1 を満たす関数は f a = cᵃ の形で任意 — c が自由）。
      exp を級数に固定しているのは expSeries ただ一つであり、conv 仮説
      （convExpD: 部分和 → expD a）は exp に一切言及しない。
      したがって conv 仮説のみから exp = expD を導出することはできない。

    等価言い換え（置換しても強さは同じ）:
      代替公理 convExp a : conv (部分和 Σₖ aᵏ/k!) (exp a) を仮定すると、
         convExp + infSumIsLim → expSeries の内容（exp a = infiniteSum 系列）
         expSeries + convExpD + convEq → convExp
      が両方向で導出でき（probe /tmp/eval15_equiv.lean、EXIT 0）、
      expSeries ↔ convExp は同値。公理数は 8 のまま変わらない。

    他の縮小経路:
      · gaussPsdDE を gaussKernelD（expD 版）で置き換え、exp 版カーネルの
        PSD を捨てる → gaussPsdD の 5 公理に落ちるが、KernelLearn.gram が
        exp 版 gaussKernel を使っているため rbfGaussEq 経由の RBF ブリッジ
        （exp 依存）は残る。exp ワールドを完全に廃止しない限り expSeries は
        どこかに必要。
      · exp を Reals で expD として定義し直す（再公理化）なら expSeries は
        定理化されるが、RBF / KernelUniversal の既存 exp 証明の全面改修になる。
    ============================================================================
  -/


  /-- 部分和の集合: series g = { sum n g | n : ℕ }（sup の対象） -/
  hott definition series (g : ℕ → ℝ) : R.subset :=
  ⟨λ x, ∥Σ n, x = sum n g∥, λ _, GroundZero.HITs.Merely.uniq⟩

  /-- series g は空でない: sum 0 g = 0 ∈ series g -/
  hott definition series.inh (g : ℕ → ℝ) : (series g).inh :=
  GroundZero.HITs.Merely.elem ⟨0, GroundZero.HITs.Merely.elem ⟨0, by reflexivity⟩⟩

  /-- 各部分和は sup 以下: sum n g ≤ sup { sum n g | n }（sup.lawful の直接適用） -/
  hott lemma sumLeSup (g : ℕ → ℝ) (G : @majorized R.κ (series g)) (n : ℕ) :
    R.ρ (sum n g) (sup (series g) (series.inh g) G) :=
  begin
    apply sup.lawful (series g) (series.inh g) G (sum n g);
    apply GroundZero.HITs.Merely.elem; existsi n; reflexivity
  end

  /-- 単調収束（sup 版の infSumNonneg）:
      sup { sum n g | n } は 0 以上。実際 0 = sum 0 g ∈ series g であり、
      sup.lawful だけで閉じる（g の非負性 p すら不要）。
      「非負項 → 級数は非負」の内容は sup の上では順序論的に自明である。 -/
  hott theorem infSumNonnegSup (g : ℕ → ℝ) (G : @majorized R.κ (series g)) :
    R.ρ 0 (sup (series g) (series.inh g) G) :=
  begin
    apply sup.lawful (series g) (series.inh g) G (sum 0 g);
    apply GroundZero.HITs.Merely.elem; existsi 0; reflexivity
  end

  /-- 符号反転した部分集合（Neg の T 推論が Alg.subset の既約性で詰まるため、
      change で型を橋渡しした別名を用意する） -/
  hott definition negφ (φ : R.subset) : R.subset :=
  begin change R.τ.subset; exact Neg φ end

  /-- negφ φ の空でなさ -/
  hott definition negφ.inh (φ : R.subset) (H : φ.inh) : (negφ φ).inh :=
  begin change (@Neg R.τ φ).inh;
        exact @Neg.inh R.τ _ φ H end

  /-- negφ φ は φ の下界の Neg として上に有界 -/
  hott definition negφ.majorized (φ : R.subset) (G : @minorized R.κ φ) :
    @majorized R.κ (negφ φ) :=
  begin change @majorized R.κ (@Neg R.τ φ);
        exact @Neg.majorized _ R _ φ G end

  /-- negφ φ は φ の上界の Neg として下に有界 -/
  hott definition negφ.minorized (φ : R.subset) (G : @majorized R.κ φ) :
    @minorized R.κ (negφ φ) :=
  begin change @minorized R.κ (@Neg R.τ φ);
        exact @Neg.minorized _ R _ φ G end

  /-- sup は符号反転と交換しない: -(sup φ) = inf (negφ φ)（正しい双対性）。
      つまり「-(sup φ) = sup (negφ φ)」型の交換は一般に偽であり、
      sup は単調な操作（加法・非負スカラー倍）とのみ交換する。 -/
  hott theorem supNegDuality (φ : R.subset) (H : φ.inh) (G : @majorized R.κ φ) :
    -(sup φ H G) = inf (negφ φ) (negφ.inh φ H) (negφ.minorized φ G) :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply inf.exact (negφ φ) (negφ.inh φ H) (negφ.minorized φ G) (-(sup φ H G));
      intros y p;
      apply Equiv.transport (λ w, R.ρ (-(sup φ H G)) w);
      apply @Group.invInv R.τ⁺;
      apply minusInvSign R (-y) (sup φ H G);
      apply sup.lawful φ H G (-y);
      exact p };
    { apply Equiv.transport (λ w, R.ρ w (-(sup φ H G)));
      apply @Group.invInv R.τ⁺;
      apply minusInvSign R (sup φ H G) (-(inf (negφ φ) (negφ.inh φ H) (negφ.minorized φ G)));
      apply sup.exact φ H G (-(inf (negφ φ) (negφ.inh φ H) (negφ.minorized φ G)));
      intros y p;
      apply Equiv.transport (λ w, R.ρ w (-(inf (negφ φ) (negφ.inh φ H) (negφ.minorized φ G))));
      apply @Group.invInv R.τ⁺;
      apply minusInvSign R (inf (negφ φ) (negφ.inh φ H) (negφ.minorized φ G)) (-y);
      apply inf.lawful (negφ φ) (negφ.inh φ H) (negφ.minorized φ G) (-y);
      apply Equiv.transport (· ∈ φ);
      symmetry; apply @Group.invInv R.τ⁺;
      exact p }
  end

  /-- 単位区間 [0,1] を R.subset として -/
  hott definition closed01 : R.subset := R.closed 0 1

  /-- [0,1] は空でない（0 ∈ [0,1]） -/
  hott definition closed01.inh : closed01.inh :=
  GroundZero.HITs.Merely.elem ⟨0, @reflexive.refl R.κ _ (0 : ℝ), zeroLeOne⟩

  /-- [0,1] は 1 で上に有界 -/
  hott definition closed01.maj : @majorized R.κ closed01 :=
  GroundZero.HITs.Merely.elem ⟨(1 : ℝ), λ x p, p.2⟩

  /-- [0,1] は 0 で下に有界 -/
  hott definition closed01.min : @minorized R.κ closed01 :=
  GroundZero.HITs.Merely.elem ⟨(0 : ℝ), λ x p, p.1⟩

  /-- sup [0,1] = 1 -/
  hott lemma closed01.supEqOne : sup closed01 closed01.inh closed01.maj = 1 :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply sup.exact closed01 closed01.inh closed01.maj (1 : ℝ);
      intros y p; exact p.2 };
    { apply sup.lawful closed01 closed01.inh closed01.maj (1 : ℝ);
      apply Prod.mk; exact zeroLeOne; apply @reflexive.refl R.κ }
  end

  /-- inf [0,1] = 0 -/
  hott lemma closed01.infEqZero : inf closed01 closed01.inh closed01.min = 0 :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply inf.lawful closed01 closed01.inh closed01.min (0 : ℝ);
      apply Prod.mk; apply @reflexive.refl R.κ; exact zeroLeOne };
    { apply inf.exact closed01 closed01.inh closed01.min (0 : ℝ);
      intros y p; exact p.1 }
  end

  /-- [0,1] では inf ≠ sup（0 ≠ 1）: 極限としての「収束先」は sup と inf が
      一般に一致しない。 -/
  hott lemma closed01.infNeSup :
    inf closed01 closed01.inh closed01.min ≠ sup closed01 closed01.inh closed01.maj :=
  begin
    intro p;
    apply @field.nontrivial R.τ _;
    exact Id.symm (Id.symm closed01.infEqZero ⬝ p ⬝ closed01.supEqOne) ⬝ Id.symm additiveUnit
  end

  /-- -0 = 0（R.zeroEqMinusZero を 0 に適用した逆） -/
  hott lemma negZero : -(0 : ℝ) = 0 :=
  Id.symm (R.zeroEqMinusZero (by reflexivity : (0 : ℝ) = 0))

  /-- sup (negφ [0,1]) = 0（符号反転の sup は -1 ではなく 0 になる） -/
  hott lemma negClosed01.supEqZero :
    sup (negφ closed01) (negφ.inh closed01 closed01.inh) (negφ.majorized closed01 closed01.min) = 0 :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply sup.exact (negφ closed01) (negφ.inh closed01 closed01.inh) (negφ.majorized closed01 closed01.min) (0 : ℝ);
      intros y p;
      apply Equiv.transport (λ w, R.ρ w 0);
      apply @Group.invInv R.τ⁺;
      apply R.zeroLeImplZeroGeMinus;
      exact p.1 };
    { apply sup.lawful (negφ closed01) (negφ.inh closed01 closed01.inh) (negφ.majorized closed01 closed01.min) (0 : ℝ);
      apply Equiv.transport (· ∈ closed01);
      symmetry; apply negZero;
      apply Prod.mk; apply @reflexive.refl R.κ; exact zeroLeOne }
  end

  /-- 反例: -(sup [0,1]) ≠ sup (negφ [0,1])。
      符号反転を sup の外へ出せない（正しくは inf になる）。
      有限2次形式の交換則 infSumFinSwap が求めるのは、まさにこの
      符号付き線形汎関数と sup の交換であり、sup ベースでは導出不能。 -/
  hott theorem negSupNotSwapClosed :
    -(sup closed01 closed01.inh closed01.maj) ≠
    sup (negφ closed01) (negφ.inh closed01 closed01.inh) (negφ.majorized closed01 closed01.min) :=
  begin
    intro p;
    apply @field.nontrivial R.τ _;
    exact Id.symm (@Group.invInv R.τ⁺ (1 : ℝ)) ⬝
          ap (λ z, -z) (Id.symm (ap (λ z, -z) closed01.supEqOne) ⬝ p ⬝ negClosed01.supEqZero) ⬝
          negZero ⬝ Id.symm additiveUnit
  end

  /-
    ============================================================================
    追記評価3: sup ベース級数理論の限界 — 単調性の正の側面と振動系列の反例
    ============================================================================

    前節の結論「infSumFinSwap は sup から導出不能」を補強するため、
    本節では sup ベースの級数理論について正負両面の結果を形式化する。

      (1) sumMonotone / supMonotone — sup が交換する操作の「正の側面」。
          非負項の部分和は単調増加し、sup は点別順序を保つ。
          「単調」な操作（加法・非負スカラー倍）とは sup は交換する。
      (2) 振動系列の反例 — 交代系列 alt = (1, -1, 0, 0, ...)。
          部分和は 0, 1, 0, 0, ... と振動し、n ≥ 2 以降は 0 に安定する。
          しかし sup { sum n alt | n } = 1 ≠ 0（alt.supEqOne / alt.supNeEventual）。
          つまり sup ベースの「和」は振動系列で極限を捉えない。
          ガウス級数 Σₙ cₙ(xy)ⁿ は xy < 0 のとき点別にまさにこの交代系列の
          状況であり、infiniteSum を sup で再定義する方針は gaussPsd に
          使えない（sup 版は間違った値 1 を返す）。
      (3) 負スカラー非交換の系列版 — seriesNegNotSwap。
          -(sup (series alt)) ≠ sup (negφ (series alt))（左辺 = -1、右辺 = 0）。
          [0,1] での反例（negSupNotSwapClosed）を実際の系列で再現する。
    ============================================================================
  -/

  /-- 交代系列: alt 0 = 1, alt 1 = -1, alt n = 0（n ≥ 2）。
       term 位置の match は本ライブラリの hott パーサーでは end を付けず
       括弧で閉じる（Euclidean.lean の strongRecAux と同様）。 -/
  hott definition alt : ℕ → ℝ :=
  @Nat.rec (λ _, ℝ) (1 : ℝ) (λ n _,
    match n with
    | 0 => -(1 : ℝ)
    | Nat.succ _ => (0 : ℝ))

  /-- alt の部分和は n ≥ 2 以降 0 に安定する: sum (n+2) alt = 0 -/
  hott lemma altEventuallyZero : Π m, sum (Nat.succ (Nat.succ m)) alt = 0 :=
  begin
    intro m;
    induction m with
    | zero =>
      exact calc sum (Nat.succ (Nat.succ 0)) alt = (0 + (1 : ℝ)) + (-(1 : ℝ)) : by reflexivity,
           = (1 : ℝ) + (-(1 : ℝ)) : ap (· + (-(1 : ℝ))) (R.τ.zeroAdd (1 : ℝ)),
           = 0 : R.τ.addComm (1 : ℝ) (-(1 : ℝ)) ⬝ R.τ.addLeftNeg (1 : ℝ)
    | succ m ih =>
      exact calc sum (Nat.succ (Nat.succ (Nat.succ m))) alt
             = sum (Nat.succ (Nat.succ m)) alt + alt (Nat.succ (Nat.succ m)) : by reflexivity,
           = 0 + (0 : ℝ) : ap (· + (0 : ℝ)) ih,
           = 0 : R.τ.addZero (0 : ℝ)
  end

  /-- alt の各部分和はちょうど 0 か 1 のどちらか（振動の範囲） -/
  hott lemma altSumRange : Π n, (sum n alt = 0) + (sum n alt = 1) :=
  begin
    intro n;
    induction n with
    | zero => apply Sum.inl; reflexivity
    | succ n ih =>
      induction n with
      | zero => apply Sum.inr; exact R.τ.zeroAdd (1 : ℝ)
      | succ m ih' => apply Sum.inl; exact altEventuallyZero m
  end

  /-- 各部分和は 1 以下（振動の上界） -/
  hott lemma altSumLeOne : Π n, R.ρ (sum n alt) 1 :=
  begin
    intro n;
    exact Sum.casesOn (altSumRange n)
      (λ p, Equiv.transport (λ w, R.ρ w 1) (Id.symm p) zeroLeOne)
      (λ p, Equiv.transport (λ w, R.ρ w 1) (Id.symm p) (@reflexive.refl R.κ _ (1 : ℝ)))
  end

  /-- 各部分和は 0 以上（振動の下界） -/
  hott lemma altSumGeZero : Π n, R.ρ 0 (sum n alt) :=
  begin
    intro n;
    exact Sum.casesOn (altSumRange n)
      (λ p, Equiv.transport (λ w, R.ρ 0 w) (Id.symm p) (@reflexive.refl R.κ _ (0 : ℝ)))
      (λ p, Equiv.transport (λ w, R.ρ 0 w) (Id.symm p) zeroLeOne)
  end

  /-- series alt の各要素は 1 以下（truncation を除去して altSumLeOne に帰着） -/
  hott lemma seriesAlt.leOne : Π x, x ∈ series alt → R.ρ x 1 :=
  begin
    intros x p;
    apply GroundZero.HITs.Merely.rec (R.κ.prop x (1 : ℝ)) _ p;
    intro q;
    apply Equiv.transport (λ w, R.ρ w 1);
    exact Id.symm q.2;
    exact altSumLeOne q.1
  end

  /-- series alt の各要素は 0 以上 -/
  hott lemma seriesAlt.leZero : Π x, x ∈ series alt → R.ρ 0 x :=
  begin
    intros x p;
    apply GroundZero.HITs.Merely.rec (R.κ.prop (0 : ℝ) x) _ p;
    intro q;
    apply Equiv.transport (λ w, R.ρ 0 w);
    exact Id.symm q.2;
    exact altSumGeZero q.1
  end

  /-- 0 ∈ series alt（部分和は n = 0 で 0 に達する） -/
  hott definition alt.zeroIn : 0 ∈ series alt :=
  GroundZero.HITs.Merely.elem ⟨0, by reflexivity⟩

  /-- 1 ∈ series alt（部分和は n = 1 で 1 に達する） -/
  hott definition alt.oneIn : 1 ∈ series alt :=
  GroundZero.HITs.Merely.elem ⟨1, Id.symm (R.τ.zeroAdd (1 : ℝ))⟩

  /-- series alt は 1 で上に有界 -/
  hott definition alt.maj : @majorized R.κ (series alt) :=
  GroundZero.HITs.Merely.elem ⟨(1 : ℝ), λ x p, seriesAlt.leOne x p⟩

  /-- series alt は 0 で下に有界 -/
  hott definition alt.min : @minorized R.κ (series alt) :=
  GroundZero.HITs.Merely.elem ⟨(0 : ℝ), λ x p, seriesAlt.leZero x p⟩

  /-- sup { sum n alt | n } = 1: sup は振動の「上端」1 を返す -/
  hott lemma alt.supEqOne :
    sup (series alt) (series.inh alt) alt.maj = 1 :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply sup.exact (series alt) (series.inh alt) alt.maj (1 : ℝ);
      intros y p;
      exact seriesAlt.leOne y p };
    { apply sup.lawful (series alt) (series.inh alt) alt.maj (1 : ℝ);
      exact alt.oneIn }
  end

  /-- 振動系列の反例: sup は n ≥ 2 以降の安定値 0 を返さない。
       sum 2 alt = 0 だが sup { sum n alt | n } = 1 ≠ 0。
       sup ベースの「和」は極限（ここでは 0）と一致しない。 -/
  hott theorem alt.supNeEventual :
    sup (series alt) (series.inh alt) alt.maj ≠ sum 2 alt :=
  begin
    intro p;
    apply @field.nontrivial R.τ _;
    exact Id.symm (Id.symm (altEventuallyZero 0) ⬝ Id.symm p ⬝ alt.supEqOne) ⬝
          Id.symm additiveUnit
  end

  /-- -x = 0 なら x = 0（neg の対合） -/
  hott lemma negAlt.invZero (x : ℝ) (p : -x = 0) : x = 0 :=
  calc x = -(-x) : Id.symm (@Group.invInv R.τ⁺ x),
       = -(0 : ℝ) : ap (λ z, -z) p,
       = 0 : negZero

  /-- -x = 1 なら x = -1（neg の対合） -/
  hott lemma negAlt.invOne (x : ℝ) (p : -x = 1) : x = -(1 : ℝ) :=
  calc x = -(-x) : Id.symm (@Group.invInv R.τ⁺ x),
       = -(1 : ℝ) : ap (λ z, -z) p

  /-- x ∈ negφ (series alt)（= -x ∈ series alt）なら x ≤ 0:
       negφ (series alt) の要素はちょうど {0, -1} だから。 -/
  hott lemma negSeriesAlt.leZero : Π x, x ∈ negφ (series alt) → R.ρ x 0 :=
  begin
    intros x p;
    apply GroundZero.HITs.Merely.rec (R.κ.prop x (0 : ℝ)) _ p;
    intro q;
    exact Sum.casesOn (altSumRange q.1)
      (λ s, Equiv.transport (λ w, R.ρ w 0) (Id.symm (negAlt.invZero x (q.2 ⬝ s)))
              (@reflexive.refl R.κ _ (0 : ℝ)))
      (λ s, Equiv.transport (λ w, R.ρ w 0) (Id.symm (negAlt.invOne x (q.2 ⬝ s)))
              (R.zeroLeImplZeroGeMinus zeroLeOne))
  end

  /-- 0 ∈ negφ (series alt)（-0 = 0 が series alt に属するから） -/
  hott definition alt.negZeroInNeg : 0 ∈ negφ (series alt) :=
  Equiv.transport (λ w, w ∈ series alt) (Id.symm negZero) alt.zeroIn

  /-- sup (negφ (series alt)) = 0: 符号反転系列の sup は -1 ではなく 0 -/
  hott lemma negAlt.supEqZero :
    sup (negφ (series alt)) (negφ.inh (series alt) (series.inh alt))
        (negφ.majorized (series alt) alt.min) = 0 :=
  begin
    apply @antisymmetric.asymm R.κ;
    { apply sup.exact (negφ (series alt)) (negφ.inh (series alt) (series.inh alt))
        (negφ.majorized (series alt) alt.min) (0 : ℝ);
      intros x p;
      exact negSeriesAlt.leZero x p };
    { apply sup.lawful (negφ (series alt)) (negφ.inh (series alt) (series.inh alt))
        (negφ.majorized (series alt) alt.min) (0 : ℝ);
      exact alt.negZeroInNeg }
  end

  /-- 反例（系列版）: -(sup (series alt)) ≠ sup (negφ (series alt))。
       符号付き線形汎関数（負スカラー倍）は sup と交換しない。
       左辺 = -1、右辺 = 0。 -/
  hott theorem seriesNegNotSwap :
    -(sup (series alt) (series.inh alt) alt.maj) ≠
    sup (negφ (series alt)) (negφ.inh (series alt) (series.inh alt))
        (negφ.majorized (series alt) alt.min) :=
  begin
    intro p;
    apply @field.nontrivial R.τ _;
    exact Id.symm (@Group.invInv R.τ⁺ (1 : ℝ)) ⬝
          ap (λ z, -z) (Id.symm (ap (λ z, -z) alt.supEqOne) ⬝ p ⬝ negAlt.supEqZero) ⬝
          negZero ⬝ Id.symm additiveUnit
  end

  /-- 非負項の部分和は単調増加（単調収束の基盤）:
       (Π n, 0 ≤ g n) → sum n g ≤ sum (Nat.succ n) g -/
  hott lemma sumMonotone (g : ℕ → ℝ) (p : Π n, R.ρ 0 (g n)) :
    Π n, R.ρ (sum n g) (sum (Nat.succ n) g) :=
  begin
    intro n;
    apply Equiv.transport (R.ρ · (sum n g + g n));
    exact R.τ.addZero (sum n g);
    apply ineqAdd R; apply @reflexive.refl R.κ; exact p n
  end

  /-- sup は点別順序を保つ（sup が交換する「単調」操作の代表例）:
       φ ⊆ ψ なら sup φ ≤ sup ψ -/
  hott lemma supMonotone (φ ψ : R.subset) (H : φ.inh) (G : @majorized R.κ φ)
    (H' : ψ.inh) (G' : @majorized R.κ ψ) (sub : Π x, x ∈ φ → x ∈ ψ) :
    R.ρ (sup φ H G) (sup ψ H' G') :=
  begin
    apply sup.exact φ H G (sup ψ H' G');
    intros y p;
    apply sup.lawful ψ H' G' y;
    exact sub y p
  end

  /-
    ============================================================================
    評価: 2公理の導出可能性 — 結論
    ============================================================================

    (1) infSumNonneg: 公理としては導出不能、その「sup 版」は導出可能。
        · 定理 infSumNonnegSup は sup { sum n g | n } ≥ 0 を示す。これは
          「0 = sum 0 g が部分和集合に含まれる」ことだけで閉じる順序論的
          自明な事実であり、g の非負性（p）すら必要としない。
        · 一方、gaussPsd が使う公理 infSumNonneg : 0 ≤ infiniteSum g は
          infiniteSum（未解釈の公理記号）についての主張であり、sup との
          同一視は証明なしに仮定できない。よって公理の除去には至らない。
        · 仮に「infiniteSum g := sup (series g)（+ 有界性の仮定）」と定義し
          直せば infSumNonneg は定理（しかも自明な定理）になるが、それは
          公理の導出ではなく公理の置き換えである。

    (2) infSumFinSwap: 導出不能。
        交換則は「有限2次形式（cᵢcⱼ により符号を持つ線形汎関数）と sup の
        交換」を要求する。しかし sup は単調な操作としか交換しない:
          · 正しい双対性は -(sup φ) = inf (Neg φ)（supNegDuality）であり、
            「-(sup φ) = sup (Neg φ)」は偽（negSupNotSwapClosed の反例:
            [0,1] で -(sup) = -1 だが sup (Neg [0,1]) = 0）。
          · 同様に sup は一般に和・スカラー倍（特に負係数）とも交換しない。         交換則の証明には sup ではなく「極限の線型性」が必要であり、それは
         コーシー列・絶対収束・収束級数の理論（ライブラリ未整備）の内容である。

     (3) 追記（追記評価3）: sup が交換する操作の「正の側面」—
         sumMonotone / supMonotone。
         非負項の部分和は単調増加し（sumMonotone）、sup は点別順序を保つ
         （supMonotone）。つまり「単調」な操作（加法・非負スカラー倍）と
         は sup は交換する。sup ベースの級数理論は単調系列に対しては
         健全であり、infSumNonneg の sup 版が自明に導出できることと整合する。

     (4) 追記（追記評価3）: 振動系列の反例（alt）— sup ベースの「和」は
         極限を捉えない。
         交代系列 alt = (1, -1, 0, 0, ...) の部分和は 0, 1, 0, 0, ... と
         振動し、n ≥ 2 以降は 0 に安定する（altEventuallyZero）。しかし
         sup { sum n alt | n } = 1（alt.supEqOne）であり、安定値 0 とは
         一致しない（alt.supNeEventual）。さらに負スカラー非交換の系列版
         seriesNegNotSwap: -(sup (series alt)) ≠ sup (negφ (series alt))
         （左辺 = -1、右辺 = 0）が成り立つ。
         これは「infiniteSum g := sup (series g)」という再定義が gaussPsd に
         使えないことを示す: ガウス級数 Σₙ cₙ(xy)ⁿ は xy < 0 のとき点別に
         この交代系列と同じ「符号振動」の状況（cₙ ≥ 0 と (xy)ⁿ の符号交代）
         になり、sup 版の和は部分和の振動の上端を返して極限と一致しない
         （alt の場合の「sup = 1 ≠ 安定値 0」はその典型例。ガウス級数自身が
         返すのは exp(2ε²xy) でない別の値）。つまり infSumNonneg の
         「sup への置き換え」でさえ、級数が振動するガウスカーネルには
         適用できない。

     従って「gaussPsd を公理なしで完成させる」には:
      · infSumNonneg は sup ベースの定義（+ 有界性の仮定）で定理にできるが、
        それは公理の「置き換え」であり、infiniteSum を sup で定義し直す
        必要がある（証明ではない）。
      · infSumFinSwap は極限理論（級数の線型性）をライブラリに追加する
        必要があり、sup（完備性）だけでは不足。2公理のうち交換則の方が
        本質的に解析的な内容を持っている。     結論: 2公理を sup から導出して gaussPsd を「公理なし」にすることは
     できない。導出可能なのは交換則を含まない自明な部分（sup 版の
     infSumNonneg）のみであり、さらに振動系列の反例（alt.supNeEventual /
     seriesNegNotSwap）が示すように、sup への「置き換え」は振動する
     ガウス級数には使えない。交換則の導出には実解析の級数理論
     （線型性・絶対収束）の整備が必要である。
     （追記評価4: この「線型性」を公理 infSumLin として追加すれば、
     交換則 infSumFinSwap は定理として導出できる。）
    ============================================================================
  -/

  /-
    ============================================================================
    追記評価4: 交換則 infSumFinSwap は「極限の線型性」infSumLin から導出できる
    ============================================================================

    追記評価2/3 は「sup（Dedekind 完備性）からは infSumFinSwap を導出できない」
    ことを示した。本節はその結論を補完する: 「極限の線型性」を公理として
    追加すれば、交換則は定理になる。つまり gaussPsd が要請する解析的内容の
    うち、交換則の部分は「無限和は線形汎関数」という最小の標準公理
    （infSumLin）に集約できる。

    構成（実装は交換則の定義位置に前倒し）:
      · infSumLin（公理）: infiniteSum (λ m, a·f m + b·g m) = a·Σf + b·Σg
      · infSumAdd（加法性）· infSumScale（斉次性）· infSumZero（零列）
        ← infSumLin から導出
      · sumSwapInf（有限和と無限和の交換、n に関する帰納法）
        ← infSumAdd / infSumZero から導出
      · infSumScale2（スカラー移動）← infSumScale + 環の結合・交換則
      · infSumFinSwap（旧公理の文面そのもの）← sumSwapInf + infSumScale2 から導出
      · gaussPsd は変更なしで通る（infSumFinSwap が定理になっただけ）。

    公理数の評価:
      · gaussPsd の系列公理は {expSeries, infSumNonneg, infSumFinSwap} から
        {expSeries, infSumNonneg, infSumLin} へ。数は 3 のまま変わらないが、
        交換則は公理から定理に降格し、公理の強さは実解析の標準最小形に統一
        される。公理の「数」を 2 に減らすには expSeries か infSumNonneg の
        除去が必要だが、前者は exp の再定義（Cauchy 積）、後者は順序構造の
        導出に相当し、いずれも線型性からは出ない。
      · ライブラリ全体の公理数は ±0（infSumFinSwap を消し、infSumLin を追加）。

    収束仮定（conv 述語）が付けられない理由:
      · ライブラリに収束述語が存在しない（infiniteSum は全作用素）。
      · 仮に sup ベースの収束条件（例: 部分和集合が上に有界）を conv とすれば、
        ガウス級数 Σₙ cₙ(xy)ⁿ は xy < 0 で交代系列となり（追記評価3 の alt
        反例: sup = 1 ≠ 安定値 0）、conv を満たさない。収束仮定を付けると
        gaussPsd に適用不能になる。
      · よって収束の内容は全作用素 infiniteSum への線型性公理に内包するのが
        この公理化では唯一の実用形である（追記評価2/3 の結論と整合）。
    ============================================================================
  -/

  /-
    ============================================================================
    追記評価5: exp を級数で再定義し、Cauchy 積から expAdd を導出できるか
    ============================================================================

    追記評価4 で gaussPsd の系列公理は {expSeries, infSumNonneg, infSumLin} に
    整理された。本節は残る expSeries を公理から外せるかを評価する。
    （プローブ /tmp/probe_cauchy.lean で実証済み。）

    方針: exp を「未解釈の公理」ではなく「級数の定義」に置き換える。
      expD t := infiniteSum (λ n, tⁿ/n!)
    これで expSeries は定義的等価（rfl）になり、公理から除外できる
    （#print axioms expDSeries = {R, infiniteSum, ...} のみ）。
    代わりに生じる義務は exp の代数的性質（expZero / expAdd）を級数から
    証明することであり、その核心は無限コーシー積（畳み込み）である。

    結果（プローブで実証）:
      · expAdd は「二項定理（階乗正規化版）binomTaylor + 無限コーシー積
        cauchyProduct」から定理として導出できる。
        #print axioms expAddD = {binomTaylor, cauchyProduct, infiniteSum, ...}
        → exp / expAdd / expSeries は公理依存から消滅する。
      · ただし cauchyProduct（任意の列 A B について
        L(A)·L(B) = L(Σₖ Aₖ·Bₙ₋ₖ)）は infSumLin / infSumNonneg から導出不能。
        線型性は「有限線型結合」とのみ交換するが、コーシー積は「無限の無限
        再配列」であり、極限の連続性に相当する別の解析的内容を要する
        （追記評価2/3 の「sup は単調操作としか交換しない」と平行する構造）。
      · binomTaylor は完全証明済み（BinomTaylor.lean、公理ゼロ）。
        nCr（Pascal 再帰）と Nat の切り捨て減算の補題群を整備し、nCrFac
        （nCr n k · k!·(n-k)! = n!）と nCrDiv（逆元分解）を経て
        binomTaylorPw で点別に階乗正規化し、sumLe で総和に持ち上げた。
      · expZero は残る。expD 0 = 1 は δ₀ = (1,0,0,..) の和が 1 であることを要し、
        線型性 + 非負性からは決まらない（cauchyProduct からも L(δ₀)² = L(δ₀)
        つまり L(δ₀) ∈ {0,1} まで。正の線形汎関数には L(δ₀) = 0 のものも存在）。
        （追記評価9 で解決済み: BinomTaylor.lean の expZeroD は infSumIsLim
        （極限同定）を使えば導出できることを実証した。L(δ₀) は線型性では
        決まらないが、極限として一意に定まる。実測: expZeroD = {infSumIsLim,
        ...} のみで exp ブロック非依存。）

    プローブの核心（自己完結のため再掲。実装はしていない）:
      expD t := infiniteSum (λ n, rdiv (rpow t n) (fac n))          -- 定義
      expDSeries t : expD t = infiniteSum (λ n, rdiv (rpow t n) (fac n))  -- rfl
      cauchyProduct (A B : ℕ → ℝ) :                                   -- 公理
        infiniteSum A * infiniteSum B =
        infiniteSum (λ n, sum (Nat.succ n) (λ k, A k * B (n - k)))
      binomTaylor (a b : ℝ) : Π n,
        rdiv (rpow (a + b) n) (fac n) =
        sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k)))
      expAddD (a b : ℝ) : expD (a + b) = expD a * expD b             -- 定理
        := expDSeries ⬝ infiniteSum.ext (binomTaylor a b) ⬝
           Id.symm (cauchyProduct (λ k, aᵏ/k!) (λ l, bˡ/l!))
      expZeroD : expD 0 = 1                                          -- 定理（追記評価9 で導出）
      #print axioms expAddD = {binomTaylor, cauchyProduct, infiniteSum, ...}

    公理数の評価:
      · exp ブロックは {exp, expZero, expAdd, expSeries}（4公理）から
        {expZero, cauchyProduct}（2公理、binomTaylor を証明すれば）に減る。
        gaussPsd の依存公理は exp 関連 3つが cauchyProduct 1つに置き換わり
        2 つ減る（これも binomTaylor を証明した場合。プローブのまま公理化
        すると -1 である）。
      · ただし cauchyProduct は expAdd + expSeries より「強い」（任意の列に
        適用される）。これは公理の弱化ではなく一般化であり、単独では
        「良い置き換え」ではない。
      · 真の価値は将来への布石: 絶対収束の理論（コーシー列・極限）を整備
        すれば cauchyProduct 自体が定理になり、その時点で exp 周りの公理は
        expZero だけになり、gaussPsd の公理は {infSumNonneg, infSumLin} の
        2 つまで下がる。
      · （追記評価7 で実行済み: BinomTaylor.lean が conv 仮説
        convExpD/convAbsExpD を整備し、cauchyProduct 公理を削除して
        expAddD を cauchyProductLim（定理）に張り替えた。実測は
        {convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin,
        infSumNonneg} で、{infSumNonneg, infSumLin} への完全縮減は
        convExpD 等の定理化（比較判定・比率判定）が前提。）
    ============================================================================
  -/

  /-
    ============================================================================
    ガウスカーネルの正定値性: 最終評価
    ============================================================================

  成果: 実数直線 ℝ 上のガウスカーネル
        K(x, y) = exp (-ε²·(x-y)²)
  の正定値性 PSD (λ x y, gaussKernel ε x y) が gaussPsd として完成した。
  証明は以下の部品で構成される。

    1. 級数分解の公理化（Reals.lean に統合）
       exp t = Σₙ tⁿ/n! を hott axiom expSeries として追加。あわせて
       rpow (tⁿ)・fac (n!)・rdiv (a/b)・infiniteSum とその外延性
       （infiniteSum.ext）をライブラリに追加した。
    2. 多項式カーネルの PSD（全て証明済み）
       (x·y)ⁿ = xⁿ·yⁿ（rpowMul）によりランク1カーネルに帰着 →
       psdRankOne。係数 cₙ = (2ε²)ⁿ/n! の非負性（coeffNonneg）は
       順序体から導出。よって有限テイラー切断 Σₙ₌₀ᴺ cₙ(x·y)ⁿ は PSD
       （taylorPsd）、ランク1因子 exp(-ε²x²)·(-)·exp(-ε²y²) を掛けても
       PSD（gaussTruncPsd）。
    3. ガウスの分解（全て証明済み）
       exp(-ε²(x-y)²) = exp(-ε²x²)·exp(2ε²xy)·exp(-ε²y²) を
       distSquare / mulDistSquare / negTriple / expTriple から導出
       （gaussDecomp）。exp(2ε²xy) = Σₙ cₙ(x·y)ⁿ は expSeries +
       rpowMul + 無限和の外延性から導出（expMid / gaussKernelSeries）。
    4. 無限和の収束論（2つの系列公理 — 残された本質的ブロッカー）
       · infSumNonneg : 非負項の無限和は非負（単調収束に相当）
       · infSumLin     : 極限の線型性（無限和は線形汎関数）
       これらは expSeries からは導出できない実解析（収束・級数）の内容で
       あり、公理として追加した。交換則 infSumFinSwap は公理ではなく
       infSumLin から導出される定理（追記評価4: infSumAdd + infSumScale +
       sumSwapInf で閉じる）。gaussPsd は {expSeries, infSumNonneg,
       infSumLin} の3公理で閉じている。公理の「数」を 2 に減らすには
       expSeries か infSumNonneg の除去が必要で、それは exp の再定義
       （Cauchy 積）か順序構造の導出を要し、線型性からは出ない。

  なお、ここで証明したのは ℝ 上の (x-y)² に対するカーネルである。
  一般の距離空間 (M, ρ) に対する exp(-ε²·ρ(x,y)²) の PSD は、
  ユークリッド構造（内積・条件付き負定値性）が未整備のため未解決のまま
  残る（ライブラリには Metric しかなく、一般の距離空間ではガウスカーネル
  は正定値とは限らない）。

  補足: exp の非負性（expNonneg）は expAdd + 順序体の2等分 + 平方非負性
  だけで公理なしに導出できる（exp(z/2)² ≥ 0 へ帰着）。これは級数分解とは
  独立の事実であり、級数の公理化には使っていない。
  ============================================================================
-/

/- ==========================================================================
  追記評価6: コーシー列・極限の最小理論 — cauchyProduct の定理化と線型性の吸収
  ============================================================================
  ユーザー依頼: 「コーシー列・極限の最小限の理論を整備し、cauchyProduct を
  定理として導出できるか評価する」。

  評価プローブ（/tmp/probe_lim.lean）: 本節の極限理論は 2026-08-10 に PosDef
  へ統合済み（conv / infSumIsLim / mertens / infSumLinD / cauchyProductLim。
  infSumLin 公理の直前の「追記評価6（統合済み）」セクションを参照）。

  (1) abs 理論の完成: absMul（|xy| = |x||y|、R.total の符号 4 分岐）等を
      既存の abs API（abs.pos / abs.neg / abs.triangle）から証明。公理ゼロ。

  (2) conv の定義: ε-N 収束
        conv f L := Π ε (p : 0 < ε), Σ N, Π n ≥ N, abs (f n - L) ≤ ε
      convConst / convExt（点別等価）を証明。公理ゼロ。

  (3) convAdd（ε/2 分割）: conv A LA → conv B LB → conv (A + B) (LA + LB)。
      PosDef の twoInv/halve + Orgraph の ineqAdd/strictIneqAdd で証明。
      公理ゼロ。

  (4) 最小公理の導入:
        infSumIsLim : infiniteSum f = L → conv f L      （無限和は極限）
        mertens     : conv (部分和 A) SA → conv (部分和 B) SB
                        → conv (部分和 |A|) Aabs
                        → conv (部分和 (三角畳み込み A B)) (SA * SB)
      （Mertens: コーシー積の極限 = 極限の積。古典 Mertens に忠実で、
        片側絶対収束（|A| の収束）を仮定に含む — 無条件形ではない）

  (5) cauchyProductLim 定理: infSumIsLim + mertens から旧公理 cauchyProduct
      を導出。
        #print axioms cauchyProductLim = {infSumIsLim, mertens, ...}
      → 追記評価5 で残っていた公理 cauchyProduct が消滅。

  (6) ボーナス — 線型性の吸収: convScale / convLin（極限の線型性）を経て
      infSumLinD（旧公理 infSumLin の内容）を infSumIsLim のみから導出。
        #print axioms infSumLinD = {infSumIsLim}
      → gaussPsd の系列公理 {expSeries, infSumNonneg, infSumLin} のうち
        infSumLin が定理に格下げ。

  結論:
  · exp 再定義（追記評価5）+ 本評価で、gaussPsd の実解析公理は現行の
    {exp, expZero, expAdd, expSeries, infSumNonneg, infSumLin} から
    {expZero, infSumNonneg, infSumIsLim, mertens} の 4つに収束する見込み
    （追記評価5 の exp 再定義を採用した場合。現行統合状態では未適用）。
    内訳: exp/expAdd/expSeries は級数再定義で吸収（定義/rfl）、
    infSumLin と cauchyProduct は定理化、infSumIsLim/mertens は新規公理。
  · infSumLin と cauchyProduct は「公理の削減」ではなく「標準公理への
    吸収」であり、それぞれ {infSumIsLim} / {infSumIsLim, mertens} に
    還元される（#print axioms で実証済み）。
  · 残る最小公理 mertens は「積の極限 = 極限の積」の Mertens 定理であり、
    これ自体を定理化するには絶対収束（重み付き評価・交代級数）の完全な
    理論が必要。ライブラリにその道具（δ 関数・重み付き和の評価）がない
    ため将来課題とする。
  · 統合状況（2026-08-10）: 極限理論（conv・infSumIsLim・mertens・
    infSumLinD・cauchyProductLim）は統合済み。ただし infSumIsLim の方向制約
    （「収束 → 極限同定」のみ）により無条件形の infSumLin 公理は残り、
    gaussPsd の依存公理は現状 {exp, expAdd, expSeries, infSumNonneg,
    infSumLin} のまま。{expZero, infSumNonneg, infSumIsLim, mertens} への
    削減は exp の級数再定義（追記評価5）+ ガウス級数の収束仮定の検証
    （絶対収束理論）を待つ。追記評価5 の binomTaylor は BinomTaylor.lean
    で完全証明済み（公理ゼロ）。expD と expAddD も BinomTaylor.lean で完了:
    expAddD は binomTaylor + cauchyProductLim（定理）+ conv 仮説から導出され、
    公理依存は {convExpD, convAbsExpD, infSumIsLim, mertens, infiniteSum,
    infiniteSum.ext} のみ（exp ブロックの公理 {exp, expZero, expAdd,
    expSeries} も cauchyProduct 公理も不要。追記評価7 で張り替え済み）。
    残るは expZeroD（expD 0 = 1、公理のまま）の確認である。
  ============================================================================
-/
/-============================================================================
  追記評価16: KernelLearn.gram の gaussKernelD 切替 — gaussPsdDE 不要化の評価
  （RBF ブリッジの exp 依存が残る範囲の確定）
  ----------------------------------------------------------------------------
  probe: /tmp/eval16_probe.lean（namespace Eval16、EXIT 0）
  ※ 以下の宣言（gaussSymmD/gramDNonneg/gramDSym/
    gaussKernelEqD/rbfGaussEqD/gramRbfNonnegD）は probe 用の定義であり、
    ライブラリの宣言ではない（import 不可）。
  ----------------------------------------------------------------------------
  実施内容
  (1) D ワールド部品の可用性（全て gaussPsdD 側の部品だけで構成可能）
      gaussSymmD   : IsSymmetric (gaussKernelD ε) — sqrSym のみで閉じる（exp 不要）
      gramDNonneg  : biForm (gaussKernelD ε) の PSD — gaussPsdD を直接適用
      gramDSym     : biFormSymI + gaussSymmD で自動導出
      → gaussKernelD の対称性・PSD は D ワールド内で完結（exp 系ゼロ）。
  (2) RBF ブリッジの D 版（ここにのみ exp 依存が残る）
      gaussKernelEqD : gaussKernel ε x y = gaussKernelD ε x y
        （expEqExpD のカーネル版。expSeries 公理が唯一の接続点）
      rbfGaussEqD    : RBF.gaussianRbf ε Rₘ c x = gaussKernelD ε c x
        （rbfGaussEq ⬝ gaussKernelEqD ⬝ gaussSymmD で合成）
      gramRbfNonnegD : gramRbfD（RBF 名義の核行列）の PSD —
        rbfGaussEqD で点別 transport 後 gramDNonneg に帰着（EXIT 0）
  ----------------------------------------------------------------------------
  結論
  (A) gram を gaussKernelD に切替え、PSD を gaussPsdD（5 公理:
      {convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg}）で証明すれば、
      **gram レベルの正定値性は exp 系ゼロ**になる。
      この経路では gaussPsdDE（8 公理、exp/expSeries/infiniteSum を含む）は
      KernelLearn から不要になる（回収可能な重複）。
  (B) 一方 **RBF ブリッジには exp 依存が構造的に残る**: RBF.gaussianRbf は exp
      で定義されており、gaussianRbf = gaussKernelD の同値には expEqExpD
      （= exp の級数分解、expSeries 公理）が不可欠。
      → gramRbfNonneg / rbfPsd（RBF 名義の PSD）は依然 exp 依存のまま
      （追記評価17 で実測: 5 + exp + expSeries = 7 公理。expAdd は不要）。
  (C) 残存 exp 依存の範囲 = 「RBF.gaussianRbf を gaussKernelD と比較する箇所
      のみ」。RBF 自体を D ワールドで再定義（RBFD := gaussKernelD）すれば
      チェーン全体が exp フリーになるが、RBF.lean の exp 版定義と二重化する。
      → 追記評価18 で実装済み（RBF.gaussianRbfD を追加し、RBF 名義 PSD を
        exp フリーに。二重化のコストは許容）。
  ----------------------------------------------------------------------------
  実装（追記評価17）: (A) を実装済み — gram / gramNonneg / gramSym / gramRow /
  gramRowLin を gaussKernelD に切替、gaussSymmD をライブラリ instance として
  登録、gaussPsdDE を削除。KernelLearn.gramNonneg は 5 公理（exp 系ゼロ）を
  #print axioms で実測。RBF 名義の rbfPsd / gramRbfNonneg は (B) の通り
  8 公理（実測 7）のままだったが、追記評価18 で (C) を実装し 5 公理（exp 系
  ゼロ）に。representer 系（表現子）は exp ワールドのまま（(C) の範囲）。
  ============================================================================
-/

/-
  ============================================================================
  追記評価17: 追記評価16 (A) の実装 — gaussPsdDE の削除と gram 系の D ワールド化
  ============================================================================

  実装内容（KernelLearn.lean 側）:
    (1) gaussSymmD : IsSymmetric (gaussKernelD ε) をライブラリ instance として
        登録（sqrSym のみで閉じる、exp 公理に非依存）。
    (2) gram / gramNonneg / gramSym を gaussKernelD に切替。
        gramNonneg := gaussPsdD。#print axioms 実測: {convExpD, convAbsExpD,
        infSumIsLim, mertens, infSumNonneg} の 5 公理（exp / expAdd / expSeries
        は消滅）。
    (3) gramRbfNonneg は rbfGaussEqD（RBF.gaussianRbf ε Rₘ c x = gaussKernelD
        ε c x = rbfGaussEq ⬝ gaussKernelEqD ⬝ gaussSymmD）で gram に帰着させて
        いた（RBF 名義のため expSeries 依存 — 追記評価16 (B)。実測:
        5 + exp + expSeries = 7 公理）。
        ※ 追記評価18 で gaussianRbfD（exp フリー）に切替、5 公理に縮減。
          rbfGaussEqD / gaussKernelEqD は不要化し削除。
    (4) gramRow / gramRowLin（リッジ双対の行列ベクトル積）も D ワールド化。
    (5) 本ファイルの gaussPsdDE は削除。expEqExpD は gaussKernelEqD（RBF
        ブリッジ）が使用するため残置していた。
        ※ 追記評価18: gaussKernelEqD / rbfGaussEqD は削除（RBF 名義 PSD が
          gaussianRbfD に切替）。expEqExpD は接続補題として保持。

  役割分担（追記評価17 時点）:
      · exp 版カーネルの性質（kernelCenter / kernelPos / kernelLeOne 等）:
        従来通り gaussKernel（exp ワールド）
      · gram 系（核行列・PSD・対称性）: gaussKernelD（D ワールド、exp 系ゼロ）
      · RBF 名義の命題（rbfPsd / gramRbfNonneg）: rbfGaussEqD ブリッジ経由で
        expSeries 依存（8 公理）→ 追記評価18 で gaussianRbfD に切替（5 公理）
  ============================================================================
-/

/-
  ============================================================================
  追記評価18: 追記評価16 (C) の実装 — RBFD（gaussianRbfD）と RBF 名義 PSD の exp 除去
  ============================================================================

  (C)「RBF 自体を D ワールドで再定義すればチェーン全体が exp フリーになる」
  を実装した。RBF.lean に D ワールド版ガウス RBF を追加:

      RBF.gaussKernelD ε : ℝ → ℝ      k(r) = expD(-ε²·r²)
      RBF.gaussianRbfD ε M c          φ(x) = expD(-ε²·ρ(x,c)²)

  KernelLearn 側（追記評価18 ブロック参照）:
      · gaussianRbfD_eq_gaussKernelD : RBF.gaussianRbfD ε Rₘ c x = gaussKernelD
        ε c x（absSqr + sqrSym による。exp 公理・conv 公理に非依存）
      · gramRbf / gramRbfNonneg / rbfPsd / gramRbfSym を RBF.gaussianRbfD に切替
      · rbfGaussSymmD（IsSymmetric）を追加、exp 版 rbfGaussSymm を削除
      · gaussKernelEqD / rbfGaussEqD（exp ブリッジ、追記評価17 で追加）は
        不要化し削除。expEqExpD は接続補題として保持（削除すると追記評価14/15/16
        の記録と AIPROVER チャートの参照が無効化されるため）

  検証（#print axioms 実測）:
      gramRbfNonneg / rbfPsd : {convExpD, convAbsExpD, infSumIsLim, mertens,
                                infSumNonneg} の 5 公理 — exp / expAdd /
                                expSeries 完全消滅
      gaussianRbfD_eq_gaussKernelD / rbfGaussSymmD / gramRbfSym : exp フリー
      （ブリッジ自体も conv / mertens に非依存）

  → 追記評価16 (B) の「RBF ブリッジには exp 依存が構造的に残る」は解消。
    残る exp 依存は「exp 版 gaussianRbf 自体の理論（RBF.lean）と表現子系」
    のみ。コストは exp 版と D 版 RBF の二重化（追記評価16 (C) の通り）。
  ============================================================================
-/

/-
  ============================================================================
  追記評価19: 表現子系・kernelCenter の D ワールド化（exp 残存範囲を RBF.lean のみに）
  ============================================================================

  実施内容（KernelLearn 側の変更。PosDef は変更なし）:
    · KernelLearn の表現子系（representer / featureMap / representerAsFeatures /
      gaussEqShift / representerShiftInvariant）と kernelCenter を gaussKernelD
      に切替（probe /tmp/eval19_probe.lean で検証、namespace Eval19、EXIT 0）。
      kernelCenter は BinomTaylor.expZeroD（expD 0 = 1、公理なしで導出済み）を
      使用するため infSumIsLim に依存するが、exp 公理はゼロ。
    · 切替により孤児化した exp ワールド宣言（rbfGaussEq / gaussSymm / kernelSym /
      expPos / kernelPos / expMonotone / kernelLeOne、およびブリッジ補題 absSqr /
      negSub / sqrSym）は RBF.lean へ移設（exp 理論の住処への集約）。

  検証（#print axioms 実測、probe /tmp/eval19_probe.lean）:
      kernelCenterD / gaussianRbfDShiftInvariant / gaussEqShiftD /
      representerEvalD / representerAsFeaturesD / representerShiftInvariantD:
        exp 系ゼロ（kernelCenterD のみ expZeroD 経由で infSumIsLim に依存）
      gramNonneg / gramRbfNonneg / rbfPsd / gramSym / gramRbfSym : 不変（5 / 0）

  → KernelLearn の exp 依存は完全消滅。残存 exp 範囲は「RBF.lean の exp 理論
    （gaussianRbf と exp 版基本性質）」のみ。コスト: exp/D 二重化（変わらず）。
  ============================================================================
-/
end PosDef

