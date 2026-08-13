import PosDef

/-
  ============================================================================
  二項定理の階乗正規化（binomTaylor）— 追記評価5 の核心
  ============================================================================

  目標: exp の級数再定義（expD t := infiniteSum (λ n, rpow t n / fac n)）の
        要となる二項定理の階乗正規化形を、公理ゼロで完全証明する。

        binomTaylor (a b : ℝ) (n : ℕ):
          rdiv (rpow (a + b) n) (fac n) =
          sum (Nat.succ n) (λ k, rdiv (rpow a k) (fac k) * rdiv (rpow b (n - k)) (fac (n - k)))

  証明の構成（すべて公理ゼロ。依存公理は {R, R.dedekind, Quot.sound} のみ）:
    1. 二項係数 nCr（Pascal 再帰）と Nat の切り捨て減算の補題群
    2. 二項定理 binom: (a+b)ⁿ = Σₖ nCr n k · aᵏ · bⁿ⁻ᵏ
    3. コンビナトリアル恒等式 nCrFac: nCr n k · k! · (n-k)! = n!（帰納法）
    4. 逆元分解 nCrDiv: nCr n k · (n!)⁻¹ = (k!)⁻¹ · ((n-k)!)⁻¹
       （nCrDivL / nCrDivR は x·y = 1 型の逆元一意性補題 invEqOfMulEqOne で結合）
    5. 点別正規化 binomTaylorPw + 総和への持ち上げ binomTaylor
    6. exp の級数再定義 expD と加法性 expAddD（binomTaylor +
       cauchyProductLim + conv 仮説から導出、exp ブロック公理は不要）
    7. gaussPsd の expD 張り替え gaussPsdD（exp ブロック公理 {exp, expAdd,
       expSeries} と cauchyProduct 公理を消滅させ、依存公理を {convExpD,
       convAbsExpD, infSumIsLim, mertens, infSumLin, infSumNonneg} に更新
       — #print axioms 実測）
    8. 追記評価7: conv 仮説（convExpD/convAbsExpD）の整備 — cauchyProduct
       公理を削除し expAddD を cauchyProductLim（定理）+ conv 仮説に張り替え
       （実測: 実解析公理 {convExpD, convAbsExpD, infSumIsLim, mertens,
       infSumLin, infSumNonneg}、目標 {infSumNonneg, infSumLin} 未達）
    9. 追記評価8: conv 仮説の定理化評価 — mulLe（乗法単調性）・
       facGePowTwo（2ᵏ ≤ (k+1)!）・rpowLeOne を公理ゼロで実証。
       残り（invLe・幾何級数・比較判定・単調収束・infSumIsLim 同定）は
       本格実解析として将来課題。目標 {infSumNonneg, infSumLin} は未達
       （convExpD/convAbsExpD は評価公理のまま、#print axioms 実測は
       {convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin,
       infSumNonneg} の 6 つのまま）
   10. 追記評価9: expZeroD（expD 0 = 1）を追加公理なしで導出（部分和 = 1
       の列 + convConst + infSumIsLim の極限同定。依存は既存の infSumIsLim
       等のみで、exp ブロック {exp, expZero, expAdd, expSeries} には完全
       非依存を #print axioms で実測）。expZero は D ワールド（expD 系・
       gaussPsdD）から完全に除去された。
   11. 追記評価10: gaussPsdD を infSumFinSwap から infSumFinSwapConv（収束
       仮定付き、PosDef.lean 追記評価10）に張り替え、conv 仮説 hK を
       convExpD（既存公理）から供給（convExt + expSummand + expMidD +
       convEq）。依存から infSumLin 公理が消滅（#print axioms 実測:
       {convExpD, convAbsExpD, infSumIsLim, mertens, infSumNonneg} の 5 つ）。
   12. 追記評価11: expD / expDSeries / convExpD / convAbsExpD を PosDef.lean
       へ移設（棚卸しの除去経路①、Stage D′ セクション）。open PosDef 経由で
       参照するため名前空間変更はコードに影響せず、gaussPsdD の依存公理は
       5 つのまま（#print axioms 実測: {PosDef.convExpD, PosDef.convAbsExpD,
       PosDef.infSumIsLim, PosDef.mertens, PosDef.infSumNonneg}）。expD /
       expDSeries 自体は公理ゼロ（インフラのみ）。依存循環は解消。
   13. 追記評価12: 本ファイルの二項定理チェーン（nCr ... binomTaylor）・
       expAddD・D ワールド gaussPsdD を PosDef.lean（namespace PosDef、追記評価12
       セクション）へ移設（除去経路②）。gaussPsdD が PosDef 層で利用可能に
       なり、#print axioms 実測で {convExpD, convAbsExpD, infSumIsLim, mertens,
       infSumNonneg} の 5 公理（exp ブロック・infSumLin 非依存）。チェーンの
       追記評価14（本ファイルの依存側の補足）: infSumLin 公理と派生チェーン 6 件
       は PosDef.lean から削除された。本ファイル内の infSumLin への言及はすべて
       削除前の評価記録（歴史的記録）であり、現行コードの依存ではない。
       Nat 補題 subSelf は ℝ 版と衝突するため nSubSelf に改名。本ファイルには
       追記評価7/8/9/10 の評価記録のみ残る（open PosDef 経由で参照）。

  補足: 二項定理チェーン（nCr / Nat 補題群 / binomTaylor）は追記評価12 で
  PosDef.lean へ移設済み。本ファイルの残りは評価記録（追記評価7/8/9/10）で、
   GroundZero のライブラリ命名と衝突しないよう名前空間 BinomTaylor を使用。

  注意: binomTaylorPw / binomTaylor / expDSeries の一部ステップは rdiv と
  expD の定義的展開（rdiv a b ≡ a · rin b、expD t ≡ Σₙ tⁿ/n!、rin は
  hasInv.inv の透明なラッパー）に依存する。rdiv / rin / expD の透明度を
  変更すると `by reflexivity` ステップが壊れるため、Reals.lean 側でこれら
  の定義を opaque 化しないこと。
  ============================================================================
-/

open GroundZero.Algebra
open GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Proto (explode)
open GroundZero.Theorems.Nat
open GroundZero.Types.Equiv (transport)
open PosDef

namespace BinomTaylor

universe u

/- ============================================================
   追記評価12: 本ファイルの二項定理チェーン（nCr ... binomTaylor）・
   expAddD・D ワールド gaussPsdD は PosDef.lean（namespace PosDef、
   追記評価12 セクション）へ移設した（除去経路②）。以降の追記評価7/8/9/10
   セクションは open PosDef 経由で expD / convExpD / gaussPsdD 等を参照する。
   ============================================================ -/

/- ============================================================
   追記評価7: conv 仮説（絶対収束）の整備 — cauchyProduct の削除（実行済み）
   ============================================================

   実行内容: cauchyProduct 公理をライブラリから削除し、expAddD を
   cauchyProductLim（追記評価6 の定理）+ conv 仮説に張り替えた。
   conv 仮説（convExpD / convAbsExpD）は上記 追記評価5（続き）セクションに
   配置: convExpD a は Σₖ aᵏ/k! の部分和が expD a に収束すること、
   convAbsExpD a は Σₖ |a|ᵏ/k! が絶対収束すること。
   これらは現行公理から導出不能（構造的理由）:
     · infSumIsLim は「conv → 極限同定」の一方向のみで、逆方向
       （infiniteSum f = L → conv）を与えない。
     · mertens は conv 仮説を仮定する公理であり、比較判定・比率判定の
       理論（テールバウンド）はライブラリに無い。
   よって conv 仮説は評価公理として追加した（古典解析では比較判定・
   比率判定の定理。TODO: 実解析理論の完成で導出）。

   公理検証（#print axioms 実測、張り替え後）:
     expAddD   = {convExpD, convAbsExpD, infSumIsLim, mertens, infiniteSum,
                  infiniteSum.ext, R, R.dedekind, Quot.sound, GroundZero}
     gaussPsdD = {GroundZero, convExpD, convAbsExpD, uaweak, uaweakβ,
                  infSumIsLim, infSumLin, infSumNonneg, mertens, Quot.sound,
                  R, infiniteSum, R.dedekind, infiniteSum.ext, choice}
   → cauchyProduct 公理は完全に消滅（定理 cauchyProductLim + conv 仮説に置換）。

   結論（目標 {infSumNonneg, infSumLin} には到達しない）:
     · 実解析公理は 3個 {cauchyProduct, infSumLin, infSumNonneg} から
       6個 {convExpD, convAbsExpD, infSumIsLim, mertens, infSumLin,
       infSumNonneg} に増える。
     · ただし cauchyProduct（任意の列に対する無条件の全称公理）は消え、
       「標準的な解析公理群」（極限同定 infSumIsLim・絶対収束版コーシー積
       mertens・指数級数の収束 convExpD/convAbsExpD）に置き換わる。
     · {infSumNonneg, infSumLin} への完全縮減は convExpD/convAbsExpD/
       infSumIsLim/mertens の定理化（本格的な実解析: 比較判定・比率判定・
       単調収束）を要し、現ライブラリの射程外。
     · なお expAddD 単体は {convExpD, convAbsExpD, infSumIsLim, mertens}
       のみ（infSumLin / infSumNonneg は infSumFinSwap 経由で gaussPsdD に
       のみ現れる）。 -/

/- ============================================================
   追記評価8: conv 仮説（convExpD / convAbsExpD）の定理化評価
   — 最小実解析の第一歩: mulLe と fac の指数バウンド
   ============================================================

   目標: 追記評価7 の評価公理 convExpD / convAbsExpD を定理化し、
   gaussPsdD の実解析公理を {infSumNonneg, infSumLin} まで縮減する。

   本節で実証（公理ゼロ）:
     · mulLeRight / mulLe — 乗法単調性（ライブラリに無かった基本補題）。
       0 ≤ a → b ≤ c → a·b ≤ a·c は subGeZeroIfLe + leOverMul +
       leIfSubGeZero + distribLeft + mulNeg + mulComm から導出可能。
     · twoLeSuccSucc — max ベースの Nat 順序 2 ≤ k+2（le.map + max.zeroLeft）。
     · facGePowTwo — 階乗の指数バウンド 2ᵏ ≤ (k+1)!（帰納法 + mulLe）。
     · rpowLeOne — 0 ≤ r ≤ 1 → rⁿ ≤ 1（幾何級数比較の準備）。

   定理化の残りチェーン（すべて「原理的には導出可能」。構造的ブロッカー
   （反例・一方向性）が無い点は 追記評価2/3 の infSumFinSwap と異なる）:
     (1) invLe（逆数単調性）: 0 < a → a ≤ b → b⁻¹ ≤ a⁻¹。
         facGePowTwo から 1/(k+1)! ≤ 1/2ᵏ を得るのに必要。
     (2) 幾何級数の部分和: Σ_{k≤n} rᵏ = (1 - rⁿ⁺¹)/(1 - r) と r < 1 での
         上界 1/(1 - r)（閉形式 + rdiv の順序理論）。
     (3) 比較判定: |t|ᵏ/k! ≤ C·(|t|/2)ᵏ から部分和の有界性
         （majorized (series ·) の構成）。rpowMul / absMul / rpowLeOne を使用。
         注意: facGePowTwo は 2ᵏ ≤ (k+1)! の形なので、応用は尾部
         |t|ᵏ⁺¹/(k+1)! ≤ |t|·(|t|/2)ᵏ となり、k = 0 の項（= 1）は
         別途先頭処理が必要。
     (4) 単調収束: sumMonotone + majorized → conv（部分和の sup への
         ε-N 収束）。sup.exact + 狭義順序補題（x - ε < x 等）で導出可能。
     (5) 同定: infSumIsLim（conv → infiniteSum = sup）で sup を
         infiniteSum に張り替え、transport で convExpD を得る。

   補足: mulLe / mulLeRight は一般的な順序体の基本補題であり、将来
   PosDef の数値補題セクション（mulNonneg / mulPos / mulLeZero の隣）への
   昇格候補。現状は本評価セクション内でのみ使用。

   結論: 目標 {infSumNonneg, infSumLin} には未達。convExpD / convAbsExpD は
   評価公理のまま残る（gaussPsdD の実解析公理は {convExpD, convAbsExpD,
   infSumIsLim, mertens, infSumLin, infSumNonneg} の 6 つのまま、#print axioms
   実測）。ただし本節の mulLe / facGePowTwo / rpowLeOne は比較判定への
   第一歩であり、定理化に構造的ブロッカーが無いことを実証した。残りは
   本格的な実解析（比較判定・単調収束の整備）として将来課題。
   注意: 本ライブラリの calc は独自 elaborator（Rewrite 型クラス合成）を
   使うため、calc ステップの `by exact idp _`（プレースホルダ付き）は
   文脈によって Rewrite 合成に失敗する。変更時は明示的な idp <term>
   （例: idp (fac (Nat.succ 0))）または中間式を避けた形にすること。
   ============================================================ -/

  /-- 乗法単調性（右因子）: 0 ≤ a → b ≤ c → a·b ≤ a·c -/
  hott lemma mulLeRight {a b c : ℝ} (pa : R.ρ 0 a) (pbc : R.ρ b c) : R.ρ (a * b) (a * c) :=
  begin
    apply leIfSubGeZero R;
    apply Equiv.transport (λ w, R.ρ 0 w);
    { exact calc a * (c - b) = a * (c + (-b)) : by exact idp _,
                              = a * c + a * (-b) : @ring.distribLeft R.τ _ a c (-b),
                              = a * c + -(a * b) : ap (a * c + ·) (@ring.mulNeg R.τ _ a b),
                              = a * c - a * b : by exact idp _ };
    exact orfield.leOverMul a (c - b) pa (subGeZeroIfLe R pbc)
  end

  /-- 乗法単調性: a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a·c ≤ b·d -/
  hott lemma mulLe {a b c d : ℝ} (pab : R.ρ a b) (pcd : R.ρ c d)
    (pa : R.ρ 0 a) (pc : R.ρ 0 c) : R.ρ (a * c) (b * d) :=
  begin
    apply @transitive.trans R.κ _ (a * c) (b * c) (b * d);
    { apply Equiv.transport (λ w, R.ρ w (b * c));
      { exact @ring.comm.mulComm R.τ _ c a };
      apply Equiv.transport (λ w, R.ρ (c * a) w);
      { exact @ring.comm.mulComm R.τ _ c b };
      exact mulLeRight (a := c) (b := a) (c := b) pc pab };
    { apply mulLeRight (a := b) (b := c) (c := d);
      { apply @transitive.trans R.κ _ (0 : ℝ) a b; exact pa; exact pab };
      exact pcd }
  end

  /-- 自然数: 2 ≤ k+2（max ベースの le で成立） -/
  hott lemma twoLeSuccSucc (k : ℕ) : le 2 (Nat.succ (Nat.succ k)) :=
    le.map 1 (Nat.succ k) (le.map 0 k (GroundZero.Theorems.Nat.max.zeroLeft k))

  /-- 階乗の指数バウンド: 2ᵏ ≤ (k+1)! -/
  hott lemma facGePowTwo : Π (k : ℕ), R.ρ (rpow (1 + 1 : ℝ) k) (fac (Nat.succ k)) :=
  begin
    intro k; induction k with
    | zero =>
        have hfac : fac (Nat.succ 0) = (1 : ℝ) :=
          calc fac (Nat.succ 0) = 0 + 1 : @ring.monoid.oneMul R.τ _ (0 + 1),
                               = 1 : R.τ.zeroAdd (1 : ℝ);
        apply Equiv.transport (λ w, R.ρ (rpow (1 + 1 : ℝ) 0) w);
        { exact Id.symm hfac };
        exact @reflexive.refl R.κ _ (1 : ℝ)
    | succ k ih =>
        apply @transitive.trans R.κ _
          (rpow (1 + 1 : ℝ) k * (1 + 1 : ℝ))
          (fac (Nat.succ k) * (1 + 1 : ℝ))
          (fac (Nat.succ k) * N.incl (Nat.succ (Nat.succ k)));
        { exact mulLe ih (@reflexive.refl R.κ _ (1 + 1 : ℝ))
            (rpowNonneg zeroLtTwo.2 k) zeroLtTwo.2 };
        { apply mulLeRight (a := fac (Nat.succ k)) (b := (1 + 1 : ℝ)) (c := N.incl (Nat.succ (Nat.succ k)));
          { exact (facPos (Nat.succ k)).2 };
          { apply Equiv.transport (λ w, R.ρ w (N.incl (Nat.succ (Nat.succ k))));
            { exact calc N.incl 2 = (1 : ℝ) + 1 : ap (· + 1) (R.τ.zeroAdd (1 : ℝ)),
                             = 1 + 1 : idp ((1 : ℝ) + 1) };
            exact N.incl.lt 2 (Nat.succ (Nat.succ k)) (twoLeSuccSucc k) } }
  end

  /-- 冪の単調性: 0 ≤ r ≤ 1 → rⁿ ≤ 1（幾何級数比較の準備） -/
  hott lemma rpowLeOne {r : ℝ} (p0 : R.ρ 0 r) (p1 : R.ρ r 1) :
    Π (n : ℕ), R.ρ (rpow r n) 1 :=
  begin
    intro n; induction n with
    | zero => exact @reflexive.refl R.κ _ (rpow r 0)
    | succ n ih =>
        apply @transitive.trans R.κ _ (rpow r (Nat.succ n)) (rpow r n * r) (1 : ℝ);
        { exact @reflexive.refl R.κ _ (rpow r (Nat.succ n)) };
        apply Equiv.transport (R.ρ (rpow r n * r));
        { exact @ring.monoid.oneMul R.τ _ (1 : ℝ) };
        exact mulLe ih p1 (rpowNonneg p0 n) p0
  end

/- ============================================================
   追記評価9: expZeroD（expD 0 = 1）の公理なし導出
   — expZero 系の gaussPsdD 依存からの完全除去
   ============================================================

   目標: 追記評価5（続き）で「公理（残す）」とされていた expZeroD を
   定理化する。当時の注記は「線型性 + 非負性（{infSumLin, infSumNonneg}）
   からは L(δ₀) = 0 の正線形汎関数が存在するため決まらない」というもの
   だったが、現行の公理集合には極限同定の infSumIsLim が含まれており、
   それを使えば導出できる（L(δ₀) は実際の極限として一意に定まる）。

   証明の構成（追加公理は無し。いずれも定理）:
     · rinOne — 逆元の 1: rin 1 = 1（invEqOfMulEqOne + oneMulL）。
     · rdivZero / rdivOneOne — 除法の基本（0/x = 0、1/1 = 1）。
     · rpowZeroSucc — 0ⁿ = 0（n ≥ 1）。
     · expPartialSumOne — 級数 Σₖ 0ᵏ/k! の部分和は常に 1
       （列 (1, 0, 0, …)。帰納法 + rdivZero）。
     · convPartialSumOne — 部分和列は 1 に収束（convConst + convExt）。
     · expZeroD — expDSeries + infSumIsLim で極限同定。

   実測（#print axioms）:
     · expZeroD の依存公理は {infSumIsLim, infiniteSum, R, R.dedekind,
       Quot.sound, uaweak, uaweakβ, choice, GroundZero} —
       exp ブロック {exp, expZero, expAdd, expSeries} は完全に非依存。
     · expPartialSumOne / rdivOneOne 等は {R, R.dedekind, Quot.sound} のみ。

   結論: expZero は D ワールド（expD 系・gaussPsdD）から完全に除去された。
   gaussPsdD の依存は {convExpD, convAbsExpD, infSumIsLim, infSumLin,
   infSumNonneg, mertens} のまま（もともと expZero 非依存）で、expZeroD も
   追加公理なしの定理になった。旧 expZero 公理（Reals.lean）はレガシー
   exp ブロック（PosDef の元の gaussPsd）でのみ使用される。
   ============================================================ -/

  /-- 逆元の 1: rin 1 = 1 -/
  hott lemma rinOne : rin (1 : ℝ) = 1 :=
  Id.symm (invEqOfMulEqOne (posProper (1 : ℝ) zeroLtOne) (oneMulL (1 : ℝ)))

  /-- 0 の除算: rdiv 0 x = 0 -/
  hott lemma rdivZero (x : ℝ) : rdiv 0 x = 0 :=
  @ring.zeroMul R.τ _ (@ring.hasInv.inv R.τ _ x)

  /-- 1 の除算: rdiv 1 1 = 1 -/
  hott lemma rdivOneOne : rdiv (1 : ℝ) 1 = 1 :=
  @ring.monoid.oneMul R.τ _ (@ring.hasInv.inv R.τ _ (1 : ℝ)) ⬝ rinOne

  /-- 0ⁿ = 0（n ≥ 1）: rpow 0 (n+1) = 0 -/
  hott lemma rpowZeroSucc (n : ℕ) : rpow 0 (Nat.succ n) = 0 :=
  @ring.mulZero R.τ _ (rpow 0 n)

  /-- 部分和は常に 1: Σ_{k≤n} 0ᵏ/k! = 1（n ≥ 0 で n+1 項） -/
  hott lemma expPartialSumOne : Π (n : ℕ),
    sum (Nat.succ n) (λ k, rdiv (rpow 0 k) (fac k)) = 1 :=
  begin
    intro n; induction n with
    | zero =>
        have h0 : rdiv (rpow 0 0) (fac 0) = 1 :=
          (by exact idp _ : rdiv (rpow 0 0) (fac 0) = rdiv (1 : ℝ) 1) ⬝ rdivOneOne
        have hsum : sum (Nat.succ 0) (λ k, rdiv (rpow 0 k) (fac k)) = 1 :=
          (by exact idp _ :
            sum (Nat.succ 0) (λ k, rdiv (rpow 0 k) (fac k)) = 0 + rdiv (rpow 0 0) (fac 0)) ⬝
          R.τ.zeroAdd (rdiv (rpow 0 0) (fac 0)) ⬝
          h0
        exact hsum
    | succ n ih =>
        have hstep : rdiv (rpow 0 (Nat.succ n)) (fac (Nat.succ n)) = 0 :=
          ap (λ z, rdiv z (fac (Nat.succ n))) (rpowZeroSucc n) ⬝
          rdivZero (fac (Nat.succ n))
        have hsum : sum (Nat.succ (Nat.succ n)) (λ k, rdiv (rpow 0 k) (fac k)) = 1 :=
          (by exact idp _ :
            sum (Nat.succ (Nat.succ n)) (λ k, rdiv (rpow 0 k) (fac k)) =
              sum (Nat.succ n) (λ k, rdiv (rpow 0 k) (fac k)) + rdiv (rpow 0 (Nat.succ n)) (fac (Nat.succ n))) ⬝
          ap (· + rdiv (rpow 0 (Nat.succ n)) (fac (Nat.succ n))) ih ⬝
          ap (1 + ·) hstep ⬝
          R.τ.addZero (1 : ℝ)
        exact hsum
  end

  /-- 部分和列は 1 に収束する（定数列 convConst からの外延性） -/
  hott lemma convPartialSumOne :
    conv (λ n, sum (Nat.succ n) (λ k, rdiv (rpow 0 k) (fac k))) 1 :=
  convExt (λ n, 1) (λ n, sum (Nat.succ n) (λ k, rdiv (rpow 0 k) (fac k))) 1
    (λ n, Id.symm (expPartialSumOne n)) (convConst 1)

  /-- expD の正規化: expD 0 = 1（expZero 公理なし。infSumIsLim のみで同定） -/
  hott theorem expZeroD : expD 0 = (1 : ℝ) :=
  calc expD 0
       = infiniteSum (λ n, rdiv (rpow 0 n) (fac n)) : expDSeries 0,
       = 1 : infSumIsLim (λ n, rdiv (rpow 0 n) (fac n)) 1 convPartialSumOne

end BinomTaylor
