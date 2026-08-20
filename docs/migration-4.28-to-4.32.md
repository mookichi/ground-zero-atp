# Lean 4.28 → 4.32.2 移行メモ

## 概要
- 旧バージョン: `leanprover/lean4:4.28.0`
- 新バージョン: `leanprover/lean4:4.32.2`
- 移行日: 2026-08-20

## 破壊的変更サマリ

### 1. CollectAxioms.collect の削除（4.32系）
- 旧: `(CollectAxioms.collect name).run env |>.run {}` → `State` を返す
- 新: `Lean.collectAxioms name` → `m (Array Name)` を返す（MonadEnv を要求）
- ファイル: `GroundZero/Meta/HottTheory.lean:128`

### 2. Level.quote のシグネチャ変更
- 旧: `Level.quote (n : Level) (prec : Nat) : Syntax.Level`
- 新: `Level.quote (n : Level) (prec : Nat) (b : Bool) (f : LMVarId → Option Nat) : Syntax.Level`
- ファイル: `GroundZero/Meta/Notation.lean:15`

### 3. isDefEq の透明性（Transparency）変更（4.29系）
- `isDefEq` が暗黙引数を比較する際に透明性を `.default` に上げる挙動がデフォルト無効化
- 回避: `set_option backward.isDefEq.respectTransparency false`
- 湖ファイルにプロジェクト全体設定を追加済み

### 4. simp/dsimp のインスタンス処理変更（4.29系）
- `simp`/`dsimp` がデフォルトで型クラスインスタンスを展開しなくなる
- 回避: `set_option backward.dsimp.instances true` または `simp +instances`

### 5. inferInstanceAs のシグネチャ変更（4.29/4.30系）
- 旧: `inferInstanceAs α` で型推論
- 新: 期待型 β が推論できる必要がある。同一型の場合は `inferInstance` を使う

### 6. do 記法のデフォルト変更（4.32系）
- 新しい do elaborator がデフォルトに（`backward.do.legacy = false`）
- `do match` が非依存、Pure インスタンスが必須
- 回避: `set_option backward.do.legacy true`

### 7. Lean.RBMap / Lean.RBTree 非推奨（4.32系）
- `Std.TreeMap` / `Std.TreeSet` に移行推奨

### 8. noncomputable セマンティクス厳格化（4.29系）
- axiom や noncomputable def を使う定義に `noncomputable` がより多く必要に

## 修正済み
- [x] `CollectAxioms.collect` → `Lean.collectAxioms` (`HottTheory.lean`)
- [x] `Level.quote` シグネチャ更新 (`Notation.lean`)
- [x] `Interval.ind` の暗黙引数を `@Interval.ind` で明示化 (`Path.lean`)
- [x] `begin`/`end` → `by` に変更 (`Path.lean`)
- [x] class の universe level 推論修正：`geodesic` の返り型に `Ens.{u, 0}` を明示 (`Geometry.lean`)
- [x] `instance` → `def` に変更（戻り型が型クラスでない場合）(`Periodic.lean`)
- [x] `complete`/`cocomplete` class に `Orgraph.{u, v}` を明示 (`Orgraph.lean`)
- [x] `dedekind` の `.{0}` universe 引数削除 (`Reals.lean`)

## 残作業（任意）
- `hott instance` には `@[reducible]` を直接付与できない（マクロ構文の制約）。残り4件の警告は許容範囲
