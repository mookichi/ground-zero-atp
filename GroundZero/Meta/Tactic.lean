import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Replace
import Lean.Elab.Command

open Lean

universe u v w u' v' w'

section
  variable {A : Sort u} (ρ : A → A → Sort v)

  class Reflexive :=
  (intro (a : A) : ρ a a)

  class Symmetric :=
  (intro (a b : A) : ρ a b → ρ b a)

  class Transitive :=
  (intro (a b c : A) : ρ a b → ρ b c → ρ a c)
end

section
  variable {A : Sort u} {B : Sort v} {C : Sort w}

  variable (ρ : A → B → Sort u')
  variable (η : B → C → Sort v')
  variable (μ : outParam (A → C → Sort w'))

  class Rewrite :=
  (intro (a : A) (b : B) (c : C) : ρ a b → η b c → μ a c)
end

namespace GroundZero.Meta.Tactic

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Ring.lean#L411-L419
def applyOnBinRel (name : Name) (rel : Name) : Elab.Tactic.TacticM Unit := do
  let mvars ← Elab.Tactic.liftMetaMAtMain (λ mvar => do
    let ε ← instantiateMVars (← MVarId.getDecl mvar).type
    ε.consumeMData.withApp λ e es => do
      unless (es.size > 1) do Meta.throwTacticEx name mvar s!"expected binary relation, got “{e} {es}”"

      let e₃ := es.back!; let es := es.pop;
      let e₂ := es.back!; let es := es.pop;

      let ty  ← Meta.inferType e₂
      let ty' ← Meta.inferType e₃

      unless (← Meta.isDefEq ty ty') do Meta.throwTacticEx name mvar s!"{ty} ≠ {ty'}"

      let u ← Meta.getLevel ty
      let v ← Meta.getLevel ε

      let ι ← Meta.synthInstance (mkApp2 (Lean.mkConst rel [u, v]) ty (mkAppN e es))
      let φ := (← Meta.reduceProj? (mkProj rel 0 ι)).getD ι

      MVarId.apply mvar φ)
  Elab.Tactic.replaceMainGoal mvars

section
  elab "reflexivity"  : tactic => applyOnBinRel `reflexivity  `Reflexive
  elab "symmetry"     : tactic => applyOnBinRel `symmetry     `Symmetric
  elab "transitivity" : tactic => applyOnBinRel `transitivity `Transitive
end

elab "fapply " e:term : tactic =>
  Elab.Tactic.evalApplyLikeTactic (MVarId.apply (cfg := {newGoals := Meta.ApplyNewGoals.all})) e

macro_rules | `(tactic| change $e:term) => `(tactic| show $e)

-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/LeftRight.lean
-- Author: Siddhartha Gadgil
def getCtors (name : Name) (mvar : MVarId) : MetaM (List Name × List Level) := do
    MVarId.checkNotAssigned mvar name
    let target ← MVarId.getType' mvar
    matchConstInduct target.getAppFn
      (λ _ => Meta.throwTacticEx `constructor mvar "target is not an inductive datatype")
      (λ ival us => return (ival.ctors, us))

def leftRightMeta (pickLeft : Bool) (mvar : MVarId) : MetaM (List MVarId) := do
  MVarId.withContext mvar do
    let name := if pickLeft then `left else `right
    let (ctors, us) ← getCtors name mvar
    unless ctors.length == 2 do
      Meta.throwTacticEx `constructor mvar
        s!"{name} target applies for inductive types with exactly two constructors"
    -- Who thought it would be a good idea to remove `List.get!` and leave *only* `xs[n]!` syntax?
    let ctor := ctors[if pickLeft then 0 else 1]!
    MVarId.apply mvar (mkConst ctor us)

elab "left"  : tactic => Elab.Tactic.liftMetaTactic (leftRightMeta true)
elab "right" : tactic => Elab.Tactic.liftMetaTactic (leftRightMeta false)

elab "whnf" : tactic => do
  let mvarId ← Elab.Tactic.getMainGoal
  let target ← Elab.Tactic.getMainTarget
  let targetNew ← Meta.whnf target
  Elab.Tactic.replaceMainGoal [← MVarId.replaceTargetDefEq mvarId targetNew]

def getExistsiCtor (mvar : MVarId) : MetaM Name := do
  MVarId.withContext mvar do
    let (ctors, us) ← getCtors `existsi mvar
    unless ctors.length == 1 do
      Meta.throwTacticEx `constructor mvar
        "existsi target applies for inductive types with exactly one constructor"
    return ctors[0]!

elab "existsi" e:term : tactic => do
  let ctor ← Elab.Tactic.liftMetaMAtMain getExistsiCtor
  let ε := Syntax.mkApp (mkIdent ctor) #[e]
  Elab.Tactic.evalTactic (← `(tactic| apply $ε))

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/How.20to.20use.20hand.20written.20parsers/near/245760023
-- Author: Mario Carneiro

abbrev ellipsisInfoKind : SyntaxNodeKind := `ellipsis

def ellipsis := Syntax.node SourceInfo.none ellipsisInfoKind #[]

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Parser.2EtrailingLoop
def calcRHS : Parser.Parser :=
Parser.withFn (λ _ c s =>
  let category := (Parser.getCategory (Parser.parserExtension.getState c.env).categories `term).get!
  Parser.trailingLoop category.tables c (s.pushSyntax ellipsis)) Parser.termParser

open PrettyPrinter Elab.Term

def expandBinaryRelation (e : Expr) : TermElabM (Expr × Expr) :=
  e.withApp λ e es => do
    unless (es.size > 1) do throwError "expected binary relation"
    return (es.back!, mkAppN e es.pop.pop)

def expandRHS (e : Syntax) : TermElabM (Syntax × Syntax) := do
  unless (e.getArgs.size > 2) do throwError "expected binary relation"
  return (e.getArgs[0]!, e.getArgs[2]!)

elab (priority := high) "calc " ε:term " : " τ:term ", " σ:(calcRHS " : " term),+ : term => do
  let σ ← Array.mapM expandRHS σ

  let ε ← Elab.Term.elabTerm ε none
  let ε ← instantiateMVars ε

  let e₁ := ε.withApp (λ _ es => es.pop.back!)
  let ty₁ ← Meta.inferType e₁
  let u₁  ← Meta.getLevel ty₁

  let mut (e₂, ρ₁) ← expandBinaryRelation ε
  let mut η ← Elab.Term.elabTermEnsuringType τ ε

  let mut ty₂ ← Meta.inferType e₂
  let mut u₂  ← Meta.getLevel ty₂

  let mut v₁ ← Meta.getLevel ε

  for (e, τ) in σ do
    guard <| (e.getArg 0).isOfKind ellipsisInfoKind

    let ε ← Elab.Term.elabTerm (e.setArg 0 (← PrettyPrinter.delab e₂)) none
    let ε ← instantiateMVars ε

    let τ ← Elab.Term.elabTermEnsuringType τ ε
    let mut v₂ ← Meta.getLevel ε

    let (e₃, ρ₂) ← expandBinaryRelation ε

    let ty₃ ← Meta.inferType e₃
    let u₃  ← Meta.getLevel ty₃

    let v₃ ← Meta.mkFreshLevelMVar
    let ρ₃ ← Meta.mkFreshExprMVar none

    let ι ← Meta.synthInstance (mkApp6 (Lean.mkConst `Rewrite [u₁, u₂, u₃, v₁, v₂, v₃]) ty₁ ty₂ ty₃ ρ₁ ρ₂ ρ₃)
    let φ := (← Meta.reduceProj? (mkProj `Rewrite 0 ι)).getD ι

    η := mkAppN φ #[e₁, e₂, e₃, η, τ]
    (ty₂, u₂, e₂, v₁, ρ₁) := (ty₃, u₃, e₃, v₃, ρ₃)

  return η

/- === path_simp: HoTT path-algebra normalizer =============================

  A congruence rewrite engine for the free-groupoid fragment of Ground Zero's
  `Id` (path) type.  Core `rw`/`MVarId.rewrite` only accepts native `Eq`/
  `Iff`/definitional equations, so hott `Id` equations cannot be rewritten
  with them; this engine implements matching via `Meta.isDefEq` and proof
  reconstruction via `Id.trans`/`Id.symm`/`Id.ap` directly (the HoTT analogue
  of mathlib's `ring` reflection).

  Rules (`pathRules`, right-associated canonical form; order is load-bearing):
    assoc (rev)   p ⬝ (q ⬝ r) ↦ (p ⬝ q) ⬝ r
    assoc (fwd)   (p ⬝ q) ⬝ r ↦ p ⬝ (q ⬝ r)
    rid           p ⬝ idp b   ↦ p
    compInv       p ⬝ p⁻¹     ↦ idp a
    invComp       p⁻¹ ⬝ p     ↦ idp b
    explodeInv    (p ⬝ q)⁻¹   ↦ q⁻¹ ⬝ p⁻¹
    invInv        (p⁻¹)⁻¹     ↦ p
    apComp        ap f (p ⬝ q) ↦ ap f p ⬝ ap f q   (and reverse)
    mapInv        ap f p⁻¹    ↦ (ap f p)⁻¹
    loop₁         ν ⬝ κ ↦ ν ⋆ κ            [EH fragment, 2-paths]
    compUniq      ν ⋆ κ ↦ ν ⋆′ κ           [interchange]
    loop₂         ν ⋆′ κ ↦ κ ⬝ ν           [EH fragment]
    comm          ν ⬝ κ ↦ κ ⬝ ν            [loop commutation]

  Additionally, `hypRules` derives whiskering rewrites from *context* 2-path
  hypotheses: from `h : p = q` (p, q themselves paths) it supplies
  `p ⬝ r ↦ q ⬝ r` (rwhs) and `r ⬝ p ↦ r ⬝ q` (lwhs), in both directions.
  Head matching is structural: the pre-check compares canonical head constant
  names (so the reducible alias `Id.inv` = `symm` matches `symm`-headed
  patterns), and it refuses to fire `⬝`-patterns on the whiskering defs
  (`horizontalComp₁` etc. unfold to `trans`-soups that would re-whisker
  forever).  The residual goal is closed with `reflexivity`; if it cannot be
  closed the tactic FAILS (so `first | path_simp | …` falls through on
  non-path goals).  All proofs are built from the library's own lemmas — no
  new axioms.  Termination: the visited set (goal types, UNREDUCED) plus a
  64-iteration cap stop the assoc/comm/loop ping-pongs.

  Prototyped in a disposable probe; regression tests live at the end of
  GroundZero/Types/Id.lean and in GroundZero/HITs/Circle.lean. -/

open Elab Tactic Meta

namespace PathSimp

/-- Apply a (possibly polymorphic, possibly Π-typed) constant to fresh metavariables. -/
partial def applyToFresh (e : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  match ty with
  | .forallE _ d _ _ =>
      let x ← mkFreshExprMVar d
      applyToFresh (mkApp e x)
  | _ => pure e

/-- Instantiate the lemma at fresh metavariables; returns (lhs, proof) sharing mvars. -/
def buildRule (nm : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo nm
  let lvls ← cinfo.levelParams.mapM (λ _ => mkFreshLevelMVar)
  let e ← applyToFresh (mkConst nm lvls)
  let ty ← inferType e
  -- the rule lemma must be an Id equation `lhs = rhs`; anything else is a
  -- configuration error (fail cleanly rather than PANIC on the spine)
  unless ty.isAppOf `GroundZero.Types.Id do
    throwError "path_simp: rule {nm} does not state an Id equation"
  pure (ty.appFn!.appArg!, e)

/-- The `Id` universe level from an Id application `Id.{u} x y`. -/
def idLevel (e : Expr) : Level :=
  match e with
  | .app f _ => idLevel f
  | .const _ (u :: _) => u
  | _ => levelZero

/-- The path space `x = y` of a path `l : x = y` (the carrier of the Id TYPE
    itself) and its universe level.  `Id.trans`/`Id.symm` act on this space:
    their carrier is the type `x = y`, not `x`'s type. -/
def pathSpaceOf (l : Expr) : MetaM (Expr × Level) := do
  let lty ← inferType l                  -- Id.{u} x y
  pure (lty, idLevel lty)

/-- Build `Id P x y` where P is the path space (carrier of the Id type). -/
def idTy (P : Expr) (u : Level) (x y : Expr) : Expr :=
  mkAppN (mkConst `GroundZero.Types.Id [u]) #[P, x, y]

/-- Flip a CONCRETE proof `l = r` to `r = l`: `@Id.symm P l r e`. -/
def symmOf (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  let l := ty.appFn!.appArg!
  let r := ty.appArg!
  let (P, u) ← pathSpaceOf l
  pure (mkAppN (mkConst `GroundZero.Types.Id.symm [u]) #[P, l, r, e])

/-- Run a MetaM action, returning none instead of throwing. -/
def tryM {α : Type} (x : MetaM α) : MetaM (Option α) :=
  try return some (← x) catch _ => pure none

/-- Congruence `ap (λ x, f x) pa : f x = f y` from `pa : x = y`, f : T → U.
    Only non-dependent unary contexts are liftable: ap needs `f x = f y` to
    typecheck, so the types of the two endpoints must agree.  A dependent
    context (e.g. a partially applied `trans` whose codomain mentions x) makes
    them differ; we throw so the caller skips this occurrence. -/
def apCtx (f pa : Expr) : MetaM Expr := do
  let fTy ← inferType f                 -- f : T → U  (a forall type, not an app)
  match fTy with
  | .forallE _ d _ _ =>
      let paTy ← inferType pa
      let l := paTy.appFn!.appArg!
      let r := paTy.appArg!
      let tl ← inferType (mkApp f l)
      let tr ← inferType (mkApp f r)
      unless (← Meta.isDefEq tl tr) do
        throwError "path_simp: apCtx: dependent context"
      let ctx := mkLambda `x BinderInfo.default d (mkApp f (mkBVar 0))
      mkAppM `GroundZero.Types.Id.ap #[ctx, pa]
  | _ => throwError "path_simp: apCtx: expected a function type, got {fTy}"

/-- Congruence `ap (λ g, g a) pf : f a = f' a` from `pf : f = f'`. -/
def apCtxArg (a pf : Expr) : MetaM Expr := do
  let pTy ← inferType pf
  let f := pTy.appFn!.appArg!
  let fTy ← inferType f
  let ctx := mkLambda `g BinderInfo.default fTy (mkApp (mkBVar 0) a)
  mkAppM `GroundZero.Types.Id.ap #[ctx, pf]

/-- Canonical head constant name: resolve reducible aliases so that a
    pattern headed by the canonical constant also matches terms headed by the
    alias (and vice versa).  `Id.inv` is defined as `symm` and `Id.refl` as
    `idp`, so without this an `⁻¹`-written rule (head `symm`) would never fire
    on an `Id.inv`-written goal.  KEEP IN SYNC with `GroundZero/Types/Id.lean`
    — if `inv`/`refl` are ever redefined, extend this table (a general
    one-step-unfold comparison is ruled out: `horizontalComp₁` unfolds to
    `trans`, which would defeat the structural head pre-check below). -/
def headCanon (n : Name) : Name :=
  if n == `GroundZero.Types.Id.inv then `GroundZero.Types.Id.symm
  else if n == `GroundZero.Types.Id.refl then `GroundZero.Types.Id.idp
  else n

/-- Replace all occurrences of `lhs` in `term`, collecting one path per
    occurrence.  `heq` shares mvars with `lhs`, so after a successful match
    the proof is concrete.  Guard: skip if the proof still has mvars. -/
partial def replaceAll (term lhs heq : Expr) : MetaM (List Expr) := do
  let mut out : List Expr := []
  -- Head-constant pre-check: the rules are structural, so a `trans`-pattern
  -- must not fire on a `horizontalComp₁` term just because isDefEq unfolds
  -- it (that is exactly how loop₁ re-whiskered its own output forever).  The
  -- head check makes `⬝`-patterns match only literal `⬝` applications.
  -- NOTE: compare constant NAMES, not Exprs — the pattern head carries a
  -- fresh level mvar (?u) that the goal's concrete level (u) never equals;
  -- and normalize aliases via headCanon (Id.inv ↦ Id.symm, Id.refl ↦ Id.idp).
  let lhsHead := lhs.getAppFn
  let termHead := (term.consumeMData).getAppFn
  let headOk :=
    if lhsHead.isConst && termHead.isConst then headCanon lhsHead.constName == headCanon termHead.constName
    else lhsHead == termHead
  if headOk then
    let s ← saveState
    if (← Meta.isDefEq lhs term) then
      let p ← instantiateMVars heq
      if p.hasMVar then restoreState s
      else out := out ++ [p]
    else
      restoreState s
  match term.consumeMData with
  | .app f a =>
      let s₁ ← saveState
      for pa in (← replaceAll a lhs heq) do
        if let some p ← tryM (apCtx f pa) then out := out ++ [p]
      restoreState s₁
      let s₂ ← saveState
      for pf in (← replaceAll f lhs heq) do
        if let some p ← tryM (apCtxArg a pf) then out := out ++ [p]
      restoreState s₂
  | .mdata _ b =>
      out := out ++ (← replaceAll b lhs heq)
  | _ => pure ()
  pure out

/-- Whether `t` (whnf'd) already appears among the visited goal types. -/
def isVisited (t : Expr) (visited : List Expr) : MetaM Bool := do
  for v in visited do
    let s ← saveState
    if (← Meta.isDefEq t v) then return true
    restoreState s
  pure false

/-- Rewrite one rule in the main goal `⊢ L = R`.  Returns (new goal, goal type).
    `flip` = true: the pattern is the lemma's RHS, rewrite uses the flipped proof.
    Matching is against the UNREDUCED goal: whnf'ing the goal would reduce the
    whiskering defs (`rwhs`/`lwhs`/`horizontalComp₁`/`₂`) to `rid`-soups that
    the other rules keep re-firing on (the EH fragments would re-whisker
    forever).  The visited set still uses whnf'd types for loop detection. -/
partial def stepRule (g : MVarId) (lhs heq : Expr) (flip : Bool) (visited : List Expr) :
    MetaM (Option (MVarId × Expr)) := do
  let sTop ← saveState
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf `GroundZero.Types.Id do return none
  let L := ty.appFn!.appArg!
  let R := ty.appArg!
  -- Already closed by reflexivity?  Leave it alone: the higher-order rules
  -- (EH fragments, loop commutation, whiskering) are NOT confluent, so
  -- rewriting a closed goal can push it away from defeq and the visited set
  -- would then halt the ping-pong in an open state.
  if (← Meta.isDefEq L R) then
    return none
  let (P, u) ← pathSpaceOf L
  -- L-side: rewrite inside L, goal becomes L' = R
  for path₀ in (← replaceAll L lhs heq) do
    let path ← if flip then symmOf path₀ else pure path₀
    let L' := (← inferType path).appArg!
    if (← Meta.isDefEq L L') then continue
    let s ← saveState
    let newM ← mkFreshExprMVar (idTy P u L' R)
    let proof := mkAppN (mkConst `GroundZero.Types.Id.trans [u]) #[P, L, L', R, path, newM]
    g.assign proof
    let t' ← instantiateMVars (← newM.mvarId!.getType)
    if (← isVisited t' visited) then restoreState s; continue
    return some (newM.mvarId!, t')
  -- R-side: rewrite inside R, goal becomes L = R', proof = symm (trans path …)
  -- Note: blocked L-side matches above may have assigned the rule's LOCAL
  -- mvars (fresh per buildRule call); harmless, since the none-path below
  -- restores sTop and the elab restores to before buildRule on every miss.
  let s₀ ← saveState
  let newM₁ ← mkFreshExprMVar (idTy P u R L)
  let proof₁ := mkAppN (mkConst `GroundZero.Types.Id.symm [u]) #[P, R, L, newM₁]
  g.assign proof₁
  for path₀ in (← replaceAll R lhs heq) do
    let path ← if flip then symmOf path₀ else pure path₀
    let R' := (← inferType path).appArg!
    if (← Meta.isDefEq R R') then continue
    let s₁ ← saveState
    let newM₂ ← mkFreshExprMVar (idTy P u R' L)
    let proof₂ := mkAppN (mkConst `GroundZero.Types.Id.trans [u]) #[P, R, R', L, path, newM₂]
    newM₁.mvarId!.assign proof₂
    let newM₃ ← mkFreshExprMVar (idTy P u L R')
    let proof₃ := mkAppN (mkConst `GroundZero.Types.Id.symm [u]) #[P, L, R', newM₃]
    newM₂.mvarId!.assign proof₃
    let t₃ ← instantiateMVars (← newM₃.mvarId!.getType)
    if (← isVisited t₃ visited) then restoreState s₁; continue
    return some (newM₃.mvarId!, t₃)
  -- none: restore the FULL pre-call state (also undoing the pattern-match
  -- mvar assignments made inside replaceAll), so stepRule is self-contained.
  restoreState sTop
  pure none

/-- The groupoid rewrite system: (lemma, reverse?).  Rule ORDER is load-bearing
    (flatten is tried before right-association; both are needed for the cancel
    lemmas).  The lemmas live in `GroundZero.Types.Id`. -/
def pathRules : List (Name × Bool) :=
  [ (`GroundZero.Types.Id.assoc,      true),  -- pattern = RHS p ⬝ (q ⬝ r) ↦ (p ⬝ q) ⬝ r   [flatten]
    (`GroundZero.Types.Id.assoc,      false), -- pattern = LHS (p ⬝ q) ⬝ r ↦ p ⬝ (q ⬝ r)   [right-associate]
    (`GroundZero.Types.Id.rid,        false), -- p ⬝ idp b ↦ p
    (`GroundZero.Types.Id.compInv,    false), -- p ⬝ p⁻¹ ↦ idp a
    (`GroundZero.Types.Id.invComp,    false), -- p⁻¹ ⬝ p ↦ idp b
    (`GroundZero.Types.Id.explodeInv, false), -- (p ⬝ q)⁻¹ ↦ q⁻¹ ⬝ p⁻¹
    (`GroundZero.Types.Id.invInv,     false), -- (p⁻¹)⁻¹ ↦ p
    (`GroundZero.Types.Id.apComp,     false), -- ap f (p ⬝ q) ↦ ap f p ⬝ ap f q   [2-naturality]
    (`GroundZero.Types.Id.apComp,     true),  -- ap f p ⬝ ap f q ↦ ap f (p ⬝ q)
    (`GroundZero.Types.Id.mapInv,     false), -- ap f p⁻¹ ↦ (ap f p)⁻¹
    (`GroundZero.Types.Whiskering.loop₁,    false), -- ν ⬝ κ ↦ ν ⋆ κ          [EH fragment]
    (`GroundZero.Types.Whiskering.compUniq, false), -- ν ⋆ κ ↦ ν ⋆′ κ         [interchange]
    (`GroundZero.Types.Whiskering.loop₂,    false), -- ν ⋆′ κ ↦ κ ⬝ ν         [EH fragment]
    (`GroundZero.Types.Whiskering.comm,     false) ] -- ν ⬝ κ ↦ κ ⬝ ν         [loop commutation]

/-- Build `rwhs h r₀ : p ⬝ r₀ = q ⬝ r₀` from a 2-path `h : p = q` (right
    whisker), with r₀ a fresh path.  Returns (lhs, proof).  None if h is not
    a 2-path (i.e. p, q are not themselves paths).  Built with an explicit
    mkAppN so no implicit-argument mvars survive (mkAppM would leave them,
    and the hasMVar guard in replaceAll would then reject the proof). -/
def rwhsProof (h : Expr) : MetaM (Option (Expr × Expr)) := do
  let hTy ← inferType h
  unless hTy.isAppOf `GroundZero.Types.Id do return none
  let p := hTy.appFn!.appArg!
  let q := hTy.appArg!
  let pTy ← inferType p
  unless pTy.isAppOf `GroundZero.Types.Id do return none
  let a := pTy.appFn!.appArg!
  let b := pTy.appArg!
  let A ← inferType a
  let u := idLevel hTy
  let c ← mkFreshExprMVar A
  let r₀ ← mkFreshExprMVar (mkAppN (mkConst `GroundZero.Types.Id [u]) #[A, b, c])
  let e := mkAppN (mkConst `GroundZero.Types.Whiskering.rwhs [u]) #[A, a, b, c, p, q, h, r₀]
  let ty ← inferType e
  pure (ty.appFn!.appArg!, e)

/-- Build `lwhs q₀ h : q₀ ⬝ p = q₀ ⬝ q` from a 2-path `h : p = q` (left
    whisker), with q₀ a fresh path.  Returns (lhs, proof). -/
def lwhsProof (h : Expr) : MetaM (Option (Expr × Expr)) := do
  let hTy ← inferType h
  unless hTy.isAppOf `GroundZero.Types.Id do return none
  let p := hTy.appFn!.appArg!
  let q := hTy.appArg!
  let pTy ← inferType p
  unless pTy.isAppOf `GroundZero.Types.Id do return none
  let a := pTy.appFn!.appArg!
  let b := pTy.appArg!
  let A ← inferType a
  let u := idLevel hTy
  let a₁ ← mkFreshExprMVar A
  let q₀ ← mkFreshExprMVar (mkAppN (mkConst `GroundZero.Types.Id [u]) #[A, a₁, a])
  let e := mkAppN (mkConst `GroundZero.Types.Whiskering.lwhs [u]) #[A, a₁, a, b, p, q, q₀, h]
  let ty ← inferType e
  pure (ty.appFn!.appArg!, e)

/-- Whiskering rewrites derived from a context 2-path hypothesis `h : p = q`
    (i.e. p, q are themselves paths).  Uses the library whiskering lemmas
    `rwhs`/`lwhs` (GroundZero.Types.Whiskering):
      rwhs h r₀ : p ⬝ r₀ = q ⬝ r₀   — right whisker: `p ⬝ r ↦ q ⬝ r`
      lwhs q₀ h : q₀ ⬝ p = q₀ ⬝ q   — left whisker:  `r ⬝ p ↦ r ⬝ q`
    Returns (lhs, proof, flip) triples, exactly like the name-based rules, so
    stepRule can use them.  Hypotheses that are not 2-paths are skipped. -/
def whiskerRulesOf (h : Expr) : MetaM (List (Expr × Expr × Bool)) := do
  let mut out := []
  if let some (lhs, e) := (← rwhsProof h) then
    let ty ← inferType e
    out := out ++ [(lhs, e, false), (ty.appArg!, e, true)]
  if let some (lhs, e) := (← lwhsProof h) then
    let ty ← inferType e
    out := out ++ [(lhs, e, false), (ty.appArg!, e, true)]
  pure out

/-- All whiskering rules derivable from the Id-typed hypotheses of g's context. -/
def hypRules (g : MVarId) : MetaM (List (Expr × Expr × Bool)) := do
  let mut out := []
  for ldecl in (← g.getDecl).lctx do
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOf `GroundZero.Types.Id then
      out := out ++ (← whiskerRulesOf ldecl.toExpr)
  pure out

end PathSimp

elab "path_simp" : tactic => do
  -- (1) rewrite loop: right-associate, cancel p ⬝ p⁻¹ / p⁻¹ ⬝ p, drop idp,
  --     push inverses in; the visited set prevents assoc ping-pong.
  Elab.Tactic.liftMetaTactic (λ mvar => do
    let mut gs : List MVarId := [mvar]
    -- visited types are kept UNREDUCED: whnf'ing them reduces the whiskering
    -- defs to rid-soups, which is both expensive and defeats loop detection
    -- (the raw type is the stable canonical form).
    let mut visited : List Expr := [← instantiateMVars (← mvar.getType)]
    for _ in [:64] do
      let mut appliedAny := false
      let mut next : List MVarId := []
      for g in gs do
        let mut applied := false
        for (nm, rev) in PathSimp.pathRules do
          let s ← saveState
          let (lhs₀, heq₀) ← PathSimp.buildRule nm
          let r ←
            if rev then
              let ty₀ ← inferType heq₀
              PathSimp.stepRule g ty₀.appArg! heq₀ true visited
            else
              PathSimp.stepRule g lhs₀ heq₀ false visited
          match r with
          | some (g', t') =>
              next := next ++ [g']; visited := visited ++ [t']
              applied := true; break
          | none => restoreState s
        -- whiskering: rewrite using 2-path hypotheses from the context (⬝ₗ / ⬝ᵣ)
        for (lhs₀, heq₀, flip) in (← PathSimp.hypRules g) do
          if applied then break
          let s ← saveState
          let r ← PathSimp.stepRule g lhs₀ heq₀ flip visited
          match r with
          | some (g', t') =>
              next := next ++ [g']; visited := visited ++ [t']
              applied := true
          | none => restoreState s
        if not applied then next := next ++ [g]
        appliedAny := appliedAny || applied
      gs := next
      if not appliedAny then break
    pure gs)
  -- (2) close residuals with reflexivity; FAIL if any remain (so that
  --     `first | path_simp | …` can fall through on non-path goals).
  let gs ← getGoals
  let mut rem := []
  for g in gs do
    let s ← saveState
    setGoals [g]   -- reflexivity targets the main goal; make g the main goal
    try
      evalTactic (← `(tactic| reflexivity))
    catch _ =>
      restoreState s
      rem := rem ++ [g]
  setGoals rem
  if !rem.isEmpty then throwError "path_simp: unsolved goals"

end GroundZero.Meta.Tactic
