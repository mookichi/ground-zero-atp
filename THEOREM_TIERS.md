# Ground Zero: Theorem Tiers for Automated Theorem Provers

This document classifies the theorems of the
[Ground Zero](https://github.com/rzrn/ground_zero) HoTT library into tiers, so
that an automated theorem prover (or AI-assisted proof engineer) can decide
*what to try first* when facing a goal.  It complements
[`AIPROVER.md`](AIPROVER.md), which explains *how* to write hott proofs; this
file says *which* theorems exist and in what order to reach for them.

The classification was generated from a full inventory of the library
(~3,100 declarations across 107 files).  Names are grouped by the module
they live in; file paths are relative to the repository root and double as the
`lake build` target names (see `AIPROVER.md` §8).

## How to use

1. Match the goal against **Tier 1** first.  These are the primitives and the
   lemmas that every proof needs; they have no dependencies beyond
   `Proto`, `Types`, `Structures`, and the two foundational theories
   (function extensionality, univalence).  If a Tier 1 name applies, use it.
2. If Tier 1 does not close the goal, look in **Tier 2** (standard derived
   lemmas — transport algebra, path algebra, equivalence algebra, h-level
   closure, natural-number arithmetic).
3. **Tier 3** only matters when the goal mentions a specific HIT or type
   construction (circle, suspension, truncation, quotient, …): use that
   type's eliminators and its theorems.
4. **Tier 4** is domain-specific (algebra structures, modal logic, kernel
   learning).  Consult it only when the goal lives in that domain.
5. If the goal mentions a *name* from `Appendix A`, remember it is an axiom —
   it cannot be `unfold`ed, only applied.

## Tier 1 — Foundational core (try first, always available)

### 1.1 Primitives — `GroundZero/Proto.lean`
`idfun`, `Iff` (`Iff.left`, `Iff.right`, `Iff.refl`, `Iff.symm`, `Iff.comp`),
`Bool.elim`, `explode` (ex falso — an axiom), `Identity.elim`, `Identity.lift`,
`Identity.lift₂`.

### 1.2 Identity type — `GroundZero/Types/Id.lean`
`refl`, `trans` (`⬝`), `inv` (`⁻¹`), `symm`, `ap`, `assoc`, `lid`, `rid`,
`compInv`, `invComp`, `invInv`, `mapInv`, `compUniq`, `invInj`, `compReflIfEq`,
`transCancelLeft`, `transCancelRight`, `reflTwice`.

### 1.3 Transport, pathovers, equivalences — `GroundZero/Types/Equiv.lean`
* Transport: `transport`, `transportconst`, `transportImpl`, `subst`,
  `transportOverConstFamily`.
* Equivalence primitives: `ideqv`, `idtoeqv`, `idtoiff`, `intro`, `qinv`,
  `ishae`, `isQinv`, `biinv`, `toBiinv`, `ofBiinv`, `forward`, `forwardLeft`,
  `forwardRight`, `left`, `right`, `leftForward`, `rightForward`, `linv`,
  `rinv`, `linvInv`, `rinvInv`, `idtoeqvLinv`, `idtoeqvRinv`, `eqvInj`,
  `eqvLeftInj`, `eqvRightInj`, `identityEqv`, `idmap`, `inveqv`, `revEquiv`.
* Homotopies: `Homotopy` (+ `Homotopy.Id`, `Homotopy.symm`, `Homotopy.trans`),
  `happly`, `happlyEqv`.
* Dependent application and pathovers: `apd`, `apd₂`, `apdOverConstantFamily`,
  `mapOverComp`, `mapFunctoriality`, `pathoverOfEq`, `pathoverOfEqInj`,
  `pathoverFromTrans`, `pathoverInv`, `reflPathover`.

### 1.4 Type formers — `Sigma`, `Product`, `Coproduct`, `Unit`
* `GroundZero/Types/Sigma.lean`: `pr₁`, `pr₂`, `prod` (pairing),
  `eqOfSigmaEq`, `sigmaEqOfEq`, `prodEq`, `uniq` (η), `assoc` (Σ-結合),
  `comm` (ΣΣ 交換), `prodSigmaDistrib` (× の Σ 分配),
  `piSigmaSwap` (`(Π a, Σ b, P a b) ≃ Σ f, Π a, P a (f a)`, funext 必要).
* `GroundZero/Types/Product.lean`: `prod`, `apFst`, `apSnd`, `ind`, `elim`,
  `uniq`, `eqOfProdEq`, `assoc` (×-結合).
* `GroundZero/Types/Coproduct.lean`: `inl`, `inr`, `elim`, `pathSum`,
  `inlInl`-style disjointness (`inlInr`, `inrInl`), `symm`, `inv`, `assoc`
  (+-結合), `sumEmpty` (`A + 𝟎 ≃ A`), `emptySum` (`𝟎 + A ≃ A`).
* `GroundZero/Types/Unit.lean`: `elim`, `ind`, `uniq`.

  (`Product.assoc` / `Coproduct.assoc` are declared in
  `GroundZero/Algebra/Group/Finite.lean` and re-exported through the root;
  `Sigma.comm` is the dependent ΣΣ swap, `piSigmaSwap` is the
  type-theoretic axiom of choice.)

### 1.5 Function extensionality — `GroundZero/Structures.lean`,
`GroundZero/Theorems/Funext.lean`, `GroundZero/HITs/Interval.lean`
`funext`, `happly`, `mapHapply`, `happlyFunext`, `funextHapply`, `homotopy`,
`happlyCom`, `happlyRev`.  The weak version is `naive`; the induction
principle behind it is `homotopyInd` with `isContrSigmaHomotopy`.  (The
interval HIT `I` and its `ind`/`rec`/β-rules are postulated in
`Theorems/Funext.lean` — see Appendix A.)

### 1.6 Univalence — `GroundZero/Theorems/Univalence.lean`
`univalence`, `ua`, `uaβ`, `uaCompRule`, `uaidp`, `idtoeqvua`, `uaidtoeqv`,
`uaε`, `uaidtoeqvε`.  (The weak form `uaweak`/`uaweakβ` is the postulate;
everything else is derived.)

### 1.7 Propositions and h-levels — `GroundZero/Structures.lean`
* Props: `prop`, `isProp`, `contrIsProp`, `propIsProp`, `propIsSet`,
  `propset`, `autoContr`, `singl`, `implProp`, `piProp`, `piHset`,
  `piRespectsNType`,
  `productProp`, `prodHset`, `sigProp`, `propSum`,
  `emptyIsProp`, `emptyIsSet`, `unitIsProp`, `unitIsSet`, `unitIsContr`,
  `contrEquivUnit`, `unitProdEquiv`, `prodUnitEquiv`, `terminalArrow`,
  `familyOverUnit`, `functionToContr`.
* H-levels: `hset`, `hsetLoop`, `hlevel`, `isTruncated`, `nType`,
  `ntypeIsProp`, `ofNat`, `isLoop`, `isNType`.

### 1.8 Natural numbers, core — `GroundZero/Theorems/Nat.lean`
`zeroPlus`, `succPlus`, `oneMul`, `mulOne`, `succMul`, `mulSucc`, `mulComm`,
`assoc`, `distribLeft`, `distribRight`, `zeroMul`, `mulZero`, `mulAssoc`,
`plusDiag`, `succInj`; the
order `le` with `le.trans`, `le.succ`, `le.step`, `le.leSucc`, `le.prop`,
`le.asymm`, `le.dec`, `le.elim`.

## Tier 2 — Standard derived lemmas (the normal toolbox)

Reach for these when Tier 1 does not close the goal directly.

* **Path algebra** (`GroundZero/Types/Id.lean`): `ap2`, `ap3`, `ap4`, `apΩ`,
  `idΩ`, `Loop`, `loop₁`, `loop₂`, `horizontalComp₁`, `horizontalComp₂`,
  `«Eckmann–Hilton»`, `UIP`, `cancelCompInv`, `cancelInvComp`,
  `eqIfCompRefl`, `explodeInv`, `invEqIfEqInv`, `eqEnvIfInvEq`, `JSymm`,
  `J₁`, `J₂`, `lwhs`, `rwhs`, `comm`, `univ`, `Neq`, `Not`, `Pointed`,
  `Pointed.Map`, `pointOf`.
* **Transport family** (`GroundZero/Types/Equiv.lean`): `transportOverPi`,
  `transportOverProduct`, `transportOverSig`, `transportOverFunction`,
  `transportOverFunctor`, `transportOverHmtpy`, `transportOverFamily`,
  `transportOverMorphism` (+ `transportOverMorphismPointwise`),
  `transportOverOperation` (+ `transportOverOperationPointwise`),
  `transportOverInvolution`, `transportOverContrMap`,
  `transportOverInvContrMap`, `transportComposition`,
  `transportCompositionRev`, `transportComp`, `transportInvCompComp`,
  `transportBackAndForward`, `transportForwardAndBack`, `transportSquare`,
  `transportBimap₁`, `transportBimap₂`, `transportDiag₁`, `transportDiag₂`,
  `transportCharacterization`, `transportToTransportconst`,
  `transportconstOverComposition`.
* **Equivalence algebra** (`GroundZero/Types/Equiv.lean`): `bimap`,
  `bimapBicom`, `bimapComp`, `bimapInv`, `bimapReflLeft`, `bimapReflRight`,
  `eqvEqEqv`, `apEquivOnEquiv`, `apLeftOnEquiv`, `apRightOnEquiv`,
  `cancelLeftEquiv`, `cancelRightEquiv`, `biinvTrans`, `apBiinvOfBiinv`,
  `apQinvOfQinv`.  (The structured-type equivalences — `contrTypeEquiv`,
  `zeroEquiv`, `sumEquiv`, `prodEquiv`, `sumBiinv`, `prodBiinv` — live in
  `GroundZero/Structures.lean`, and `propEquiv` in
  `GroundZero/Theorems/Equiv.lean`.)
* **Pathover machinery** (`GroundZero/Types/Equiv.lean`): `pathUnderAp`,
  `pathOverAp`, `pathOverApCoh`, `depPath`, `depPathMap`, `depPath.refl`,
  `depPathTransSymm`, `depPathTransSymmCoh`, `depSymm`, `depTrans`,
  `mapOverAS`, `mapWithHomotopy`, `apComHmtpy`, `apdComHmtpy`,
  `apdFunctoriality`, `apdOverComp`, `mapFunctoriality₃`, `mapFunctoriality₄`,
  `mapFunctoriality₅`.
* **Ω (loop-space) algebra** (`GroundZero/Types/Equiv.lean` +
  `GroundZero/Structures.lean`): `apΩ`, `apdΩ`, `comΩ`, `biapdΩ`,
  `comBiapdΩ`, `apConjugateΩ`, `conjugateΩ`, `conjugateIdΩ`,
  `conjugateRevΩ`, `conjugateTransΩ`, `conjugateOverΩ`,
  `conjugateRewriteΩ`, `conjugateRewriteInvΩ`, `cancelDoubleConjLeftLeft`,
  `cancelHigherConjLeft`, `comDistribΩ`, `idOverΩ`, `idrevΩ`, `inΩ`, `outΩ`,
  `inOverΩ`, `outOverΩ`, `overApΩ`, `underApΩ`, `fillΩ`, `fillHaeΩ`,
  `fillConjugateΩ`, `fillConjugateRevΩ`, `lidΩ`, `ridΩ`,
  `revΩ`, `revlΩ`, `revrΩ`, `revConjugateΩ`, `altDefΩ`, `altDefIdΩ`,
  `altDefOverΩ`, `assocΩ`, `abelianComΩ`, `prodΩ`, `sigmaProdΩ`.
* **Type-former extras**: `Sigma.map`, `Sigma.gen`, `Sigma.assoc`, `Sigma.Ind`,
  `Sigma.mapFstOverProd`, `Sigma.mapSndOverProd`, `Sigma.apOverSigma`,
  `Sigma.sigmaPath`, `Sigma.prodRepr`, `Sigma.reprProd`, `Sigma.prodComp`,
  `Sigma.prodRefl`, `Sigma.respectsEquiv`, `Sigma.sigmaEmpty`,
  `Sigma.sigmaSumDistrib` (moved here from `HITs/Circle.lean`);
  `Product.mapProd`, `Product.bimap`, `Product.swap`, `Product.comm`,
  `Product.emptyProd`, `Product.prodEmpty`, `Product.piEmpty`,
  `Product.piProdDistrib`; `Coproduct.bimap`, `Coproduct.code`,
  `Coproduct.inl.decode`/`Coproduct.inr.decode`,
  `Coproduct.inl.encode`/`Coproduct.inr.encode`,
  `Coproduct.inl.decodeEncode`/`Coproduct.inr.decodeEncode`,
  `Coproduct.inl.encodeDecode`/`Coproduct.inr.encodeDecode`,
  `Coproduct.inl.recognize`/`Coproduct.inr.recognize`, `Coproduct.inv`,
  `Coproduct.prodSumDistrib`, `Coproduct.sumProdDistrib`,
  `Coproduct.respectsEquivLeft` (moved here from
  `Algebra/Group/Finite.lean`).
* **h-level closure and decidability** (`GroundZero/Structures.lean`):
  `dec`, `decEq`, `Hedberg`, `boolDecEq`, `boolEqTotal`, `boolIsSet`,
  `eqrel` family (`eqrel.apply`, `eqrel.eq`, `eqrel.iseqv`, `eqrel.prop`,
  `eqrel.refl`, `eqrel.rel`, `eqrel.symm`, `eqrel.trans`), `iseqrel`,
  `issymm`, `istrans`, `isrefl`, `induced`, `hrel`, `hlevel.cumulative`,
  `hlevel.strongCumulative`, `ntypeRespectsEquiv`, `ntypeRespectsProd`,
  `ntypeRespectsSigma`, `propRespectsEquiv`, `hsetRespectsEquiv`,
  `hsetRespectsSigma`, `contrRespectsEquiv`, `contrRespectsSigma`,
  `contrRetract`, `loopOverHSet`, `loopOverNType`, `loopOverProp`,
  `loopPropNType`, `levelOverΩ`,  `levelStableΩ`, `mapToHapply`, `mapToHapply₂`, `mapToHapply₃`,
  `mapToHapply₄`, `happlyFunextPt`, `funextΩ`, `happlyFunextΩ`,
  `funextHapplyΩ`, `equivFunext`, `hcommSquare`, `propEM`, `propEquivLemma`,
  `propIffLemma`, `doubleNegEq`, `DNEGprop`, `DNEGinf`, `lemContr`, `LEMprop`,
  `LEMinf`, `lemToDoubleNeg`, `notIsProp`, `neqBoolToEqNot`, `Squash`
  family, `vect` family, `pullback`, `pullbackSquare`, `isPullback`.
* **Equivalence characterizations** (`GroundZero/Theorems/Equiv.lean`):
  `biinvProp`, `compQinv₁`, `compQinv₂`, `qinvImplsIshae`, `ishaeImplContrFib`,
  `corrOfQinv`, `qinvOfCorr`, `corrRev`, `hsetEquiv`, `pathOver`,
  `pathOverCharacterization`, `symmQinv`, `symmSymmIdfun`, `propEquiv`,
  `propFromEquiv`, `propEquivProp`, `equivHmtpyLem`, `hmtpyRewrite`,
  `contrFamily`, `contrQinvFib`, `contrToType`, `typeToContr`,
  `lemContrEquiv`, `lemContrInv`, `linvContr`, `rinvContr`, `productContr`,
  `equivNType₁`, `equivNType₂`, `equivInvEquiv`, `fibEq`, `respectsEquivOverFst`,
  `uniqDoesNotAddNewPaths`, `eqvAssoc` (associativity of `Equiv.trans`).
* **Functions** (`GroundZero/Theorems/Functions.lean`): `injective`,
  `surjective`, `isEmbedding`, `Embedding`, `Surjection`, `eqvMapForward`,
  `fibInh`, `isConnected`, `cut`, `cutIsSurj`, `propSigmaEmbedding`,
  `propSigmaEquiv`, `sigmaPropEq`, `ntypeOverEmbedding`, `Ran` family
  (`Ran.incl`, `Ran.subset`, `ranConst`, `ranConstEqv`, `surjImplRanEqv`).
* **Classical** (`GroundZero/Theorems/Classical.lean`): `lem`, `dneg`,
  `dneg.decode`, `dneg.encode`, `Contrapos` family (`Contrapos.intro`,
  `Contrapos.elim`, `Contrapos.eq`), `choiceOfRel`, `cartesian`, `inh`.
* **Natural numbers, extended** (`GroundZero/Theorems/Nat.lean`): `min`,
  `max`, `dist` families (`.refl`, `.symm`, `.trans`, `.le`, `.addl`,
  `.addr`, `.translation`, `.zeroLeft`, `.zeroRight`, `.succLeft`,
  `.identity`, `.max`, `.min`), the full `le` family (`le.addl`, `le.addr`,
  `le.map`, `le.max`, `le.min`, `le.ofNotLe`, `le.neqSucc`, `le.neSucc`),
  `stdLe*` (`stdLeOf`, `stdLePred`, `stdLeRev`, `stdLeTrans`, `stdLeZero`,
  `stdNoLeOneZero`, `stdNoLeSucc`), `decideEqTrue`, `decideEqFalse`,
  `ofDecideEqTrue`, `natDecEq`, `natDecLE`, `natIsSet'`, `trueNeqFalse`,
  `isEven`, `isOdd`, `iso`.

## Tier 3 — Type-construction and HIT theorems

Use only when the goal mentions the type.  Each HIT module exports the
eliminator (`ind`, with `[induction_eliminator]`), the recursion principle
(`rec`), the point/glue constructors, and the β-rules (`indβrule`,
`recβrule`); those are always the first things to try for goals over that
type.

* **Quotients**: `GroundZero/HITs/Quotient.lean` (`Quotient`, `elem`, `ind`,
  `rec`), `GroundZero/HITs/Setquot.lean` (`Setquot`, `Relquot` + their
  `ind`/`indProp`/`lift₂`/`rec`/`sound`/`set`), `GroundZero/Types/Setquot.lean`
  (`setquot`, `setquot.elem`, `setquot.sound`, `setquot.set`, `iseqclass`).
* **Pushout-shaped HITs**: `GroundZero/HITs/Pushout.lean` (`Pushout`, `inl`,
  `inr`, `glue`), `GroundZero/HITs/Coequalizer.lean` (`Coeq`, `iota`, `resp`),
  `GroundZero/HITs/Wedge.lean` (`Wedge`), `GroundZero/HITs/Join.lean`
  (`Join`, `inl`, `inr`, `glue`, `toSusp`, `fromSusp`),
  `GroundZero/HITs/Suspension.lean` (`Suspension`, `north`, `south`,
  `merid`, `suspIdΩ`, `suspMultΩ`, `suspRevΩ`),
  `GroundZero/HITs/Colimit.lean` (`Colimit`, `incl`, `glue`),
  `GroundZero/HITs/Flattening.lean` (`Flattening`, `iota`, `sec`),
  `GroundZero/HITs/Generalized.lean` (`Generalized`, `glue`).
* **Spheres and the circle**: `GroundZero/HITs/Circle.lean` (the largest HIT
  module: `base`, `loop`, `ind`, `rec`, `winding`, `fundamentalGroup`,
  `mapExt`, `degree`, `helix`, `rot`, `mul`/`mult`, `powerComm`/`windPower`
  families, `Torus`/`t`), `GroundZero/HITs/Sphere.lean` (`base`, `surf`,
  `loopSphere`, `mapExtΩ`, `cup`, `code`/`decode`/`encode`).
* **Truncation and mere propositions**: `GroundZero/HITs/Trunc.lean`
  (`Trunc`, `nthTrunc`, `elem`, `ind`, `rec`, `ap₂`, `setEquiv`,
  `respectsEquiv`), `GroundZero/HITs/Merely.lean` (`Merely`, `elem`, `ind`,
  `lift`, `rec`, `uniq`, `incl`, `congClose`, `equivIffTrunc`).
* **Intervals, integers, reals, Möbius**: `GroundZero/HITs/Interval.lean`
  (`intervalContr`, `intervalProp`, `mapExt`, `twist`, `transportOverSeg`),
  `GroundZero/HITs/Int.lean` (`Int`, `mk`, `glue`, `ind`, `rec`, `add`, `mul`,
  `neg`, `pos`), `GroundZero/HITs/Reals.lean` (`R`, `Reals`, `elem`, `ind`,
  `rec`, `Euler`, `cis`, `vect`, `center`, `fibOfHomo`, `kerOfHomo`,
  `helixOverCis`), `GroundZero/HITs/Moebius.lean` (`M`, `moebius`, `C`,
  `cylEqv`).
* **Symmetry quotient**: `GroundZero/HITs/Unordered.lean` (`UnorderedTriple`,
  `elem`, `resp12`, `resp23`, `ind`, `rec`, `prod3UP`,
  `prod3UPRespects12/23`).
* **W-types and encodings**: `GroundZero/Types/W.lean` (`W`, `WAlg`, `Wh`,
  `Wd`, `Ws`, `ind₂`, `propDecode`/`propEncode`/`propEquivSig`),
  `GroundZero/Types/Nat.lean` (`code`, `encode`, `decode`, `encodeDecode`,
  `decodeEncode`, `equivAddition`, `natUnitEqv`).
* **Topology theorems**: `GroundZero/Theorems/Hopf.lean` (`family`,
  `total`, `μLoop`), `GroundZero/Theorems/Fibration.lean` (`Fibration`,
  `fiberOver`, `hasLifting`, `lifting`), `GroundZero/Theorems/Connectedness.lean`
  (`connImplQinv`, `connImplTerminalConn`, `indTrunc`, `isProp`),
  `GroundZero/Theorems/Pullback.lean` (`pullbackCorner`, `terminalPullback`),
  `GroundZero/Theorems/Weak.lean` (coherence: `Coh`, `Con`, `Ref`).
* **Cubical**: `GroundZero/Cubical/Path.lean` (`Path`, `PathP`, `coerce`,
  `coe`, `funext`, `homotopyEquality`, `idtoeqv`, `eta`, `singl`, `J`),
  `GroundZero/Cubical/V.lean` (`V`, `iso`, `ua`, `uabeta`,
  `univalence.elim`), `GroundZero/Cubical/Cubes.lean`, `Connection.lean`,
  `Example.lean`.

## Tier 4 — Domain-specific applications

Consult only when the goal lives in that domain.

* **Algebra structures** (`GroundZero/Algebra/`): `Basic.lean` (magma,
  pregroup, monoid, `isAbelian`, `isGroup`, `Alg`, `Iso`, `Hom`),
  `Ring.lean` (`ring` axioms: `addAssoc`, `addComm`, `mulAssoc`, `mulComm`,
  `distribLeft/Right`, `ring.mulZero`, `ring.mulNeg`, …), `Reals.lean`
  (ℝ: `exp`, `expAdd`, `expZero`, `expSeries`, `infiniteSum`, `negAdd`,
  `R.orfield`, `R.hasInv`; series tooling `rpow`/`fac`/`rdiv`; the
  sup/lim theory — `R.complete`/`R.cocomplete`, `sup`/`inf`
  (+`sup.lawful`/`sup.exact`/`inf.lawful`/`inf.exact`), `tendsto`,
  `continuous`, the `abs` family, and the metric structure
  `Metric`/`metric`/`triangle`), `Euclidean.lean` (Euclidean domain: `dvd`,
  `gcd`, `divEq`, `strongRec`), `Orgraph.lean`, `Boolean.lean`,
  `Category.lean`, `Geometry.lean`, `EilenbergMacLane.lean` (`K1`, `KΩ`,
  `code`/`decode`/`encode`, `univ`), `Transformational.lean` (reflections:
  `π`, `ρ`, `τ`, `ι`, `octave`).
* **Group theory** (`GroundZero/Algebra/Group/`): `Basic.lean` (104 decls:
  `cancelLeft/Right`, `invInv`, `conjugate` family, `commutes`,
  `subgroup`, `mkiso`, `Z₁`, `Z₂`), `Factor.lean` (`Factor`, `univFactor`),
  `Subgroup.lean`, `Presentation.lean`, `Free.lean`, `Homotopy.lean`,
  `Symmetric.lean`, `Alternating.lean`, `Periodic.lean`, `Differential.lean`,
  `Automorphism.lean`, `Product.lean`, `Semidirect.lean`, `Z.lean`.
* **Modal logic** (`GroundZero/Modal/`): `Disc.lean` (`Disc`, `discBundle`,
  `infinitesimallyClose`, `Homogeneous`), `Infinitesimal.lean` (`Im`, `ι`,
  `κ`, `μ`, `isCoreduced`), `Etale.lean` (`EtaleMap`, `isManifold`,
  `Manifold`).
* **Category theory** (`GroundZero/Types/`): `Precategory.lean`
  (`iso`, `idtoiso`, `isProduct`, `isCoproduct`, `isFaithful`, `isFull`,
  `isGroupoidIfUnivalent`, `univalent`, `Functor.com`, `Natural.horiz`),
  `Category.lean` (`Category`, `isotoid`, `twoOutOfThree`,
  `ofIdtoiso`, `ofIsotoid`), `CellComplex.lean` (`FdCC`, `Model`).
* **Sets and the universe** (`GroundZero/Types/`): `Ens.lean`
  (`Ens`, `Ens.ext`, `Ens.inter`, `Ens.union`, `Ens.image`,
  `Ens.singleton`, …), `Integer.lean` (ℤ = ℕ+ℕ arithmetic: `add`,
  `sub`, `mul`, `negate`, `pred`, `succ`, `sgn`, `abs`, …), `HEq.lean`.
* **Symmetry typeclasses** (`GroundZero/Meta/Symm.lean`,
  `GroundZero/Meta/Tactic.lean`): `IsSymmetric`, `IsSymmInvariant`,
  `cycle123`, `cycle132`, `reverse`, and the `symm` tactic (see `AIPROVER.md`
  §7).
* **Kernel learning** (repository root): `PosDef.lean` (`biForm`,
  `biFormSymI`, `biFormSwapInner`, `sumSwap`, `sumZero`, `gaussPsdD`
  (the exp-world `gaussPsd` was retired in 追記評価14), `taylorPsd`,
  `polyKernelPsd`, `PSD`, `quadForm`, `psdRankOne`, `normSq`/`normSqConvex`,
  `conv`, `convAdd`, …; the D-world chain — `expD`, `expDSeries`,
  `expAddD`, `expTripleD`, `gaussDecompD`, `expMidD`, `gaussKernelD`,
  `gaussKernelDSeries`, `gaussPsdD` — built on the series axioms
  `infSumNonneg`/`infSumIsLim`/`mertens`/`convExpD`/`convAbsExpD`
  with derivatives `infSumLinD`, `cauchyProductLim`, `infSumFinSwapConv`,
  `infSumZeroLim`, `convAddFin`, `sumSwapInfConv`; `expEqExpD` is the
  exp/D connection lemma; the factorial-normalized binomial theorem
  `nCr`/`nCrFac`/`binomTaylor`/`binomTaylorPw` — the basis for `expAddD`),
  `BinomTaylor.lean` (D-world supporting lemmas: `expZeroD` — basis for
  `kernelCenter`'s `{infSumIsLim}` dependency — plus `expPartialSumOne`/
  `convPartialSumOne` (convergence of exp's partial sums) and `facGePowTwo`),
  `KernelLearn.lean` (`gram`, `gramSym`, `gramNonneg`,
  `gramRbfNonneg`, `rbfPsd`, `gramRbfSym`, `kernelCenter`, the
  `polyKernel`/`polyGram` families, `gaussSymmD`, `rbfGaussSymmD`,
  `gaussianRbfD_eq_gaussKernelD`, `representer`, `representerEval`,
  `representerAsFeatures`, `featureMap`, `gaussEqShift`,
  `representerShiftInvariant`, `gaussianRbfDShiftInvariant`,
  `dualLossConvex`, `dualObjective`, …), `RBF.lean` (`rbf`,
  `gaussianRbf`, `gaussKernel`, `gaussianRbfShiftInvariant`,
  `gaussianRbfShiftEquivariant`, `gaussianRbfCenter`, `gaussKernelD`/
  `gaussianRbfD` (D-world), `gaussKernelMul`, `expKernel`,
  `rbfShiftInvariant`, …), `KernelUniversal.lean` (`bump`, `bumpCenter`,
  `bumpSymm`, `bumpNonneg`, `bumpProduct`, `bumpSum`, `bumpSumMulClosed`,
  `windowApprox`, `continuousFun`, `universalKernel`, `gaussianUniversal`,
  `stoneWeierstrassGauss`, …).
* **Exercises** (`GroundZero/Exercises/Chap1.lean`–`Chap6.lean`): solved
  HoTT-book exercises.  They are imported by the root module and their
  theorems are *available*, but treat them as worked examples and practice
  material (indexed in `GroundZero/Exercises/README.md`), not as part of the
  library's API contract.  `Sample.lean` at the root is a demo file.

## Appendix A — Axioms at a glance

The following are postulates (`hott axiom` or `hott opaque axiom`): they have
no body to compute with, so `unfold`/defeq will not see through them, and
statements mentioning them must apply them explicitly (`AIPROVER.md` §2, §6).
Everything else in the library is transparent and definitionally reducible.

| Module | Axioms |
|---|---|
| `GroundZero/Proto.lean` | `explode` (ex falso) |
| `GroundZero/Theorems/Funext.lean` | the interval HIT: `I`, `i₀`, `i₁`, `ofBool`, `ind`, `rec`, `recβrule`, `recβruleRev` — `funext` itself is *derived* from these |
| `GroundZero/Theorems/Univalence.lean` | `uaweak`, `uaweakβ` (weak univalence) — `ua` and `univalence` are *derived* |
| `GroundZero/Theorems/Nat.lean` | `Leibnitz` |
| `GroundZero/HITs/Quotient.lean` | `Quotient`, `elem`, `ind`, `rec`, opaque `line`, `indβrule`, `recβrule`, `grpd`, `uniq` |
| `GroundZero/HITs/Trunc.lean` | `Trunc`, `elem`, `ind`, `rec`, opaque `seg`, `indβrule`, `recβrule` |
| `GroundZero/Algebra/Reals.lean` | the ℝ exponential: `exp`, `expZero`, `expAdd`, `expSeries`, `infiniteSum`, `infiniteSum.ext` (and the ℝ field laws in `R.orfield`) |
| `GroundZero/Algebra/EilenbergMacLane.lean` | `K1`, `base`, `loop`, `loop.mul` |
| `GroundZero/Modal/Infinitesimal.lean` | `Im`, `Im.ind`, `ι`, `κ`, `μ` |
| `PosDef.lean` (repository root) | `infSumNonneg`, `infSumIsLim`, `mertens`, `convExpD`, `convAbsExpD` — the series axioms of the Gaussian-kernel PSD proof (`infSumLin` was an axiom in the pre-追記評価14 era (introduced around 追記評価10–11) and was absorbed/retired in 追記評価14; `infSumFinSwapConv`/`infSumZeroLim`/`infSumLinD` are theorems from `{infSumIsLim}`, `cauchyProductLim` from `{infSumIsLim, mertens}`) |
| `RBF.lean` (repository root) | `expMonotone` (moved here from `KernelLearn` in 追記評価19; the exp-world Gaussian-kernel theory — `gaussSymm`, `kernelPos`, `kernelLeOne`, `rbfGaussEq`, … — lives in this module) |
| `KernelLearn.lean` (repository root) | *(no axioms — the gram/representer systems are D-world (expD-based) and exp-free)* |
| `KernelUniversal.lean` (repository root) | `stoneWeierstrassGauss` (`0 < a → universalKernel a`) |

## Appendix B — Maintenance convention

This is a *living* catalog.  Whenever a session adds a new module or a notable
theorem to the library, it should update the tier lists (or at minimum the
module-level entries of Tiers 3–4 and the axiom table).  The tiers were
assigned by dependency depth and by how often a generic ATP goal needs the
theorem — keep that criterion in mind when classifying new results.

*Last updated:* 2026-08-12 (Appendix A: reconciled with the 追記評価17–20
measurements — PosDef axioms are `infSumNonneg`/`infSumIsLim`/`mertens`/
`convExpD`/`convAbsExpD` (`infSumLin` retired in 追記評価14); `expMonotone`
moved to `RBF.lean` in 追記評価19, so `KernelLearn` has no axioms;
`KernelUniversal.stoneWeierstrassGauss` unchanged.  Tier 1–4 lists:
reconciled against the live declaration inventory — retired/renamed names
updated (`transportOverSig`, `equivNType₁/₂`, `doubleNegEq`, `mkiso`,
`powerComm`, `sigProp`), `lwhsΩ`/`rwhsΩ` dropped (only homotopy versions
exist), and the Coproduct encode–decode family qualified to `inl`/`inr`;
Tier 4 gained the previously missing modules and families — `BinomTaylor.lean`,
the PosDef D-world chain (`expD`/`gaussPsdD`/`convExpD`/…), the Reals
sup/lim/Metric theory, and the D-world kernel entries in `KernelLearn`/`RBF`.).
Built from a full declaration inventory of the library and a grep of all
`hott axiom`/`hott opaque axiom` postulates.
