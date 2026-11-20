import SGPT.Projective.BDivOriginalCartierPrimeCodimension
import SGPT.BDivisor.BD7NumericalTransitions
import SGPT.Okounkov.SchemeNativeBirationalPrimeCycleClassification

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set SGPT.Okounkov
open SGPT.Projective.BDivNov16 SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy CanonicalCurrentFrame TopologicalSpace
open scoped Topology Manifold ContDiff

local instance primeTopology {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance primeCharts {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance primeManifold {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

section Model

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) {m : ℕ} [SmoothOfRelativeDimension (m+1) f]
  [IsSeparated f] [QuasiCompact f]

/-- The native prime attached to the actual algebraic codimension-one point. -/
def nativePrimeOfOriginalPoint (x : {x : X // Order.coheight x = 1}) :
    SGPT.PSH.GeometricPrimeCarrier (m+1) (SchemeComplexPoint f) :=
  (exists_nativePrime_of_original_codimOne f m E x.property).choose

theorem nativePrimeOfOriginalPoint_val (x : {x : X // Order.coheight x = 1}) :
    (nativePrimeOfOriginalPoint f E (m := m) x).val =
      schemeNativeAlgebraicTrace f (closure {x.val}) :=
  (exists_nativePrime_of_original_codimOne f m E x.property).choose_spec

variable [ConnectedSpace (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  (hnorm : NormalizationProjectiveForCurves)

/-- The degree-one numerical class of the actual original prime. Its
representative by the actual canonical inverse ideal line is given below. -/
def originalPrimeNumerical (x : {x : X // Order.coheight x = 1}) :
    OriginalIntegralCurveDegreeQuotient_bd7 f E :=
  (integralNumericalEquivNS_bd7 f E m hnorm).symm
    ⟨DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor (nativePrimeOfOriginalPoint f E (m := m) x)),
      DFAlg.cycleClass_mem_neronSeveri _⟩

theorem numericalChern_originalPrimeNumerical (x : {x : X // Order.coheight x = 1}) :
    ((integralNumericalEquivNS_bd7 f E m hnorm
      (originalPrimeNumerical f E (m := m) hnorm x) :
      DFAlg.neronSeveri (m+1) (SchemeComplexPoint f)) :
      RealBottChern (m+1) (SchemeComplexPoint f)) =
        DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor (nativePrimeOfOriginalPoint f E (m := m) x)) := by
  simp [originalPrimeNumerical]

/-- A numerical generator is represented by the canonical line of an integral
effective Cartier subscheme with support exactly the closure of its index. -/
theorem originalPrimeNumerical_sameCartier (x : {x : X // Order.coheight x = 1}) :
    ∃ (I : X.IdealSheafData) (hI : I.IsInvertible),
      (I.support : Set X) = closure {x.val} ∧
      sectionZeroIdealSheaf (originalCartierIdealAtlas I hI).dual
        (originalCartierCanonicalSection I) = I ∧
      originalPrimeNumerical f E (m := m) hnorm x =
        (originalIntegralCurveDegreeRelations_bd7 f E).mkQ
          (Finsupp.single ⟨bundleDual I.toModules, (originalCartierIdealAtlas I hI).dual⟩ (1 : ℝ)) := by
  let P := nativePrimeOfOriginalPoint f E (m := m) x
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  obtain ⟨z, I, hI, _, hcl, htrace, _, _, _, hzero, hclass⟩ :=
    exists_originalCartierCodimOnePrime_cycleClass f m E P
  have hz : z = x.val := original_codimOne_eq_of_native_trace_eq f
    (htrace.symm.trans (nativePrimeOfOriginalPoint_val f E (m := m) x))
  refine ⟨I, hI, hcl.symm.trans (congrArg (fun w : X => closure {w}) hz), hzero, ?_⟩
  apply (integralNumericalEquivNS_bd7 f E m hnorm).injective
  apply Subtype.ext
  rw [numericalChern_originalPrimeNumerical, numericalChern_mkQ]
  simpa only [cartierChern_bd7, Finsupp.linearCombination_single, one_smul] using hclass

end Model

section Transition

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (EX : ClosedProjectiveEmbedding fX) (EY : ClosedProjectiveEmbedding fY) {m : ℕ}
  [SmoothOfRelativeDimension (m+1) fX] [SmoothOfRelativeDimension (m+1) fY]
  [IsSeparated fX] [QuasiCompact fX] [IsSeparated fY] [QuasiCompact fY]
  [CompactSpace (SchemeComplexPoint fX)] [CompactSpace (SchemeComplexPoint fY)]
  (q : X ⟶ Y) (hq : q ≫ fY = fX) [IsProper q]
  (hη : q (genericPoint X) = genericPoint Y) [IsIso (q.stalkMap (genericPoint X))]
  (hmod : IsAnalyticModification (n := m+1) (schemeComplexPointMap fX fY q hq))

local notation "qC" => schemeComplexPointMap fX fY q hq
local notation "pushBC" => classPushforward hmod.1 (canonicalBasis (m+1)) (Nat.succ_pos m)

include hq hη hmod in
/-- Both actual cycle pushforwards use the same target point and prime. The
analytic exceptional case and algebraic dimension-drop case both vanish. -/
theorem originalPrimeCycleClass_pushforward_square
    (x : {x : X // Order.coheight x = 1}) :
    let P := nativePrimeOfOriginalPoint fX EX (m := m) x
    if hy : Order.coheight (q x.val) = 1 then
      q.residueDegree x.val = 1 ∧
      AlgebraicCycle.map q (pointDimension X) (pointDimension Y) (schemePointCycle x.val 1) =
        schemePointCycle (q x.val) 1 ∧
      pushBC (DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P)) =
        (q.residueDegree x.val : ℝ) • DFAlg.cycleClass
          (SGPT.Siu.primeEffectiveDivisor (nativePrimeOfOriginalPoint fY EY (m := m) ⟨q x.val,hy⟩))
    else
      AlgebraicCycle.map q (pointDimension X) (pointDimension Y) (schemePointCycle x.val 1) = 0 ∧
      pushBC (DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P)) = 0 := by
  classical
  subst fX
  let : LocallyOfFiniteType (q ≫ fY) := EX.locallyOfFiniteType
  let : LocallyOfFiniteType fY := EY.locallyOfFiniteType
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  let P := nativePrimeOfOriginalPoint (q ≫ fY) EX (m := m) x
  have hcarrier : schemeComplexPointMap (q ≫ fY) fY q rfl '' P.val =
      schemeNativeAlgebraicTrace fY (closure {q x.val}) := by
    change schemeComplexPointMap (q ≫ fY) fY q rfl ''
      (nativePrimeOfOriginalPoint (q ≫ fY) EX (m := m) x).val = _
    rw [nativePrimeOfOriginalPoint_val]
    exact schemeComplexPointMap_image_pointClosure fY q x.val
  dsimp only
  by_cases hy : Order.coheight (q x.val) = 1
  · rw [dif_pos hy]
    let Q := nativePrimeOfOriginalPoint fY EY (m := m) ⟨q x.val, hy⟩
    have hQ : Q.val = schemeComplexPointMap (q ≫ fY) fY q rfl '' P.val :=
      (nativePrimeOfOriginalPoint_val fY EY (m := m) ⟨q x.val, hy⟩).trans hcarrier.symm
    have hne : ¬ P.val ⊆ SGPT.Foundations.Analysis.FirstPass.BlowupSequences.exceptionalLocus (m+1) (schemeComplexPointMap (q ≫ fY) fY q rfl) := by
      intro h
      exact (DFAlg.not_prime_subset_image_of_subset_exceptionalLocus hmod h Q) hQ.le
    have hP := DFAlg.classPushforward_cycleClass_prime hmod P
    rw [DFAlg.primePushforward, dif_neg hne, DFAlg.divisorClass_single, one_smul] at hP
    have hPQ : DFAlg.primeImage hmod P hne = Q :=
      SGPT.PSH.GeometricPrimeCarrier.ext ((DFAlg.primeImage_val hmod P hne).trans hQ.symm)
    rw [hPQ] at hP
    have hdeg := nativeBirational_residueDegree_eq_one_of_smooth_codimOne q hη x.val fY (m+1) hy
    have halg := (nativeBirational_primeCycle_map_and_complexCarrier_of_codimOne_image
      q hη x.val fY m x.property hy).1
    refine ⟨hdeg, halg, ?_⟩
    simpa only [hdeg, Nat.cast_one, one_smul] using hP
  · rw [dif_neg hy]
    have hexc : P.val ⊆ SGPT.Foundations.Analysis.FirstPass.BlowupSequences.exceptionalLocus (m+1) (schemeComplexPointMap (q ≫ fY) fY q rfl) := by
      by_contra hne
      let Q := DFAlg.primeImage hmod P hne
      obtain ⟨z, I, hI, hz, _, htrace, _⟩ :=
        exists_originalCartierCodimOnePrime_cycleClass fY m EY Q
      have hqz : q x.val = z := original_codimOne_eq_of_native_trace_eq fY
        (hcarrier.symm.trans ((DFAlg.primeImage_val hmod P hne).symm.trans htrace))
      exact hy (hqz.symm ▸ hz)
    have halg : AlgebraicCycle.map q (pointDimension X) (pointDimension Y)
        (schemePointCycle x.val 1) = 0 := by
      rcases nativeBirational_primeCycle_classification q hη x.val fY (m+1) x.property
        with ⟨_, hzero⟩ | ⟨hc, _, _⟩
      · exact hzero
      · exact (hy hc).elim
    exact ⟨halg, DFAlg.classPushforward_cycleClass_of_subset hmod hexc⟩

variable [ConnectedSpace (SchemeComplexPoint fX)] [ConnectedSpace (SchemeComplexPoint fY)]
  (hnorm : NormalizationProjectiveForCurves)

include hq hη hmod in
/-- The concrete residue-weighted generator premise for the actual numerical
pushforward in `BD7NumericalTransitions`. -/
theorem originalPrimeNumerical_pushforward_formula
    (x : {x : X // Order.coheight x = 1}) :
    pushBC (((integralNumericalEquivNS_bd7 fX EX m hnorm
      (originalPrimeNumerical fX EX (m := m) hnorm x) :
      DFAlg.neronSeveri (m+1) (SchemeComplexPoint fX)) :
      RealBottChern (m+1) (SchemeComplexPoint fX))) =
      ((integralNumericalEquivNS_bd7 fY EY m hnorm
        (algebraicPrimeImageClass fY EY q (originalPrimeNumerical fY EY (m := m) hnorm) x) :
        DFAlg.neronSeveri (m+1) (SchemeComplexPoint fY)) :
        RealBottChern (m+1) (SchemeComplexPoint fY)) := by
  classical
  rw [numericalChern_originalPrimeNumerical]
  have h := originalPrimeCycleClass_pushforward_square fX fY EX EY q hq hη hmod x
  dsimp only at h
  unfold algebraicPrimeImageClass
  split
  · rename_i hy
    rw [dif_pos hy] at h
    rw [map_smul]
    change _ = (q.residueDegree x.val : ℝ) •
      ((integralNumericalEquivNS_bd7 fY EY m hnorm
        (originalPrimeNumerical fY EY (m := m) hnorm ⟨q x.val, hy⟩) :
        DFAlg.neronSeveri (m+1) (SchemeComplexPoint fY)) :
        RealBottChern (m+1) (SchemeComplexPoint fY))
    rw [numericalChern_originalPrimeNumerical]
    exact h.2.2
  · rename_i hy
    rw [dif_neg hy] at h
    simpa using h.2

end Transition


section ActualModels

variable {Z : Scheme.{0}} [IsIntegral Z] {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  {A B : SmoothAlgebraicModel f (m+1)} (h : A ≤ B)

include E in
theorem SmoothAlgebraicModel.homOfLE_genericPoint_eq :
    A.homOfLE h (genericPoint B.V) = genericPoint A.V := by
  let := A.embedding.isSeparated
  let := A.embedding.quasiCompact
  let := B.embedding.isSeparated
  let := B.embedding.quasiCompact
  let := A.embedding.locallyOfFiniteType
  let q := A.homOfLE h
  let hq := SmoothAlgebraicModel.homOfLE_structure h
  have hs : Function.Surjective
      (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) q hq) :=
    AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      (SmoothAlgebraicModel.homOfLE_analyticModification h E)
  apply genericPoint_eq_of_surjective_complexPoints (A.p ≫ f) q
  intro z
  obtain ⟨y, hy⟩ := hs z
  refine ⟨⟨y.val, ?_⟩, ?_⟩
  · rw [hq]
    exact y.property
  · exact Subtype.ext (congrArg Subtype.val hy)

/-- The checked transported pushforward on the selected actual transition has
the residue-weighted formula on the same original Cartier generators. -/
theorem SmoothAlgebraicModel.homOfLE_originalPrimeNumerical_pushforward
    [ConnectedSpace (SchemeComplexPoint (B.p ≫ f))]
    [ConnectedSpace (SchemeComplexPoint (A.p ≫ f))]
    (hnorm : NormalizationProjectiveForCurves) (x : {x : B.V // Order.coheight x = 1}) :
    letI := A.embedding.isSeparated
    letI := A.embedding.quasiCompact
    letI := B.embedding.isSeparated
    letI := B.embedding.quasiCompact
    letI := A.embedding.analyticCompact
    letI := B.embedding.analyticCompact
    let q := A.homOfLE h
    let hq := SmoothAlgebraicModel.homOfLE_structure h
    let hmod := SmoothAlgebraicModel.homOfLE_analyticModification h E
    transportedAnalyticPushforward (B.p ≫ f) (A.p ≫ f) B.embedding A.embedding
      (m := m) hnorm (q := q) (hq := hq) (hmod := hmod)
      (originalPrimeNumerical (B.p ≫ f) B.embedding (m := m) hnorm x) =
    algebraicPrimeImageClass (A.p ≫ f) A.embedding q
      (originalPrimeNumerical (A.p ≫ f) A.embedding (m := m) hnorm) x := by
  let := A.embedding.isSeparated
  let := A.embedding.quasiCompact
  let := B.embedding.isSeparated
  let := B.embedding.quasiCompact
  let := A.embedding.analyticCompact
  let := B.embedding.analyticCompact
  let q := A.homOfLE h
  let hq := SmoothAlgebraicModel.homOfLE_structure h
  let hmod := SmoothAlgebraicModel.homOfLE_analyticModification h E
  let : IsProper q := SmoothAlgebraicModel.homOfLE_isProper h
  let : IsIso (q.stalkMap (genericPoint B.V)) :=
    SmoothAlgebraicModel.homOfLE_genericStalk_isIso h E
  apply (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m hnorm).injective
  apply Subtype.ext
  rw [numericalChern_transportedAnalyticPushforward]
  exact originalPrimeNumerical_pushforward_formula (B.p ≫ f) (A.p ≫ f)
    B.embedding A.embedding q hq (SmoothAlgebraicModel.homOfLE_genericPoint_eq E h)
    hmod hnorm x

end ActualModels

end SGPT.BDivisor.BD7
