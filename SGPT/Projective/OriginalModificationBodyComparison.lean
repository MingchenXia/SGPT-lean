import SGPT.Projective.OriginalModificationPullbackCounts
import SGPT.Projective.OkounkovOriginalBigOfIVolume
import SGPT.AlmostSemigroup.DistanceZeroBodyTransport
import SGPT.AlmostSemigroup.CommonSupersetComparison

/-! Genuine arbitrary-valuation native-modification equality via actual counts and source distance. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalModification
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.Okounkov.OriginalBook
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
local instance : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
variable [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  [Nonempty (SchemeComplexPoint f)]
variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (c : X)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z] {π : Z → SchemeComplexPoint f}
  (hπ : IsAnalyticModification (n := m+1) π) (omegaZ : KahlerBackground (m+1) Z)
  {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)

include H hπ omegaZ hφ in
/-- Actual arbitrary-valuation value slices have zero discrepancy from actual original slices. -/
theorem distance_pullbackValues_eq_zero {C : AdmissibleCone (m+1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    (hsubZ : pullbackValues f E a v c π φ ⊆ (latticePoints C.cone : Set _))
    (hsubX : AlgebraicValuation.multiplierSectionSet f (m+1) E v c a φ ⊆
      (latticePoints C.cone : Set _)) :
    ConeSubset.distance (⟨_,hsubZ⟩ : ConeSubset C) (⟨_,hsubX⟩ : ConeSubset C) = 0 := by
  let : PseudoMetricSpace (ConeSubset C) := @ConeSubset.pseudoMetricSpace (m+1) C
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (m+1) E
  let S : ConeSubset C := ⟨_,hsubZ⟩
  let T : ConeSubset C := ⟨_,hsubX⟩
  let V := MeasureTheory.volume.real (PartialBody.generalPartialBody
    (schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY) (H.curvature a) φ)
  have hcardS (k : ℕ) : S.normalizedCardinality k = (k : ℝ)⁻¹ ^ (m+1) *
      (OkoTower.pullbackMultiplierH0 a H hπ hφ k : ℝ) := by
    rw [ConeSubset.normalizedCardinality]
    congr 1
    have h := Nat.card_eq_card_finite_toFinset (S.finite_slice k)
    have hc := card_slice_pullbackValues f E a v c hS hG hπ.1.continuous
      (OkoTower.quasiPsh_comp a H hπ hφ) k
    exact_mod_cast h.symm.trans hc
  have hs : Tendsto S.normalizedCardinality atTop (𝓝 V) :=
    (tendsto_normalized_pullbackMultiplierH0 f E a H hπ hφ Y hY omegaZ).congr
      (fun k => (hcardS k).symm)
  have ht : Tendsto T.normalizedCardinality atTop (𝓝 V) :=
    ValGen.tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφ
  have hcardT (k : ℕ) : T.normalizedCardinality k = (k : ℝ)⁻¹ ^ (m+1) *
      (Nat.card (slice T.val (k : ℤ)) : ℝ) := by
    rw [ConeSubset.normalizedCardinality]
    congr 1
    exact_mod_cast (Nat.card_eq_card_finite_toFinset (T.finite_slice k)).symm
  exact dist_eq_zero_of_common_superset S T (fun k => slice T.val (k : ℤ))
    T.finite_slice
    (by
      apply Eventually.of_forall
      intro k x hx
      exact (pullbackValues_subset f E a v c hπ hφ.1.quasiPlurisubharmonic) hx)
    (Eventually.of_forall fun _ => subset_rfl) hs ht (ht.congr fun k => hcardT k)

include hπ omegaZ in
/-- Actual positive original I-volume supplies the SAME own cone and the genuine pulled body equality. -/
theorem exists_pullbackBody_eq_of_kahler (hv : Function.Surjective v)
    (hpos : 0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      pullbackBody f E a v c (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) π φ =
        ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ := by
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφ hpos
  obtain ⟨hKc,hKv,_,hSL,hfull⟩ :=
    sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let : PseudoMetricSpace (ConeSubset C) := @ConeSubset.pseudoMetricSpace (m+1) C
  obtain ⟨_,_,hsubX,hGammaX,_,_,_⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f (m+1) E a H hbig v hv c hφ hpos
  have hsubZ : pullbackValues f E a v c π φ ⊆ (latticePoints C.cone : Set _) :=
    (pullbackValues_subset f E a v c hπ hφ.1.quasiPlurisubharmonic).trans hsubX
  have hz := distance_pullbackValues_eq_zero f E a H v c hπ omegaZ hφ hSL hfull.2 hsubZ hsubX
  have hGammaZ := DistanceZeroTransport.mem_almostSemigroupLocus_of_dist_eq_zero
    (⟨_,hsubZ⟩ : ConeSubset C) (⟨_,hsubX⟩ : ConeSubset C) hz hGammaX
  have hb := DistanceZeroTransport.bodyExtension_eq_of_dist_eq_zero
    (⟨_,hsubZ⟩ : ConeSubset C) (⟨_,hsubX⟩ : ConeSubset C) hz hGammaX
  refine ⟨hKc,hKv,?_⟩
  change ValGen.setBody C (pullbackValues f E a v c π φ) =
    ValGen.setBody C (AlgebraicValuation.multiplierSectionSet f (m+1) E v c a φ)
  rw [ValGen.setBody_eq hsubZ hGammaZ,ValGen.setBody_eq hsubX hGammaX]
  exact congrArg (fun K : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) => (K : Set (EuclideanSpace ℝ (Fin (m+1))))) hb

end SGPT.Okounkov.OriginalModification
