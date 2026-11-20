import SGPT.Projective.OkounkovOriginalTwistedMultiplierAsymptotics
import SGPT.Projective.OkounkovOriginalCurrentDictionary
import SGPT.Projective.OkounkovOriginalCommonMultiplierTwist
import SGPT.Projective.OkounkovOriginalBodyClassInvariance
import SGPT.AlmostSemigroup.CommonSupersetComparison
import SGPT.AlmostSemigroup.ConeIndependence

/-! Actual original current invariance, ANY original valuation, both genuine original own-body cones.
Blueprint: okounkov-original-book-current.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.Okounkov.AlgebraicValuation SGPT.NAPotential.FSPos
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance bookCurrentTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookCurrentCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance bookCurrentManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original current equality gives SAME partial bodies in OWN original cones, positive dimension. -/
theorem partialBodies_ownCones_eq_of_current_eq_positiveDimension {L L' : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas L') (K : SchemeLineBundleMetric f (m+1) E L')
    (hbig : SGPT.LineBundle.IsBig f L (m+1)) (hbig' : SGPT.LineBundle.IsBig f L' (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (c : X) (hc : IsNonnegAt v c) {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (K.curvature b).val ψ)
    (heq : letI := E.isSeparated; letI := E.quasiCompact;
      thetaPotentialCurrent (H.curvature a).val φ hφ = thetaPotentialCurrent (K.curvature b).val ψ hψ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hAc : IsCompact (okounkovBody v c a)) (hAv : Convex ℝ (okounkovBody v c a))
      (hBc : IsCompact (okounkovBody v c b)) (hBv : Convex ℝ (okounkovBody v c b)),
      okounkovBody v c a = okounkovBody v c b ∧
      0 < iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ ∧
      ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ =
        ValGen.partialBody f (m+1) E v c b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨hclass,hI,hmass⟩ := OriginalCurrentDictionary.original_class_ideals_iVolume_of_current_eq
    f E a b H K hφ hψ heq
  have hpos' : 0 < iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ := by
    rw [←hmass]
    exact hpos
  have hbody := okounkovBody_eq_of_chernClass_eq_allDimensions f (m+1) E a H b K hbig hbig' v hv c hc hclass
  obtain ⟨hAc,hAv,hsubA,hΓA,-⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f (m+1) E a H hbig v hv c hφ hpos
  obtain ⟨hBc,hBv,hsubB,hΓB,-⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f (m+1) E b K hbig' v hv c hψ hpos'
  let C := SGPT.GAGA.OkoClose.coneOver _ hAc hAv
  let D := SGPT.GAGA.OkoClose.coneOver _ hBc hBv
  have hDC : (D.cone : Set ((Fin (m+1) → ℝ) × ℝ)) ⊆ C.cone := by
    intro z hz
    change 0≤z.2 ∧ ∃ y∈okounkovBody v c b,z.1=z.2•y at hz
    change 0≤z.2 ∧ ∃ y∈okounkovBody v c a,z.1=z.2•y
    obtain ⟨hz,y,hy,he⟩ := hz
    refine ⟨hz,y,?_,he⟩
    rw [hbody]
    exact hy
  let SA : AlmostSpace C := ⟨⟨_,hsubA⟩,hΓA⟩
  let TB : AlmostSpace D := ⟨⟨_,hsubB⟩,hΓB⟩
  let TC : AlmostSpace C := ConeIndependence.includeAlmost hDC TB
  obtain ⟨k,hk,hinc⟩ := OriginalCommonMultiplierTwist.exists_common_fixed_positive_twist_multiplier_inclusions
    f (m+1) E a b (hyperplaneAtlas E) H K (fubiniStudyMetric f E (m+1))
      (fubiniStudy_isKahler f E (m+1)) hclass
  let R (j : ℕ) := pairwiseTensorAtlas ((hyperplaneAtlas E).tensorPower k) (b.tensorPower j)
  let Q (j : ℕ) := AlgebraicValuation.twistedMultiplierValues f (m+1) E v c j (R j) ψ
  have hQeq (j : ℕ) : AlgebraicValuation.twistedMultiplierValues f (m+1) E v c j (R j) φ=Q j := by
    dsimp only [Q]
    unfold AlgebraicValuation.twistedMultiplierValues
    rw [hI (j:ℝ)]
  have hSQ : ∀ᶠ j : ℕ in atTop, slice SA.val.val (j:ℤ) ⊆ Q j := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have h := (hinc j hj v c hc (R j) φ ψ hI).1
    rw [hQeq j] at h
    exact h
  have hTQ : ∀ᶠ j : ℕ in atTop, slice TC.val.val (j:ℤ) ⊆ Q j := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have h := (hinc j hj v c hc (R j) φ ψ hI).2
    rw [hQeq j] at h
    exact h
  have hQ (j : ℕ) : (Q j).Finite :=
    (OriginalTwistedMultiplierCount.twistedMultiplierValues_finite_card f E b hbig' v hv c j (R j)
      hψ.1.quasiPlurisubharmonic).1
  let V : ℝ := (iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ).toReal /
    ((m+1).factorial:ℝ)
  have hS : Tendsto SA.val.normalizedCardinality atTop (𝓝 V) := by
    have h := OriginalMultiplierAsymptotics.tendsto_normalized_original_multiplier_slice_card f E a H hbig v hv c hφ
    rw [hmass] at h
    exact h.congr (fun j => (ValGen.normalizedCardinality_eq_card SA.val j).symm)
  have hT : Tendsto TC.val.normalizedCardinality atTop (𝓝 V) := by
    have h := OriginalMultiplierAsymptotics.tendsto_normalized_original_multiplier_slice_card f E b K hbig' v hv c hψ
    exact h.congr (fun j => (ValGen.normalizedCardinality_eq_card TC.val j).symm)
  have hcount : Tendsto (fun j : ℕ => (j:ℝ)⁻¹^(m+1)*(Nat.card (Q j):ℝ)) atTop (𝓝 V) :=
    OriginalMultiplierAsymptotics.tendsto_normalized_twistedMultiplierValues_card f E b K hbig' v hv c
      ((hyperplaneAtlas E).tensorPower k) R hψ
  have hext := bodyExtension_eq_of_common_superset SA TC Q hQ hSQ hTQ hS hT hcount
  have hcone := ConeIndependence.bodyExtension_includeAlmost hDC TB
  refine ⟨hAc,hAv,hBc,hBv,hbody,hpos',?_⟩
  calc
    _ = (bodyExtension SA : Set (EuclideanSpace ℝ (Fin (m+1)))) := ValGen.partialBody_eq a φ hsubA hΓA
    _ = (bodyExtension TC : Set (EuclideanSpace ℝ (Fin (m+1)))) :=
      congrArg (fun B : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) =>
        (B:Set (EuclideanSpace ℝ (Fin (m+1))))) hext
    _ = (bodyExtension TB : Set (EuclideanSpace ℝ (Fin (m+1)))) :=
      congrArg (fun B : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) =>
        (B:Set (EuclideanSpace ℝ (Fin (m+1))))) hcone
    _ = _ := (ValGen.partialBody_eq b ψ hsubB hΓB).symm

end SGPT.Okounkov.OriginalBook
