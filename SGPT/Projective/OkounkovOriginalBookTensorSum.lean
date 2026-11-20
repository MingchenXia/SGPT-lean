import SGPT.Projective.OkounkovOriginalTensorSumPositiveIVolume
import SGPT.NAPotential.FSPosKahler

/-! ENTIRE printed prop:suba, actual ORIGINAL I-volume domain, arbitrary original valuation, all n0.
Blueprint: okounkov-original-book-tensor-sum.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.NAPotential.FSPos
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance bookTensorSumTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bookTensorSumCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bookTensorSumManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_partialBody_tensorSum_allDimensions {L N : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f n E N)
    (d : LineBundleAtlas (bundleTensor L N))
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (K.curvature b).val ψ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ →
    0 < iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ →
    ∃ (hAc : IsCompact (centreOkounkovBody f v a)) (hAv : Convex ℝ (centreOkounkovBody f v a))
      (hBc : IsCompact (centreOkounkovBody f v b)) (hBv : Convex ℝ (centreOkounkovBody f v b))
      (hDc : IsCompact (centreOkounkovBody f v d)) (hDv : Convex ℝ (centreOkounkovBody f v d)),
      ValGen.partialBody f n E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ +
        ValGen.partialBody f n E v (valuationCenter f v) b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) ψ ⊆
      ValGen.partialBody f n E v (valuationCenter f v) d (SGPT.GAGA.OkoClose.coneOver _ hDc hDv) (fun x => φ x+ψ x) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  intro hposφ hposψ
  cases n with
  | succ m =>
    let P : SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) := {
      power := 1
      power_pos := one_pos
      ambientDimension := E.ambientDimension
      map := E.map
      isClosedImmersion := E.closedImmersion
      over_base := E.over_base
      iso := bundleTensorLeftUnitIso (hyperplaneBundle E) }
    exact original_partialBody_tensorSum_positive_iVolume f E a H b K d (hyperplaneAtlas E) P
      (fubiniStudyMetric f E (m+1)) (fubiniStudy_isKahler f E (m+1)) v hv hφ hψ hposφ hposψ
  | zero =>
    let c := valuationCenter f v
    let HM := H.tensorProduct K a b
    let χ := fun x => φ x+ψ x
    have hraw := isThetaPshPotential_add_from_positive_sum hφ hψ
    have hχ := ((H.curvature_tensorProduct K a b d).thetaPshPotential_iff χ).mpr hraw
    have hposχ : 0 < iVolume (HM.curvature d) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) χ hχ := by
      rw [PobDimZero.iVolume_eq_one (HM.curvature d) _ hχ]
      exact zero_lt_one
    have hbigA := original_isBig_of_positive_iVolume_allDimensions f 0 E a H hφ hposφ
    have hbigB := original_isBig_of_positive_iVolume_allDimensions f 0 E b K hψ hposψ
    have hbigD := original_isBig_of_positive_iVolume_allDimensions f 0 E d HM hχ hposχ
    obtain ⟨hAc,hAv,hAint,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a 0 E hbigA v hv c
    obtain ⟨hBc,hBv,hBint,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f b 0 E hbigB v hv c
    obtain ⟨hDc,hDv,hDint,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f d 0 E hbigD v hv c
    let CA := SGPT.GAGA.OkoClose.coneOver _ hAc hAv
    let CB := SGPT.GAGA.OkoClose.coneOver _ hBc hBv
    let CD := SGPT.GAGA.OkoClose.coneOver _ hDc hDv
    obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
    have hA1 := PobDimZero.mem_coneOver_zero_one hAc hAv (hAint.mono interior_subset)
    have hB1 := PobDimZero.mem_coneOver_zero_one hBc hBv (hBint.mono interior_subset)
    have hD1 := PobDimZero.mem_coneOver_zero_one hDc hDv (hDint.mono interior_subset)
    have hA0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential CA hA1
    have hB0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY b c v hψ.quasiPshPotential CB hB1
    have hD0 := PobDimZero.valuation_partialBody_eq_univ f E Y hY d c v hχ.quasiPshPotential CD hD1
    refine ⟨hAc,hAv,hBc,hBv,hDc,hDv,?_⟩
    change ValGen.partialBody f 0 E v c a CA φ+ValGen.partialBody f 0 E v c b CB ψ⊆
      ValGen.partialBody f 0 E v c d CD χ
    rw [hA0,hB0,hD0]
    exact subset_univ _
end SGPT.Okounkov.OriginalBook
