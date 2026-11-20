import SGPT.Projective.OkounkovOriginalCurrentAllDimensions
import SGPT.Projective.OkounkovOriginalBigOfIVolume
import SGPT.Projective.OkounkovOriginalRightScalarAllDimensions
import SGPT.Okounkov.ThetaCurrentPullbackFunctorial

/-! Actual physical curvature coefficient equality, strict currents and original own-body transport.
Blueprint: okounkov-original-physical-body-transport.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
local instance physicalBodyTransportTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance physicalBodyTransportCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance physicalBodyTransportManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem original_kahlerCurrent_of_geometricallyEq (n : ℕ) [SmoothOfRelativeDimension n f]
    (E : ClosedProjectiveEmbedding f)
    (δ ρ : letI := E.isSeparated;letI := E.quasiCompact;ClosedRealOneOneForm n (SchemeComplexPoint f))
    (hgeo : letI := E.isSeparated;letI := E.quasiCompact;δ.val.GeometricallyEq ρ.val)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential ρ φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsKahlerCurrentPotential δ φ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨κ,hκ⟩ := hφ
  refine ⟨κ,?_⟩
  have hh : (δ-κ.form).val.GeometricallyEq (ρ-κ.form).val := by
    intro c z hz
    rw [sub_eq_add_neg,sub_eq_add_neg,ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_add,hgeo c hz]
  exact (hh.thetaPshPotential_iff φ).mpr hκ

theorem original_kahler_partialBodies_eq_of_geometricallyEq [IsIntegral X]
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L N : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas N) (K : SchemeLineBundleMetric f (m+1) E N)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (hgeo : letI := E.isSeparated;letI := E.quasiCompact;(K.curvature b).val.GeometricallyEq (H.curvature a).val)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsKahlerCurrentPotential (H.curvature a) φ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hAc : IsCompact (centreOkounkovBody f v a)) (hAv : Convex ℝ (centreOkounkovBody f v a))
      (hBc : IsCompact (centreOkounkovBody f v b)) (hBv : Convex ℝ (centreOkounkovBody f v b)),
      ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hAc hAv) φ =
      ValGen.partialBody f (m+1) E v (valuationCenter f v) b (SGPT.GAGA.OkoClose.coneOver _ hBc hBv) φ := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  have hK := original_kahlerCurrent_of_geometricallyEq f (m+1) E (K.curvature b) (H.curvature a) hgeo hφ
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hφK := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hpos := original_iVolume_pos_of_kahler_allDimensions f (m+1) E a H hφ
  have hbigA := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφθ hpos
  have hbigB := original_isBig_of_positive_iVolume_allDimensions f (m+1) E b K hφK
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E b K hK)
  have hcur := SGPT.Okounkov.thetaPotentialCurrent_eq_of_geometricallyEq hgeo.symm hφθ hφK
  obtain ⟨hAc,hAv,hBc,hBv,_,_,heq⟩ := centrePartialBodies_ownCones_eq_of_current_eq_allDimensions
    f (m+1) E a H b K hbigA hbigB v hv hφθ hφK hcur hpos
  exact ⟨hAc,hAv,hBc,hBv,heq⟩
end SGPT.Okounkov.OriginalBook
