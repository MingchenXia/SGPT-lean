import SGPT.Bergman.SourceReferenceContactUnion
import SGPT.Bergman.SourceOriginalContactWeakLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Actual original eq:muP0_temp2: every true weak subsequential limit
of the SAME raw original beta gives the full phi contact-open in
c1(L)+eps*omega zero mass. Actual alpha-reference envelope convergence
and its union identity are produced internally from genuine current,
mass, d_S and partial-envelope producers. No desired contact-null or
reference-limit certificate is supplied. Whole weak convergence and the
epsilon->0/Berman/DX steps are not asserted by this LOCAL reader. -/
theorem source_perturbedContact_weakLimit_zero
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {phi : X → EReal} (hphi : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val phi)
    (han : (ofFixedModel n X).HasRationalAnalyticChartType phi)
    {eps : ℝ} (heps : 0 < eps)
    (sigma : ℕ → ℕ) (hpos : ∀ j, 0 < sigma j) (hsigma : Tendsto sigma atTop atTop)
    (tau : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (sigma j) (hpos j) phi) atTop (𝓝 tau)) :
    (tau : Measure X) (sourceEnvelopeGap
      (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + eps • omega.form))
      phi v 0) = 0 := by
  have hq : IsGlobalQuasiPshPotential (n := n) phi :=
    ⟨hphi.1.quasiPlurisubharmonic, hphi.2⟩
  obtain ⟨alpha, hmono, ha, hlim, hcontacts⟩ :=
    exists_source_fixedContactGap_weakLimit_zero omega L T hL hT v hv hq han heps
  have hcurrent : IsKahlerCurrentPotential
      (sourceNativeFirstChernForm L hL + eps • omega.form) phi := by
    let kappa : KahlerBackground n X := KahlerBackground.smul heps omega
    refine ⟨kappa, ?_⟩
    have hform : (sourceNativeFirstChernForm L hL + eps • omega.form) - kappa.form =
        sourceNativeFirstChernForm L hL := by
      dsimp only [kappa, KahlerBackground.smul]
      abel
    simpa only [hform] using hphi
  rw [sourceEnvelopeGap_zero_eq_iUnion_scaled omega _ hcurrent v alpha hmono.monotone
    (fun k => (ha k).1) (fun k => (ha k).2) hlim]
  exact measure_iUnion_null (fun k => hcontacts sigma hpos hsigma tau hweak k)

end SGPT.Bergman.ReferenceEnvelopeConvergence
