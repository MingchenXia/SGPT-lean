import SGPT.Bergman.SourceEpsilonContactUnion
import SGPT.Bergman.SourcePerturbedContactWeakLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Bergman.BackgroundEnvelopeLimit

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.ReferenceEnvelopeConvergence
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Actual original eq:muP0_temp1 from source866-893 and immutable
fixed-epsilon eq:muP0_temp2. SAME original physical raw beta and phi;
the real source Kahler current/analytic type are the only new hypotheses.
No contact-null, envelope-limit, Berman upper baseline or DX mass certificate.
This proves the local subsequential-contact step, not whole weak convergence. -/
theorem source_originalAnalyticContact_weakLimit_zero
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {phi : X → EReal}
    (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) phi)
    (han : (ofFixedModel n X).HasRationalAnalyticType phi)
    (sigma : ℕ → ℕ) (hpos : ∀ j, 0 < sigma j) (hsigma : Tendsto sigma atTop atTop)
    (tau : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (sigma j) (hpos j) phi) atTop (𝓝 tau)) :
    (tau : Measure X) (sourceEnvelopeGap
      (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)) phi v 0) = 0 := by
  obtain ⟨hphi, _hmass⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega _ (wholeWeightedSubset (n := n) v).nonPluripolar_carrier hcurrent
  have hanchart : (ofFixedModel n X).HasRationalAnalyticChartType phi :=
    hasRationalAnalyticType_iff_chartType.mp han
  rw [sourceEnvelopeGap_zero_eq_iUnion_epsilon omega _ hcurrent han v]
  exact measure_iUnion_null fun j => source_perturbedContact_weakLimit_zero
    omega L T hL hT v hv hphi hanchart (sourceEpsilonSequence_pos j)
    sigma hpos hsigma tau hweak

end SGPT.Bergman.BackgroundEnvelopeLimit
