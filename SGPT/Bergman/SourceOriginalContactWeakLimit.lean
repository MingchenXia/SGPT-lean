import SGPT.Bergman.SourceContactGapMassDecay
import SGPT.Bergman.SourceBergmanFiniteMeasures
import SGPT.Bergman.SourceFiniteMeasureOpenZero
import SGPT.Bergman.SourceContactGapCountableUnion
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

/-- Literal final local source step935-938: EVERY actual weak subsequential
limit of the ORIGINAL beta measures gives every fixed-m ENTIRE original
open contact gap zero mass. The subsequence/weak-limit reader is exactly the local
book proof-use input; existence or whole weak convergence is NOT claimed.
Finite original measures, the actual gap mass decay, open gaps and native
metrizability are all manufactured internally, without phi normalization. -/
theorem exists_source_fixedContactGap_weakLimit_zero
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {phi : X → EReal} (hphi : IsGlobalQuasiPshPotential (n := n) phi)
    (han : (ofFixedModel n X).HasRationalAnalyticChartType phi)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ alpha : ℕ → ℝ, StrictMono alpha ∧ (∀ k, 0 < alpha k ∧ alpha k < 1) ∧
      Tendsto alpha atTop (𝓝 1) ∧
      ∀ sigma : ℕ → ℕ, ∀ hpos : ∀ j, 0 < sigma j,
        Tendsto sigma atTop atTop → ∀ tau : FiniteMeasure X,
        Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
          (sigma j) (hpos j) phi) atTop (𝓝 tau) →
        ∀ m : ℕ,
          (tau : Measure X) (sourceEnvelopeGap
            (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + eps • omega.form))
            (fun x => ((alpha m : ℝ) : EReal) * phi x) v 0) = 0 := by
  obtain ⟨alpha, hmono, ha, hlim, hdecay⟩ :=
    exists_source_fixedContactGap_mass_tendsto_zero omega L T hL hT v hv hphi han heps
  refine ⟨alpha, hmono, ha, hlim, fun sigma hpos hsigma tau hweak m => ?_⟩
  apply measure_sourceEnvelopeGap_zero_of_positive
  intro delta hdelta
  let : TopologicalSpace.PseudoMetrizableSpace X :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n X
  apply finiteMeasure_open_eq_zero_of_mass_tendsto_zero hweak
    (sourceEnvelopeGap_isOpen _ _ v delta)
  simpa only [Function.comp_def, sourceBergmanFiniteMeasure_toMeasure] using
    (hdecay m delta hdelta).comp hsigma

end SGPT.Bergman.ContactConcentration
