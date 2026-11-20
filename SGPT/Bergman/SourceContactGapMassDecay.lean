import SGPT.Bergman.SourceContactGapExponentialBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.SingularWeightedHilbert
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

/-- Scalar exponential tail against a genuinely finite nonnegative mass. -/
theorem tendsto_exponential_finite_mass (D delta : ℝ) (hdelta : 0 < delta)
    (mass : ℝ≥0∞) (hmass : mass ≠ ⊤) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (D * Real.exp (-((k : ℝ) * delta))) * mass)
      atTop (𝓝 0) := by
  have hlin : Tendsto (fun k : ℕ => (k : ℝ) * delta) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hdelta tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hreal : Tendsto (fun k : ℕ => D * Real.exp (-((k : ℝ) * delta))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using he.const_mul D
  have henn : Tendsto (fun k : ℕ => ENNReal.ofReal (D * Real.exp (-((k : ℝ) * delta))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simpa only [zero_mul] using ENNReal.Tendsto.mul_const henn (Or.inr hmass)

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

/-- Literal source937: for EVERY fixed source alpha_m contact gap and
positive delta, the ACTUAL original beta_k mass tends to zero. Alpha,
the point/measure estimate and finite raw Kahler volume are produced
internally. No weak/asymptotic or desired zero-mass certificate enters. -/
theorem exists_source_fixedContactGap_mass_tendsto_zero
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {phi : X → EReal} (hphi : IsGlobalQuasiPshPotential (n := n) phi)
    (han : (ofFixedModel n X).HasRationalAnalyticChartType phi)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ alpha : ℕ → ℝ, StrictMono alpha ∧ (∀ k, 0 < alpha k ∧ alpha k < 1) ∧
      Tendsto alpha atTop (𝓝 1) ∧ ∀ m : ℕ, ∀ delta : ℝ, 0 < delta →
        Tendsto (fun k : ℕ =>
          sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
            ((IntegrationCurrent.kahlerVolume omega).comap
              (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi
            (sourceEnvelopeGap
              (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + eps • omega.form))
              (fun x => ((alpha m : ℝ) : EReal) * phi x) v delta)) atTop (𝓝 0) := by
  obtain ⟨alpha, hmono, ha, hlim, C, hC, N, hN, hbound⟩ :=
    exists_source_fixedContactGap_exponential_bound omega L T hL hT v hv hphi han heps
  refine ⟨alpha, hmono, ha, hlim, fun m delta hdelta => ?_⟩
  have hupper := tendsto_exponential_finite_mass ((n.factorial : ℝ) * C) delta hdelta
    (IntegrationCurrent.kahlerVolume omega univ) (measure_ne_top _ _)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [eventually_ge_atTop (max N m)] with k hk
    exact hbound m delta hdelta k (le_of_max_le_left hk) (le_of_max_le_right hk)

end SGPT.Bergman.ContactConcentration
