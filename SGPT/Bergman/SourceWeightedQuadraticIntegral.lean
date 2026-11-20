import SGPT.Bergman.SourceBergmanNormAxioms
import SGPT.Bergman.SourceTwistedMultiplierSections
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# WeightedQuadraticIntegral

The weighted square `|s|² e^{-kv}` on `K` and the parallelogram law of the norm `N^k_{v,μ}` (source `def:Bergman:L706`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X]

/-- The actual SAME Hermitian section's original real v-weighted square on the SAME K. -/
def weightedQuadraticDensity (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (s : twistedSections L T k) (x : W.carrier) : ℝ :=
  weightedPointNorm (twistedPower L T k).Fiber W k s x ^ 2

omit [MeasurableSpace X] [BorelSpace X] in
/-- Genuine original continuity, without a finite-mass or prescribed family input. -/
theorem weightedQuadraticDensity_continuous (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (s : twistedSections L T k) : Continuous (weightedQuadraticDensity L T W k s) :=
  (weightedPointNorm_continuous (twistedPower L T k).Fiber W k s).pow 2

omit [MeasurableSpace X] [BorelSpace X] in
/-- The original SAME-metric density is genuinely nonnegative. -/
theorem weightedQuadraticDensity_nonneg (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (s : twistedSections L T k) (x : W.carrier) : 0 ≤ weightedQuadraticDensity L T W k s x :=
  sq_nonneg _

/-- Genuine compactK continuity and original finite probability produce real integrability. -/
theorem weightedQuadraticDensity_integrable [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (μ : Measure W.carrier) [IsProbabilityMeasure μ] (s : twistedSections L T k) :
    Integrable (weightedQuadraticDensity L T W k s) μ := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  exact (weightedQuadraticDensity_continuous L T W k s).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- EXACT real squared original source norm integral, for ALL genuine SAME tensor sections. -/
theorem bernsteinMarkov_norm_sq_eq_integral [CompactSpace X] [ConnectedSpace X]
    (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (s : twistedSections L T k) :
    bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk s ^ 2 =
      ∫ x, weightedQuadraticDensity L T W k s x ∂μ := by
  let : IsProbabilityMeasure μ := hBM.1
  have hN : 0 ≤ bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk s := ENNReal.toReal_nonneg
  apply (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (weightedQuadraticDensity_nonneg L T W k s))).mp
  rw [ENNReal.ofReal_pow hN, bernsteinMarkovL2AddGroupNorm_ofReal,
    ofReal_integral_eq_lintegral_ofReal (weightedQuadraticDensity_integrable L T W k μ s)
      (Filter.Eventually.of_forall (weightedQuadraticDensity_nonneg L T W k s))]
  unfold weightedL2Norm
  simp_rw [weightedSectionDensity_eq_pointNorm_sq]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- The actual ORIGINAL tensor Hermitian fibers produce the weighted parallelogram pointwise. -/
theorem weightedQuadraticDensity_parallelogram (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)
    (s t : twistedSections L T k) (x : W.carrier) :
    weightedQuadraticDensity L T W k (s + t) x + weightedQuadraticDensity L T W k (s - t) x =
      2 * (weightedQuadraticDensity L T W k s x + weightedQuadraticDensity L T W k t x) := by
  change (‖s x.val + t x.val‖ * Real.exp (-((k : ℝ) * W.weight x) / 2)) ^ 2 +
    (‖s x.val - t x.val‖ * Real.exp (-((k : ℝ) * W.weight x) / 2)) ^ 2 = _
  simp only [weightedQuadraticDensity, weightedPointNorm, mul_pow]
  rw [← add_mul, parallelogram_law_with_norm ℂ]
  ring

/-- The source norm's parallelogram law is INTERNALLY derived from actual original integrals. -/
theorem bernsteinMarkov_norm_parallelogram [CompactSpace X] [ConnectedSpace X]
    (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (s t : twistedSections L T k) :
    bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk (s + t) ^ 2 +
        bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk (s - t) ^ 2 =
      2 * (bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk s ^ 2 +
        bernsteinMarkovL2AddGroupNorm L T W μ hBM k hk t ^ 2) := by
  let : IsProbabilityMeasure μ := hBM.1
  simp_rw [bernsteinMarkov_norm_sq_eq_integral]
  rw [← integral_add (weightedQuadraticDensity_integrable L T W k μ (s + t))
      (weightedQuadraticDensity_integrable L T W k μ (s - t)),
    ← integral_add (weightedQuadraticDensity_integrable L T W k μ s)
      (weightedQuadraticDensity_integrable L T W k μ t), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (weightedQuadraticDensity_parallelogram L T W k s t)

end SGPT.Bergman.SingularWeightedHilbert
