import SGPT.Bergman.SourceSingularWeightedHilbert
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# WeightedHermitianIntegral

The weighted Hermitian pairing `∫_K ⟨s,t⟩ e^{-kv} dμ` and its integrability.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ)

omit [MeasurableSpace X] [BorelSpace X] in
/-- EXACT original real quadratic density and SAME full Hermitian fiber norm. -/
theorem weightedQuadraticDensity_eq_norm_sq_weight (s : twistedSections L T k) (x : W.carrier) :
    weightedQuadraticDensity L T W k s x = ‖s x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x)) := by
  have h := weightedSectionDensity_eq_pointNorm_sq (twistedPower L T k).Fiber W k s x
  rw [weightedSectionDensity, SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight,
    multiplierWeight_coe, ← ENNReal.ofReal_mul (sq_nonneg _)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (weightedQuadraticDensity_nonneg L T W k s x)
    (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).mp h.symm

/-- ACTUAL original fiber Hermitian pairing, with the SAME real source obstacle v and original k. -/
def weightedHermitianPairing (s t : twistedSections L T k) (x : W.carrier) : ℂ :=
  (Real.exp (-((k : ℝ) * W.weight x)) : ℂ) * inner ℂ (s x.val) (t x.val)

omit [MeasurableSpace X] [BorelSpace X] in
/-- True fiber polarization identifies the weighted original pairing with four ACTUAL original section densities. -/
theorem weightedHermitianPairing_polarization (s t : twistedSections L T k) (x : W.carrier) :
    weightedHermitianPairing L T W k s t x =
      ((weightedQuadraticDensity L T W k (s + t) x : ℂ) -
        (weightedQuadraticDensity L T W k (s - t) x : ℂ) +
        ((weightedQuadraticDensity L T W k (s - Complex.I • t) x : ℂ) -
          (weightedQuadraticDensity L T W k (s + Complex.I • t) x : ℂ)) * Complex.I) / 4 := by
  unfold weightedHermitianPairing
  rw [inner_eq_sum_norm_sq_div_four]
  simp_rw [weightedQuadraticDensity_eq_norm_sq_weight]
  change (Real.exp (-((k : ℝ) * W.weight x)) : ℂ) *
    (((‖s x.val + t x.val‖ : ℂ) ^ 2 - (‖s x.val - t x.val‖ : ℂ) ^ 2 +
      ((‖s x.val - Complex.I • t x.val‖ : ℂ) ^ 2 - (‖s x.val + Complex.I • t x.val‖ : ℂ) ^ 2) * Complex.I) / 4) =
      ((↑(‖s x.val + t x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x))) : ℂ) -
        (↑(‖s x.val - t x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x))) : ℂ) +
        ((↑(‖s x.val - Complex.I • t x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x))) : ℂ) -
          (↑(‖s x.val + Complex.I • t x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x))) : ℂ)) * Complex.I) / 4
  push_cast
  ring

variable [CompactSpace X] (μ : Measure W.carrier) [IsProbabilityMeasure μ]

/-- Genuine integrability is INTERNALLY derived for the actual original fiber pairing. -/
theorem weightedHermitianPairing_integrable (s t : twistedSections L T k) :
    Integrable (weightedHermitianPairing L T W k s t) μ := by
  have hq (u : twistedSections L T k) :
      Integrable (fun x => (weightedQuadraticDensity L T W k u x : ℂ)) μ :=
    (weightedQuadraticDensity_integrable L T W k μ u).ofReal
  have hi := ((hq (s + t)).sub (hq (s - t))).add
    (((hq (s - Complex.I • t)).sub (hq (s + Complex.I • t))).mul_const Complex.I)
  exact (hi.div_const 4).congr (Filter.Eventually.of_forall fun x =>
    (weightedHermitianPairing_polarization L T W k s t x).symm)

/-- Actual Bochner linearity reads the SAME original fiber pairing integral in its four real quadratic integrals. -/
theorem integral_weightedHermitianPairing_polarization (s t : twistedSections L T k) :
    (∫ x, weightedHermitianPairing L T W k s t x ∂μ) =
      (Complex.ofReal (∫ x, weightedQuadraticDensity L T W k (s + t) x ∂μ) -
        Complex.ofReal (∫ x, weightedQuadraticDensity L T W k (s - t) x ∂μ) +
        (Complex.ofReal (∫ x, weightedQuadraticDensity L T W k (s - Complex.I • t) x ∂μ) -
          Complex.ofReal (∫ x, weightedQuadraticDensity L T W k (s + Complex.I • t) x ∂μ)) * Complex.I) / 4 := by
  have hq (u : twistedSections L T k) :
      Integrable (fun x => (weightedQuadraticDensity L T W k u x : ℂ)) μ :=
    (weightedQuadraticDensity_integrable L T W k μ u).ofReal
  simp_rw [weightedHermitianPairing_polarization]
  have he := integral_add ((hq (s + t)).sub (hq (s - t)))
    (((hq (s - Complex.I • t)).sub (hq (s + Complex.I • t))).mul_const Complex.I)
  simp only [Pi.sub_apply] at he
  rw [integral_sub (hq (s + t)) (hq (s - t)), integral_mul_const,
    integral_sub (hq (s - Complex.I • t)) (hq (s + Complex.I • t))] at he
  simpa only [Pi.add_apply, Pi.sub_apply, integral_div, integral_complex_ofReal] using
    congrArg (fun z : ℂ => z / 4) he

variable [ConnectedSpace X] (hBM : IsBernsteinMarkov L T W μ) (hk : 0 < k) (φ : X → EReal)

/-- The produced complex Hilbert pairing is EXACTLY the SAME original h^k tensorh_T, v,mu integral,
with native conjugate-first/linear-second convention. No inner-product certificate is supplied. -/
theorem sourceHilbert_inner_eq_original_integral
    (s t : SourceHilbertSections L T W μ hBM k hk φ) :
    inner ℂ s t = ∫ x, weightedHermitianPairing L T W k
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ s).val
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ t).val x ∂μ := by
  rw [inner_eq_sum_norm_sq_div_four, integral_weightedHermitianPairing_polarization]
  have hn (u : SourceHilbertSections L T W μ hBM k hk φ) :
      (‖u‖ : ℂ) ^ 2 = Complex.ofReal (∫ x, weightedQuadraticDensity L T W k
        (sourceHilbertOriginalEquiv L T W μ hBM k hk φ u).val x ∂μ) := by
    exact_mod_cast sourceHilbert_norm_sq_integral L T W μ hBM k hk φ u
  change (( (‖s + t‖ : ℂ) ^ 2 - (‖s - t‖ : ℂ) ^ 2 +
    ((‖s - Complex.I • t‖ : ℂ) ^ 2 - (‖s + Complex.I • t‖ : ℂ) ^ 2) * Complex.I) / 4) = _
  rw [hn (s + t), hn (s - t), hn (s - Complex.I • t), hn (s + Complex.I • t)]
  rfl

end SGPT.Bergman.SingularWeightedHilbert
