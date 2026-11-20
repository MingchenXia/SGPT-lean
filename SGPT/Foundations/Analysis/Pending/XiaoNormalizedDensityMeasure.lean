import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

/-!
# The genuine normalized density measure in Xiao's bad-set argument

An integrable nonnegative density of total mass one produces a probability
measure. For a strictly positive measurable density, division by that density
transfers integrability and the integral itself from the base measure.
-/

open MeasureTheory Set

namespace SGPT.Foundations.Analysis.Pending.XiaoNormalizedDensityMeasure

/-- A nonnegative integrable density with integral one gives an actual probability measure. -/
theorem isProbabilityMeasure_withDensity_of_integral_one {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {v : X → ℝ} (hvi : Integrable v σ) (hv : ∀ x, 0 ≤ v x)
    (hnorm : ∫ x, v x ∂σ = 1) :
    IsProbabilityMeasure (σ.withDensity fun x => ENNReal.ofReal (v x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hvi (ae_of_all σ hv), hnorm]
  simp

/-- An integrable numerator becomes an integrable ratio for the true density measure. -/
theorem integrable_div_withDensity {X : Type*} [MeasurableSpace X] (σ : Measure X)
    {v P : X → ℝ} (hvm : Measurable v) (hv : ∀ x, 0 < v x) (hPi : Integrable P σ) :
    Integrable (fun x => P x / v x) (σ.withDensity fun x => ENNReal.ofReal (v x)) := by
  apply (integrable_withDensity_iff_integrable_smul' hvm.ennreal_ofReal
    (ae_of_all σ fun _ => ENNReal.ofReal_lt_top)).2
  have hfun : (fun x => (ENNReal.ofReal (v x)).toReal • (P x / v x)) = P := by
    funext x
    rw [ENNReal.toReal_ofReal (hv x).le, smul_eq_mul]
    field_simp [(hv x).ne']
  rwa [hfun]

/-- Integrating the ratio against the actual density measure cancels its denominator. -/
theorem integral_div_withDensity {X : Type*} [MeasurableSpace X] (σ : Measure X)
    {v : X → ℝ} (hvm : Measurable v) (hv : ∀ x, 0 < v x) (P : X → ℝ) :
    ∫ x, P x / v x ∂(σ.withDensity fun x => ENNReal.ofReal (v x)) = ∫ x, P x ∂σ := by
  rw [integral_withDensity_eq_integral_toReal_smul hvm.ennreal_ofReal
    (ae_of_all σ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (hv x).le, smul_eq_mul]
  field_simp [(hv x).ne']

end SGPT.Foundations.Analysis.Pending.XiaoNormalizedDensityMeasure
