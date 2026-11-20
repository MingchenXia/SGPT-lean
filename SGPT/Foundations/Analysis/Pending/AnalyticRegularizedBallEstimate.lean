import SGPT.Foundations.Analysis.Pending.AnalyticWeightedMeanValue
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-! # Actual Haar normalization for analytic regularized-ball estimates -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallEstimate

open FirstPass

noncomputable section

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- The actual square-root ball has its literal Haar normalization in every
complex dimension, including the zero-dimensional model. -/
theorem volume_ball_sqrt_toReal (y : ComplexModel n) {S : ℝ} (hS : 0 < S) :
    (volume (ball y (Real.sqrt S))).toReal =
      S ^ n * (volume (ball (0 : ComplexModel n) 1)).toReal := by
  have hdim : Module.finrank ℝ (ComplexModel n) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel n),
      Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  rw [Measure.addHaar_ball_of_pos volume y (Real.sqrt_pos.mpr hS),
    ENNReal.toReal_mul, hdim, pow_mul, Real.sq_sqrt hS.le,
    ENNReal.toReal_ofReal (pow_nonneg hS.le n)]

/-- Actual weighted holomorphic submean, literal generator control, and
actual Haar volume produce the regularized positive-base power bound. -/
theorem norm_sq_le_regularized_power_bound
    {B : Set (ComplexModel n)} (hB : IsOpen B) {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h B) {P : ComplexModel n → EReal}
    {N : ℕ} (g : Fin N → ComplexModel n → ℂ)
    {q c A S b : ℝ} (hq : 0 < q) (hc : 0 < c) (hA : 0 < A) (hS : 0 < S)
    {y : ComplexModel n} (hsub : closedBall y (Real.sqrt S) ⊆ B)
    (hP : ∀ z ∈ ball y (Real.sqrt S),
      P z ≤ (c : EReal) * generatorLog g z + (b : EReal))
    (hg : ∀ z ∈ ball y (Real.sqrt S), generatorNormSq g z ≤ A * S)
    (hfinite : (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤) :
    ‖h y‖ ^ 2 ≤
      (Real.exp (q * b) * A ^ (q * c) *
        (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)).toReal /
        (volume (ball (0 : ComplexModel n) 1)).toReal) * S ^ (q * c - (n : ℝ)) := by
  have hAS : 0 < A * S := mul_pos hA hS
  have hb : ∀ z ∈ ball y (Real.sqrt S), P z ≤ ((c * Real.log (A * S) + b : ℝ) : EReal) := by
    intro z hz
    have hlog : generatorLog g z ≤ (Real.log (A * S) : EReal) := by
      rw [generatorLog_eq_log_sum]
      calc ENNReal.log (ENNReal.ofReal (∑ i, ‖g i z‖ ^ 2))
          ≤ ENNReal.log (ENNReal.ofReal (A * S)) :=
            ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (hg z hz))
        _ = _ := ENNReal.log_ofReal_of_pos hAS
    calc P z ≤ (c : EReal) * generatorLog g z + (b : EReal) := hP z hz
      _ ≤ (c : EReal) * (Real.log (A * S) : EReal) + (b : EReal) := by
        gcongr
      _ = _ := by simp only [← EReal.coe_mul, ← EReal.coe_add]
  have hbound := AnalyticWeightedMeanValue.norm_sq_le_weighted_lintegral_toReal_div_volume
    hB hh hq (Real.sqrt_pos.mpr hS) hsub hb hfinite
  rw [volume_ball_sqrt_toReal y hS] at hbound
  have hexp : Real.exp (q * (c * Real.log (A * S) + b)) =
      Real.exp (q * b) * A ^ (q * c) * S ^ (q * c) := by
    rw [Real.log_mul hA.ne' hS.ne', Real.rpow_def_of_pos hA,
      Real.rpow_def_of_pos hS, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hbound
  rw [Real.rpow_sub_natCast hS.ne']
  convert hbound using 1
  ring

end

end SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallEstimate
