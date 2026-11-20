import SGPT.Bergman.SourceSectionLogObstacle

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.MultiplierSectionSingularity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped ENNReal

/-- Actual exponential readback of the normalized physical log candidate.
Both infinite envelope values and pointwise zero vectors are included;
the exact physical density and P prefactor are unchanged. -/
theorem weightedDensity_le_exp_of_normalizedLog_le
    {E : Type*} [NormedAddCommGroup E] (a : E) (v P : ℝ) (hP : 0 < P)
    (k : ℕ) (hk : 0 < k) (U : EReal)
    (h : (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq a +
      ((-((k : ℝ)⁻¹ * Real.log P) : ℝ) : EReal) ≤ U) :
    ENNReal.ofReal (‖a‖ ^ 2 * Real.exp (-((k : ℝ) * v))) ≤
      ENNReal.ofReal P * EReal.exp (((k : ℝ) : EReal) * (U - (v : EReal))) := by
  by_cases ha : a = 0
  · simp only [ha, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      ENNReal.ofReal_zero]
    exact zero_le
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hn : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  rw [logNormSq, ENNReal.log_ofReal_of_pos hn, ← EReal.coe_mul, ← EReal.coe_add] at h
  induction U using EReal.rec with
  | bot => exact False.elim ((not_le_of_gt (EReal.bot_lt_coe _)) h)
  | top =>
    rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.top_add_coe,
      EReal.coe_mul_top_of_pos hkp, EReal.exp_top,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hP)]
    exact le_top
  | coe U =>
    rw [EReal.coe_le_coe_iff] at h
    have hs := mul_le_mul_of_nonneg_left h hkp.le
    have hmul : (k : ℝ) * ((k : ℝ)⁻¹ * Real.log (‖a‖ ^ 2) +
        -((k : ℝ)⁻¹ * Real.log P)) = Real.log (‖a‖ ^ 2) - Real.log P := by
      field_simp
      ring
    rw [hmul] at hs
    have hlog : Real.log (‖a‖ ^ 2) + -((k : ℝ) * v) ≤
        Real.log P + (k : ℝ) * (U - v) := by linarith
    have hexp := Real.exp_le_exp.mpr hlog
    simp only [Real.exp_add, Real.exp_log hn, Real.exp_log hP] at hexp
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.exp_coe,
      ← ENNReal.ofReal_mul hP.le]
    exact ENNReal.ofReal_le_ofReal hexp

end SGPT.Bergman.MultiplierSectionSingularity
