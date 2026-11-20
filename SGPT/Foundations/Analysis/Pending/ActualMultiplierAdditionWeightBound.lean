import SGPT.Foundations.Analysis.Pending.IEquivalentMax

set_option autoImplicit false

/-! # Actual exponential density bounds preparing multiplier-order addition -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionWeightBound

open FirstPass

noncomputable section

/-- Strong-openness slack is absorbed by one of two separate exponential ratios. -/
theorem real_exp_le_sum_add_ratios {c δ m : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hm : 2 * (c * (1 + δ)) / δ ≤ m) (a b u v : ℝ) :
    Real.exp (-(c * (a + b))) ≤
      Real.exp (-(c * (1 + δ) * (u + v))) + 1 +
        Real.exp (m * u) * Real.exp (-(m * a)) +
        Real.exp (m * v) * Real.exp (-(m * b)) := by
  have he1 : 0 ≤ Real.exp (-(c * (1 + δ) * (u + v))) := (Real.exp_pos _).le
  have he2 : 0 ≤ Real.exp (m * u) * Real.exp (-(m * a)) := by positivity
  have he3 : 0 ≤ Real.exp (m * v) * Real.exp (-(m * b)) := by positivity
  by_cases hpos : 0 ≤ c * (a + b)
  · have ht : Real.exp (-(c * (a + b))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  by_cases hfirst : c * (1 + δ) * (u + v) ≤ c * (a + b)
  · have ht := Real.exp_le_exp.mpr (neg_le_neg hfirst)
    linarith
  have hlt : c * (a + b) < c * (1 + δ) * (u + v) := lt_of_not_ge hfirst
  have hgap : -(c * (a + b)) <
      (c * (1 + δ) / δ) * ((u - a) + (v - b)) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hδ]
    nlinarith
  have hgap0 : 0 < (u - a) + (v - b) := by
    have hq : 0 < c * (1 + δ) / δ := by positivity
    by_contra hn
    have hle := mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt hn)
    linarith
  have hq0 : 0 ≤ c * (1 + δ) / δ := by positivity
  have hm' : (c * (1 + δ) / δ) * 2 ≤ m := by
    convert hm using 1; ring
  rcases le_total (v - b) (u - a) with h | h
  · have hd : 0 ≤ u - a := by linarith
    have hs : (u - a) + (v - b) ≤ 2 * (u - a) := by linarith
    have h1 := mul_le_mul_of_nonneg_left hs hq0
    have h2 := mul_le_mul_of_nonneg_right hm' hd
    have ht : -(c * (a + b)) ≤ m * u + -(m * a) := by nlinarith
    have he := Real.exp_le_exp.mpr ht
    rw [Real.exp_add] at he
    linarith

  · have hd : 0 ≤ v - b := by linarith
    have hs : (u - a) + (v - b) ≤ 2 * (v - b) := by linarith
    have h1 := mul_le_mul_of_nonneg_left hs hq0
    have h2 := mul_le_mul_of_nonneg_right hm' hd
    have ht : -(c * (a + b)) ≤ m * v + -(m * b) := by nlinarith
    have he := Real.exp_le_exp.mpr ht
    rw [Real.exp_add] at he
    linarith


/-- The ratio bound uses products rather than indeterminate extended-real differences. -/
theorem multiplierWeight_le_sum_add_ratios {c δ m : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hm : 2 * (c * (1 + δ)) / δ ≤ m) {a b u v : EReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    multiplierWeight c (a + b) ≤
      multiplierWeight (c * (1 + δ)) (u + v) + 1 +
        EReal.exp ((m : EReal) * u) * multiplierWeight m a +
        EReal.exp ((m : EReal) * v) * multiplierWeight m b := by
  have hq : 0 < c * (1 + δ) := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  induction u using EReal.rec with
  | bot => simp [EReal.bot_add v, multiplierWeight_bot hq]
  | top => exact absurd rfl hu
  | coe U =>
    induction v using EReal.rec with
    | bot => simp [EReal.add_bot (U : EReal), multiplierWeight_bot hq]
    | top => exact absurd rfl hv
    | coe V =>
      have heU : EReal.exp ((m : EReal) * (U : EReal)) ≠ 0 := by
        rw [← EReal.coe_mul, EReal.exp_coe]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
      have heV : EReal.exp ((m : EReal) * (V : EReal)) ≠ 0 := by
        rw [← EReal.coe_mul, EReal.exp_coe]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
      induction a using EReal.rec with
      | bot => simp [multiplierWeight_bot hm0, ENNReal.mul_top heU]
      | top => exact absurd rfl ha
      | coe A =>
        induction b using EReal.rec with
        | bot => simp [multiplierWeight_bot hm0, ENNReal.mul_top heV]
        | top => exact absurd rfl hb
        | coe B =>
          simp only [← EReal.coe_add, multiplierWeight_coe, ← EReal.coe_mul,
            EReal.exp_coe]
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add (Real.exp_pos _).le zero_le_one,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (real_exp_le_sum_add_ratios hc hδ hm A B U V)

end

end SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionWeightBound
