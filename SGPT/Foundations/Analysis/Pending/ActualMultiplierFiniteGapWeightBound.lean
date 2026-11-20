import SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionWeightBound

set_option autoImplicit false

/-! # Actual finite exponent gaps preparing complete sum approximations -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapWeightBound

open FirstPass

noncomputable section

/-- Strict source/target exponents internally supply an integer generator level
and a smaller positive target level that absorb the density gap. -/
theorem exists_exponent_parameters {c q : ℝ} (hc : 0 < c) (hcq : c < q) :
    ∃ m : ℕ, 0 < m ∧ ∃ p : ℝ, 0 < p ∧ p < m ∧ 2 * c ≤ p - (m : ℝ) * c / q := by
  have hq : 0 < q := hc.trans hcq
  have hr : 0 < c / q := div_pos hc hq
  have hr1 : c / q < 1 := (div_lt_one hq).mpr hcq
  let α : ℝ := (1 + c / q) / 2
  have hα0 : 0 < α := by dsimp only [α]; positivity
  have hα1 : α < 1 := by dsimp only [α]; linarith
  have hgap : 0 < α - c / q := by dsimp only [α]; linarith
  let m : ℕ := ⌈2 * c / (α - c / q)⌉₊
  have hm : 0 < m := Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num) hc) hgap)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨m, hm, α * m, mul_pos hα0 hmR, ?_, ?_⟩
  · simpa only [one_mul] using mul_lt_mul_of_pos_right hα1 hmR
  · have hmle : 2 * c / (α - c / q) ≤ (m : ℝ) := Nat.le_ceil _
    have ht := (div_le_iff₀ hgap).mp hmle
    rw [mul_sub, mul_comm (m : ℝ) α, ← mul_div_assoc] at ht
    exact ht

/-- One of two independently integrated ratios controls every finite gap. -/
theorem real_exp_le_sum_add_ratios {c q p m : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hm : 0 < m)
    (hgap : 2 * c ≤ p - m * c / q) (a b u v : ℝ) :
    Real.exp (-(c * (a + b))) ≤ Real.exp (-(q * (u + v))) + 1 +
      Real.exp (m * u) * Real.exp (-(p * a)) +
      Real.exp (m * v) * Real.exp (-(p * b)) := by
  have he1 : 0 ≤ Real.exp (-(q * (u + v))) := (Real.exp_pos _).le
  have he2 : 0 ≤ Real.exp (m * u) * Real.exp (-(p * a)) := by positivity
  have he3 : 0 ≤ Real.exp (m * v) * Real.exp (-(p * b)) := by positivity
  by_cases hpos : 0 ≤ c * (a + b)
  · have ht : Real.exp (-(c * (a + b))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    linarith
  by_cases hfirst : q * (u + v) ≤ c * (a + b)
  · have ht := Real.exp_le_exp.mpr (neg_le_neg hfirst)
    linarith
  have hlt : c * (a + b) < q * (u + v) := lt_of_not_ge hfirst
  have hX : 0 ≤ -(a + b) := by nlinarith
  have hratio : (c / q) * (a + b) < u + v := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hq]
    simpa only [mul_comm q] using hlt
  have h1 := mul_lt_mul_of_pos_left hratio hm
  have h2 := mul_le_mul_of_nonneg_right hgap hX
  simp only [mul_div_assoc] at h2
  have hsum : 2 * (-(c * (a + b))) <
      (m * u - p * a) + (m * v - p * b) := by
    nlinarith only [h1, h2]
  rcases le_total (m * v - p * b) (m * u - p * a) with h | h
  · have ht : -(c * (a + b)) ≤ m * u + -(p * a) := by linarith
    have he := Real.exp_le_exp.mpr ht
    rw [Real.exp_add] at he
    linarith
  · have ht : -(c * (a + b)) ≤ m * v + -(p * b) := by linarith
    have he := Real.exp_le_exp.mpr ht
    rw [Real.exp_add] at he
    linarith

/-- Actual nonnegative extended products exhaust the pole cases without ∞−∞. -/
theorem multiplierWeight_le_sum_add_ratios {c q p m : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hp : 0 < p) (hm : 0 < m)
    (hgap : 2 * c ≤ p - m * c / q) {a b u v : EReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    multiplierWeight c (a + b) ≤ multiplierWeight q (u + v) + 1 +
      EReal.exp ((m : EReal) * u) * multiplierWeight p a +
      EReal.exp ((m : EReal) * v) * multiplierWeight p b := by
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
      | bot => simp [multiplierWeight_bot hp, ENNReal.mul_top heU]
      | top => exact absurd rfl ha
      | coe A =>
        induction b using EReal.rec with
        | bot => simp [multiplierWeight_bot hp, ENNReal.mul_top heV]
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
          exact ENNReal.ofReal_le_ofReal (real_exp_le_sum_add_ratios hc hq hm hgap A B U V)

end

end SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapWeightBound
