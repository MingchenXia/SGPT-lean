import SGPT.Trace.OTMarginDatum
import SGPT.PSH.GlobalL2PointWeights
import Mathlib.Analysis.MeanInequalities

/-!
# Weights: powers, the pole weight and the Young–Hölder step

Blueprint `claude-ot3.tex`, node `claude-ot3:holder`.

* `multiplierWeight_eq_rpow`: `e^{-c x} = (e^{-x})^c` in `ℝ≥0∞` (all values of `x`).
* `young_weights`: the pointwise interpolation behind the Hölder estimate on the overlaps:
  for `t > 1` and `a/t + b(1 - 1/t) = r`,
  `d u v^r ≤ d u^t v^a + d v^b` (with `u = e^{-kψ}`, `v = e^{-Λ}`, `d = |S_ν - S_μ|²`).
* `multiplierWeight_poleWeight`: `e^{-k(ψ + rΛ/k)} = e^{-kψ} e^{-rΛ}` for `Λ ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis

/-- `e^{-cx} = (e^{-x})^c` for `c ≥ 0`. -/
theorem multiplierWeight_eq_rpow {c : ℝ} (hc : 0 ≤ c) (x : EReal) :
    multiplierWeight c x = multiplierWeight 1 x ^ c := by
  rcases hc.lt_or_eq with hc | rfl
  · induction x using EReal.rec with
    | bot => rw [multiplierWeight_bot hc, multiplierWeight_bot one_pos, ENNReal.top_rpow_of_pos hc]
    | top => rw [multiplierWeight_top hc, multiplierWeight_top one_pos, ENNReal.zero_rpow_of_pos hc]
    | coe s =>
      rw [multiplierWeight_coe, multiplierWeight_coe, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
        hc.le, ← Real.exp_mul]
      congr 2; ring
  · simp [multiplierWeight]

/-- **Young's inequality for the weights.** -/
theorem young_weights (d u v : ℝ≥0∞) {t a b r : ℝ} (ht : 1 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : a / t + b * (1 - 1 / t) = r) :
    d * u * v ^ r ≤ d * u ^ t * v ^ a + d * v ^ b := by
  have ht0 : 0 < t := by linarith
  set q : ℝ := t / (t - 1) with hq
  have hpq : t.HolderConjugate q := Real.HolderConjugate.conjExponent ht
  have hq1 : 1 / q = 1 - 1 / t := by rw [hq]; field_simp
  have hq0 : 0 < q := hpq.symm.pos
  set X := d * u ^ t * v ^ a with hX
  set Y := d * v ^ b with hY
  have hα : X ^ (1 / t) = d ^ (1 / t) * u * v ^ (a / t) := by
    rw [hX, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _
      (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel ht0.ne',
      ENNReal.rpow_one, mul_one_div]
  have hβ : Y ^ (1 / q) = d ^ (1 - 1 / t) * v ^ (b * (1 - 1 / t)) := by
    rw [hY, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hq1]
  have h1t : 0 ≤ 1 - 1 / t := by
    have : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht.le
    linarith
  have hprod : X ^ (1 / t) * Y ^ (1 / q) = d * u * v ^ r := by
    rw [hα, hβ]
    calc d ^ (1 / t) * u * v ^ (a / t) * (d ^ (1 - 1 / t) * v ^ (b * (1 - 1 / t)))
        = (d ^ (1 / t) * d ^ (1 - 1 / t)) * u * (v ^ (a / t) * v ^ (b * (1 - 1 / t))) := by ring
      _ = d ^ (1 / t + (1 - 1 / t)) * u * v ^ (a / t + b * (1 - 1 / t)) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) h1t,
            ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hb h1t)]
      _ = d * u * v ^ r := by rw [hr, show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring, ENNReal.rpow_one]
  have hyoung := ENNReal.young_inequality (X ^ (1 / t)) (Y ^ (1 / q)) hpq
  rw [hprod, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel ht0.ne',
    one_div_mul_cancel hq0.ne', ENNReal.rpow_one, ENNReal.rpow_one] at hyoung
  refine hyoung.trans (add_le_add ?_ ?_)
  · refine ENNReal.div_le_of_le_mul (le_mul_of_one_le_right zero_le ?_)
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ht.le
  · refine ENNReal.div_le_of_le_mul (le_mul_of_one_le_right zero_le ?_)
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hq, le_div_iff₀ (by linarith)]; linarith

/-- `e^{-k(ψ + (rΛ)/k)} = e^{-kψ} e^{-rΛ}` (the pole weight of `SGPT.PSH.GlobalL2.poleWeight`), for
`ψ < ⊤`, `Λ ≤ 0`, `k, r > 0`. -/
theorem multiplierWeight_poleWeight {X : Type*} {ψ Λ : X → EReal} {k : ℕ} (hk : 0 < k) {r : ℝ}
    (hr : 0 < r) {x : X} (hψ : ψ x ≠ ⊤) (hΛ : Λ x ≤ 0) :
    multiplierWeight (k : ℝ) (SGPT.PSH.GlobalL2.poleWeight ψ (fun y => (r : EReal) * Λ y) k x) =
      multiplierWeight (k : ℝ) (ψ x) * multiplierWeight r (Λ x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold SGPT.PSH.GlobalL2.poleWeight
  beta_reduce
  have hΛt : Λ x ≠ ⊤ := fun h => by rw [h] at hΛ; exact absurd hΛ (by simp)
  induction hL : Λ x using EReal.rec with
  | top => exact absurd hL hΛt
  | bot =>
    have h1 : ((1 / (k : ℝ) : ℝ) : EReal) * ((r : EReal) * ⊥) = ⊥ := by
      rw [EReal.coe_mul_bot_of_pos hr, EReal.coe_mul_bot_of_pos (by positivity)]
    rw [h1, EReal.add_bot, multiplierWeight_bot hk', multiplierWeight_bot hr, ENNReal.mul_top]
    intro h0
    induction hψx : ψ x using EReal.rec with
    | top => exact hψ hψx
    | bot => rw [hψx, multiplierWeight_bot hk'] at h0; exact ENNReal.top_ne_zero h0
    | coe s => rw [hψx, multiplierWeight_coe] at h0; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' h0
  | coe L =>
    have h1 : ((1 / (k : ℝ) : ℝ) : EReal) * ((r : EReal) * (L : EReal)) = ((r * L / k : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul]; congr 1; ring
    rw [h1]
    induction hψx : ψ x using EReal.rec with
    | top => exact absurd hψx hψ
    | bot =>
      rw [EReal.bot_add, multiplierWeight_bot hk', multiplierWeight_coe, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; field_simp; ring

end SGPT.Trace.OTMargin
