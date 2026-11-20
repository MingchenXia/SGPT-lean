import SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence

set_option autoImplicit false

/-! # Actual weighted holomorphic mean-value estimates -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticWeightedMeanValue

open FirstPass

noncomputable section

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- The genuine holomorphic ball submean controls a point value by its
actual weighted integral, with poles and infinite integrals retained. -/
theorem volume_mul_norm_sq_le_weighted_lintegral
    {B : Set (ComplexModel n)} (hB : IsOpen B) {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h B) {P : ComplexModel n → EReal}
    {q : ℝ} (hq : 0 < q) {y : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall y r ⊆ B) {b : ℝ} (hb : ∀ z ∈ ball y r, P z ≤ b) :
    volume (ball y r) * ENNReal.ofReal (‖h y‖ ^ 2) ≤
      ENNReal.ofReal (Real.exp (q * b)) *
        ∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z) := by
  have hmv := lintegral_ball_normSq_ge hB hh hr hsub
  have hw (z : ComplexModel n) (hz : z ∈ ball y r) :
      ENNReal.ofReal (‖h z‖ ^ 2) ≤ ENNReal.ofReal (Real.exp (q * b)) *
        (ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) := by
    have hlow : ENNReal.ofReal (Real.exp (-(q * b))) ≤ multiplierWeight q (P z) := by
      rw [← multiplierWeight_coe]
      exact multiplierWeight_antitone hq.le (hb z hz)
    calc ENNReal.ofReal (‖h z‖ ^ 2)
        = ENNReal.ofReal (Real.exp (q * b)) * ENNReal.ofReal (Real.exp (-(q * b))) *
          ENNReal.ofReal (‖h z‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
              add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (q * b)) * multiplierWeight q (P z) *
          ENNReal.ofReal (‖h z‖ ^ 2) := by gcongr
      _ = _ := by ring
  refine hmv.trans ?_
  calc (∫⁻ z in ball y r, ENNReal.ofReal (‖h z‖ ^ 2))
      ≤ ∫⁻ z in ball y r, ENNReal.ofReal (Real.exp (q * b)) *
          (ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) :=
        setLIntegral_mono' measurableSet_ball hw
    _ = ENNReal.ofReal (Real.exp (q * b)) *
          ∫⁻ z in ball y r, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      gcongr
      exact ball_subset_closedBall.trans hsub

/-- Finiteness of the actual weighted integral and internally positive
finite Haar ball volume give a genuine finite real pointwise bound. -/
theorem norm_sq_le_weighted_lintegral_toReal_div_volume
    {B : Set (ComplexModel n)} (hB : IsOpen B) {h : ComplexModel n → ℂ}
    (hh : DifferentiableOn ℂ h B) {P : ComplexModel n → EReal}
    {q : ℝ} (hq : 0 < q) {y : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall y r ⊆ B) {b : ℝ} (hb : ∀ z ∈ ball y r, P z ≤ b)
    (hfinite : (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤) :
    ‖h y‖ ^ 2 ≤ Real.exp (q * b) *
      (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)).toReal /
      (volume (ball y r)).toReal := by
  have hvol : 0 < (volume (ball y r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume y hr).ne' measure_ball_lt_top.ne
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (volume_mul_norm_sq_le_weighted_lintegral hB hh hq hr hsub hb)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  apply (le_div_iff₀ hvol).mpr
  simpa only [mul_comm (‖h y‖ ^ 2)] using hreal

end

end SGPT.Foundations.Analysis.Pending.AnalyticWeightedMeanValue
