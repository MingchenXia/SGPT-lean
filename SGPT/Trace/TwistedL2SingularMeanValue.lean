import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# Uniform point bounds from local holomorphic `L²` bounds

A local uniform square-integral bound for an eventually holomorphic family
implies an eventual uniform point bound on the half-radius ball. This is the
Euclidean mean-value step in the line-bundle Montel argument.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-- An eventually holomorphic family with a single finite `L²` bound on a
ball is uniformly bounded on its half-radius ball. -/
theorem exists_eventually_uniform_norm_bound_of_ball_l2
    {z : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (F : ℕ → ComplexModel n → ℂ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (F j) (ball z R) ∧
      (∫⁻ y in ball z R, ENNReal.ofReal (‖F j y‖ ^ 2)) ≤ C) :
    ∃ A : ℝ, ∀ᶠ j in atTop, ∀ y ∈ ball z (R / 2), ‖F j y‖ ≤ A := by
  set r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel n) r)
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ hr).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set B : ℝ≥0∞ := C / V
  have hBtop : B ≠ ⊤ := ENNReal.div_ne_top hC.ne hV0
  refine ⟨Real.sqrt B.toReal, hF.mono fun j hj y hy => ?_⟩
  have hsub : closedBall y r ⊆ ball z R := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball] at hy ⊢
    dsimp [r] at *
    have htri := dist_triangle x y z
    linarith
  have hmean := lintegral_ball_normSq_ge isOpen_ball hj.1 hr hsub
  rw [Measure.addHaar_ball_center] at hmean
  have hle : ENNReal.ofReal (‖F j y‖ ^ 2) ≤ B := by
    rw [show B = C / V from rfl,
      ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)]
    calc ENNReal.ofReal (‖F j y‖ ^ 2) * V =
        V * ENNReal.ofReal (‖F j y‖ ^ 2) := mul_comm _ _
      _ ≤ ∫⁻ x in ball y r, ENNReal.ofReal (‖F j x‖ ^ 2) := hmean
      _ ≤ ∫⁻ x in ball z R, ENNReal.ofReal (‖F j x‖ ^ 2) :=
        lintegral_mono_set (ball_subset_closedBall.trans hsub)
      _ ≤ C := hj.2
  have hsq : ‖F j y‖ ^ 2 ≤ B.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle
  exact Real.le_sqrt_of_sq_le hsq

end SGPT.Trace.TwistedL2
