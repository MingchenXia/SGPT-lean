import SGPT.Bergman.SourcePolynomialLocalBound

/-!
# PolynomialPointEstimate

Local point estimate `|f(z)|² e^{-kψ(z)} ≤ C kⁿ ∫ |f|² e^{-kψ}` for holomorphic `f` (step for `h⁰ = O(kⁿ)`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology ContDiff ENNReal

variable {n : ℕ}

/-- Genuine local polynomial holomorphic point estimate. All constants and
the inner neighborhood precede ALL positive k, ALL holomorphic F and ALL a.
No desired point estimate, local gauge, Taylor certificate or dimension bound
is an incoming hypothesis. Actual infinite integrals remain meaningful. -/
theorem exists_local_polynomial_point_bound {U : Set (ComplexModel n)} (hU : IsOpen U)
    {y : ComplexModel n} (hy : y ∈ U) {p q g : ComplexModel n → ℝ}
    (hp : ContDiffOn ℝ 2 p U) (hq : ContDiffOn ℝ 2 q U)
    (hg : ContinuousAt g y) (hgpos : 0 < g y) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ball y r ⊆ U ∧
      ∀ k : ℕ, 0 < k → ∀ F : ComplexModel n → ℂ,
        DifferentiableOn ℂ F U → ∀ a ∈ ball y r,
          ENNReal.ofReal (‖F a‖ ^ 2 * Real.exp (degreePotential p q k a)) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ n) *
              ∫⁻ z in U, ENNReal.ofReal (‖F z‖ ^ 2 *
                Real.exp (degreePotential p q k z) * g z) := by
  obtain ⟨r, c, B, hr, hc, _hB, hlocal⟩ :=
    exists_local_polynomial_data hU hy hp hq hg hgpos
  let V := (volume (ball (0 : ComplexModel n) r)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : ComplexModel n) hr).ne' measure_ball_lt_top.ne
  have hVread : ENNReal.ofReal V = volume (ball (0 : ComplexModel n) r) :=
    ENNReal.ofReal_toReal measure_ball_lt_top.ne
  let A := Real.exp B / c
  let C := V⁻¹ * A
  have hA : 0 < A := div_pos (Real.exp_pos _) hc
  have hC : 0 < C := mul_pos (inv_pos.mpr hV) hA
  have hball : ball y r ⊆ U := by
    intro a ha
    exact (hlocal 1 one_pos a ha).1 (mem_closedBall_self (polynomialRadius_pos hr one_pos).le)
  refine ⟨r, C, hr, hC, hball, fun k hk F hF a ha => ?_⟩
  let G := holomorphicFirstOrderGauge (degreeDifferential p q k a)
    (degreePotential p q k a) a F
  have hG : DifferentiableOn ℂ G U := holomorphicFirstOrderGauge_differentiableOn _ _ _ hF
  have hδ := polynomialRadius_pos hr hk
  have hsub := (hlocal k hk a ha).1
  have hpoint := lintegral_ball_normSq_ge hU hG hδ hsub
  have hdom (z : ComplexModel n) (hz : z ∈ ball a (polynomialRadius r k)) :
      ‖G z‖ ^ 2 ≤ A * (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) := by
    have hzdata := (hlocal k hk a ha).2 z (ball_subset_closedBall hz)
    rw [holomorphicFirstOrderGauge_norm_sq]
    have hexp := Real.exp_le_exp.mpr hzdata.2
    calc
      _ ≤ ‖F z‖ ^ 2 * Real.exp (degreePotential p q k z + B) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = ‖F z‖ ^ 2 * (Real.exp (degreePotential p q k z) * Real.exp B) := by rw [Real.exp_add]
      _ ≤ A * (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) := by
        dsimp only [A]
        rw [show Real.exp B / c * (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) =
          (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * Real.exp B * g z) / c by ring]
        apply (le_div_iff₀ hc).mpr
        have h := mul_le_mul_of_nonneg_left hzdata.1
          (mul_nonneg (mul_nonneg (sq_nonneg ‖F z‖)
            (Real.exp_pos (degreePotential p q k z)).le) (Real.exp_pos B).le)
        convert h using 1; ring
  have hI : (∫⁻ z in ball a (polynomialRadius r k), ENNReal.ofReal (‖G z‖ ^ 2)) ≤
      ENNReal.ofReal A * ∫⁻ z in U,
        ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) := by
    calc
      _ ≤ ∫⁻ z in ball a (polynomialRadius r k), ENNReal.ofReal A *
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) := by
        apply setLIntegral_mono' measurableSet_ball
        intro z hz
        rw [← ENNReal.ofReal_mul hA.le]
        exact ENNReal.ofReal_le_ofReal (hdom z hz)
      _ = ENNReal.ofReal A * ∫⁻ z in ball a (polynomialRadius r k),
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
        gcongr
        exact ball_subset_closedBall.trans hsub
  have hm := hpoint.trans hI
  rw [holomorphicFirstOrderGauge_center] at hm
  have hscaled := mul_le_mul' (le_refl (ENNReal.ofReal ((k : ℝ) ^ n))) hm
  rw [← mul_assoc, polynomialRadius_ball_volume n a hk] at hscaled
  have hcancel : ENNReal.ofReal V⁻¹ * volume (ball (0 : ComplexModel n) r) = 1 := by
    rw [← hVread, ← ENNReal.ofReal_mul (inv_pos.mpr hV).le, inv_mul_cancel₀ hV.ne',
      ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal V⁻¹ * (volume (ball (0 : ComplexModel n) r) *
        ENNReal.ofReal (‖F a‖ ^ 2 * Real.exp (degreePotential p q k a))) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal V⁻¹ * (ENNReal.ofReal ((k : ℝ) ^ n) *
        (ENNReal.ofReal A * ∫⁻ z in U,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (degreePotential p q k z) * g z))) :=
      mul_le_mul' le_rfl hscaled
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hV).le,
        ← ENNReal.ofReal_mul (mul_nonneg (inv_pos.mpr hV).le (pow_nonneg (Nat.cast_nonneg _) _))]
      congr 2
      dsimp only [C]
      ring

end SGPT.Bergman.PolynomialH0Growth
