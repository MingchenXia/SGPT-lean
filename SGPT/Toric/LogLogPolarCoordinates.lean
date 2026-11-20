import SGPT.Toric.LogLogRadialMeasure

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

/-- The actual squared-log point is exactly the genuine polar inverse. -/
theorem logLogRadialPoint_eq_polarCoord (x t : ℝ) :
    logLogRadialPoint (x, t) = Complex.polarCoord.symm (Real.exp (x / 2), t) := by
  rw [logLogRadialPoint, Complex.exp_add, Complex.exp_ofReal_mul_I,
    Complex.polarCoord_symm_apply]
  rw [Complex.ofReal_exp]

/-- Positive original polar radii have precisely the original squared-log coordinate. -/
theorem polarCoord_symm_eq_logLogRadialPoint {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Complex.polarCoord.symm (r, t) = logLogRadialPoint (2 * Real.log r, t) := by
  rw [logLogRadialPoint_eq_polarCoord]
  rw [show 2 * Real.log r / 2 = Real.log r by ring, Real.exp_log hr]

/-- The squared-log evaluation is literal, with the source factor two. -/
theorem log_normSq_polarCoord_symm {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Real.log (Complex.normSq (Complex.polarCoord.symm (r, t))) = 2 * Real.log r := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, abs_of_pos hr,
    Real.log_pow]
  norm_num

/-- Actual polar Jacobian cancellation on the full normalized scalar coefficient. -/
theorem polarJacobian_scalarDensity (ρ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    r * (ρ (Real.log (Complex.normSq (Complex.polarCoord.symm (r, t)))) /
      (Real.pi * Complex.normSq (Complex.polarCoord.symm (r, t)))) =
      ρ (2 * Real.log r) / (Real.pi * r) := by
  rw [log_normSq_polarCoord_symm hr, Complex.normSq_eq_norm_sq,
    Complex.norm_polarCoord_symm, abs_of_pos hr]
  field_simp [hr.ne', Real.pi_ne_zero]

end SGPT.Toric
