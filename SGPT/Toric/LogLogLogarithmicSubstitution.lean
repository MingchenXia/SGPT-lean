import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory

private theorem positive_log_image : Real.log '' Ioi (0 : ℝ) = univ := by
  apply eq_univ_of_forall
  intro x
  exact ⟨Real.exp x, Real.exp_pos x, Real.log_exp x⟩

/-- Actual Jacobian and Haar substitution give the literal squared-log factor. -/
theorem integral_squaredLog_substitution (F : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r⁻¹ * F (2 * Real.log r)) =
      (2 : ℝ)⁻¹ * ∫ x : ℝ, F x := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := Real.log) (f' := fun r => r⁻¹)
    measurableSet_Ioi (fun r hr => (Real.hasDerivAt_log hr.ne').hasDerivWithinAt)
    Real.log_injOn_pos (fun x => F (2 * x))
  rw [positive_log_image, setIntegral_univ] at H
  calc
    (∫ r in Ioi (0 : ℝ), r⁻¹ * F (2 * Real.log r)) =
        ∫ r in Ioi (0 : ℝ), |r⁻¹| • F (2 * Real.log r) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change r⁻¹ * F (2 * Real.log r) = |r⁻¹| • F (2 * Real.log r)
      rw [abs_of_pos (inv_pos.mpr hr), smul_eq_mul]
    _ = ∫ x : ℝ, F (2 * x) := H.symm
    _ = (2 : ℝ)⁻¹ * ∫ x : ℝ, F x := by
      simpa [smul_eq_mul] using Measure.integral_comp_mul_left F (2 : ℝ)

/-- Genuine integrability is preserved by the entire positive-radius substitution. -/
theorem integrableOn_squaredLog_substitution_iff (F : ℝ → ℝ) :
    IntegrableOn (fun r => r⁻¹ * F (2 * Real.log r)) (Ioi (0 : ℝ)) ↔
      Integrable F := by
  have H := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := Real.log) (f' := fun r => r⁻¹)
    measurableSet_Ioi (fun r hr => (Real.hasDerivAt_log hr.ne').hasDerivWithinAt)
    Real.log_injOn_pos (fun x => F (2 * x))
  rw [positive_log_image, integrableOn_univ] at H
  have heq : EqOn (fun r => r⁻¹ * F (2 * Real.log r))
      (fun r => |r⁻¹| • F (2 * Real.log r)) (Ioi (0 : ℝ)) := by
    intro r hr
    change r⁻¹ * F (2 * Real.log r) = |r⁻¹| • F (2 * Real.log r)
    rw [abs_of_pos (inv_pos.mpr hr), smul_eq_mul]
  exact (integrableOn_congr_fun heq measurableSet_Ioi).trans
    (H.symm.trans (integrable_comp_mul_left_iff F (by norm_num : (2 : ℝ) ≠ 0)))

end SGPT.Toric
