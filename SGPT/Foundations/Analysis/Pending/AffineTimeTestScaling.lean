import SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false

/-! # Actual affine Hessian and planar Haar scale cancellation

Independent differential and measure-theoretic adaptation of the smooth-test
step following (4.29) on Xia SGPT page 171. The time Laplacian is the actual
real Hessian trace divided by four. Integrability is proved separately from
the total Bochner integral identity.
-/

open MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.AffineTimeTestScaling

open BedfordTaylorTimeSlot

noncomputable section

/-- The actual Hessian chain rule gives the squared real affine scale, including zero scale. -/
theorem timeLaplacian_comp_affine {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (a : ℝ) (b z : ℂ) :
    timeLaplacian (fun q => ψ (b + a • q)) z = a ^ 2 * timeLaplacian ψ (b + a • z) := by
  have h (v w : ℂ) :
      realHessian (fun q => ψ (b + a • q)) z v w =
        a * (a * realHessian ψ (b + a • z) v w) := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply,
      realHessian_smul_left, realHessian_smul_right] using
      realHessian_comp_affine hψ (a • ContinuousLinearMap.id ℝ ℂ) b z v w
  unfold timeLaplacian
  rw [h, h]
  ring

/-- The genuinely translated inverse-affine test has the inverse squared Laplacian scale. -/
theorem timeLaplacian_comp_inverse_affine {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (δ : ℝ) (b z : ℂ) :
    timeLaplacian (fun q => ψ (δ⁻¹ • (q - b))) z =
      (δ⁻¹) ^ 2 * timeLaplacian ψ (δ⁻¹ • (z - b)) := by
  have hA (q : ℂ) : -(δ⁻¹ • b) + δ⁻¹ • q = δ⁻¹ • (q - b) := by
    rw [smul_sub]
    abel
  simpa only [hA] using timeLaplacian_comp_affine hψ δ⁻¹ (-(δ⁻¹ • b)) z

/-- Nonzero scaling, actual Haar translation and a nonzero constant multiplier transport true integrability both ways. -/
theorem integrable_scaled_affine_iff (H : ℂ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (b : ℂ) :
    Integrable (fun z => (δ⁻¹) ^ 2 * H (δ⁻¹ • (z - b))) volume ↔ Integrable H volume := by
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hδ)))]
  have htrans : Integrable (fun z => H (δ⁻¹ • (z - b))) volume ↔
      Integrable (fun z => H (δ⁻¹ • z)) volume := by
    constructor
    · intro hi
      simpa only [sub_neg_eq_add, add_sub_cancel_right] using hi.comp_sub_right (-b)
    · intro hi
      exact hi.comp_sub_right b
  exact htrans.trans (integrable_comp_smul_iff volume H (inv_ne_zero hδ))

/-- Actual planar Haar area scaling cancels the inverse squared scale. The identity also uses the total integral convention for nonintegrable functions. -/
theorem integral_scaled_affine (H : ℂ → ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ℂ) :
    (∫ z : ℂ, (δ⁻¹) ^ 2 * H (δ⁻¹ • (z - b))) = ∫ z : ℂ, H z := by
  rw [integral_const_mul, integral_sub_right_eq_self (fun z : ℂ => H (δ⁻¹ • z)) b,
    Measure.integral_comp_inv_smul_of_nonneg volume H hδ.le,
    Complex.finrank_real_complex, smul_eq_mul]
  field_simp

/-- Actual signed weighted time pairing and its genuine integrability are preserved by affine transport, without dividing by the Laplacian. -/
theorem timeLaplacian_affine_pairing {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (E : ℂ → ℝ) {δ : ℝ} (hδ : 0 < δ) (b : ℂ) :
    (Integrable (fun z => timeLaplacian (fun q => ψ (δ⁻¹ • (q - b))) z *
        E (δ⁻¹ • (z - b))) volume ↔
      Integrable (fun z => timeLaplacian ψ z * E z) volume) ∧
    (∫ z : ℂ, timeLaplacian (fun q => ψ (δ⁻¹ • (q - b))) z * E (δ⁻¹ • (z - b))) =
      ∫ z : ℂ, timeLaplacian ψ z * E z := by
  simp_rw [timeLaplacian_comp_inverse_affine hψ, mul_assoc]
  exact ⟨integrable_scaled_affine_iff (fun z => timeLaplacian ψ z * E z) hδ.ne' b,
    integral_scaled_affine (fun z => timeLaplacian ψ z * E z) hδ b⟩

end

end SGPT.Foundations.Analysis.Pending.AffineTimeTestScaling
