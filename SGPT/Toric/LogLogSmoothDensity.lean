import SGPT.Toric.TropicalHessian
import SGPT.Toric.ProjectiveLineFubiniStudy

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

/-- The original scalar function in the genuine one-dimensional Euclidean coordinate. -/
def scalarTropicalProfile (h : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 1)) : ℝ := h (x 0)

theorem contDiff_scalarTropicalProfile {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (scalarTropicalProfile h) := by
  exact hh.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff

/-- Reuse the true affine Hessian chain rule on arbitrary original Euclidean vectors. -/
theorem realHessian_scalarTropicalProfile {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (x v w : EuclideanSpace ℝ (Fin 1)) :
    realHessian (scalarTropicalProfile h) x v w = realHessian h (x 0) (v 0) (w 0) := by
  have H := realHessian_comp_affine hh
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0) 0 x v w
  unfold scalarTropicalProfile
  simpa using H

/-- The actual one-entry source Hessian is the original scalar second derivative. -/
theorem tropicalHessianEntry_scalarTropicalProfile {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (x : EuclideanSpace ℝ (Fin 1)) :
    tropicalHessianEntry (scalarTropicalProfile h) x 0 0 = realHessian h (x 0) 1 1 := by
  rw [tropicalHessianEntry, realHessian_scalarTropicalProfile hh]
  simp [EuclideanSpace.basisFun_apply]

/-- The complete normalized source tropical form specializes on arbitrary real vectors. -/
theorem smoothDDC_scalarTropicalProfile {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {z : ComplexModel 1} (hz : z 0 ≠ 0) (v w : ComplexModel 1) :
    smoothDDC (fun y => h (tropicalization y 0)) z ![v, w] =
      realHessian h (Real.log (Complex.normSq (z 0))) 1 1 *
        ((v 0 / z 0).re * (w 0 / z 0).im -
          (w 0 / z 0).re * (v 0 / z 0).im) / Real.pi := by
  have htorus : z ∈ complexTorus 1 := by
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hi] using hz
  have hf := contDiff_scalarTropicalProfile hh
  change smoothDDC (fun y => scalarTropicalProfile h (tropicalization y)) z ![v, w] = _
  rw [smoothDDC_tropicalization_coordinate_sum hf htorus]
  simp only [Fin.sum_univ_one]
  rw [tropicalHessianEntry_scalarTropicalProfile (hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    tropicalization_apply_eq_log_norm_sq, ← Complex.normSq_eq_norm_sq]

/-- The actual original orthonormal 1,i coefficient has the exact squared-log density. -/
theorem smoothDDC_scalarTropicalProfile_standard {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    smoothDDC (fun y => h (tropicalization y 0)) z
        ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I] =
      realHessian h (Real.log (Complex.normSq (z 0))) 1 1 /
        (Real.pi * Complex.normSq (z 0)) := by
  rw [smoothDDC_scalarTropicalProfile hh hz]
  simp only [projectiveModelEquiv_apply_zero, div_eq_mul_inv,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub]
  have hn : ((z 0)⁻¹).re * ((z 0)⁻¹).re + ((z 0)⁻¹).im * ((z 0)⁻¹).im =
      (Complex.normSq (z 0))⁻¹ := by
    rw [← Complex.normSq_apply, Complex.normSq_inv]
  have he : ((z 0)⁻¹).re * ((z 0)⁻¹).re - -(((z 0)⁻¹).im) * ((z 0)⁻¹).im =
      (Complex.normSq (z 0))⁻¹ := by
    linarith
  rw [he]
  simp only [mul_inv_rev]
  ring

end SGPT.Toric
