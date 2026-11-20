import SGPT.Convex.HalfLine
import SGPT.Convex.SmoothAlexandrov
import SGPT.Foundations.Analysis.LeviForm
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory SGPT.Convex SGPT.Foundations.Analysis
open scoped ContDiff RealInnerProductSpace

/-- The actual scalar multiplication perfect pairing is the original real inner pairing. -/
theorem scalarPairing_eq_real_inner : scalarPairing = innerₗ ℝ := by
  ext
  simp [scalarPairing]

/-- The genuine singleton orthonormal Hessian determinant is the actual scalar second derivative. -/
theorem det_scalarHessianMatrix (h : ℝ → ℝ) (x : ℝ) :
    (hessianMatrix (OrthonormalBasis.singleton (Fin 1) ℝ) h x).det =
      realHessian h x 1 1 := by
  rw [Matrix.det_fin_one]
  simp [hessianMatrix, realHessian_eq_fderiv]

/-- Original smooth convex hypotheses produce the actual rank-one Alexandrov density. -/
theorem alexandrovMeasure_scalar_eq_withDensity_hessian {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) :
    alexandrovMeasure scalarPairing volume (fun x => (h x : EReal)) =
      volume.withDensity (fun x => ENNReal.ofReal (realHessian h x 1 1)) := by
  have h2 : ContDiff ℝ 2 h :=
    hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd : Differentiable ℝ h := h2.differentiable (by norm_num)
  have hder : ContDiff ℝ 1 (fderiv ℝ h) := h2.fderiv_right (by norm_num)
  have H := alexandrovMeasure_eq_withDensity_det_hessianMatrix (μ := volume)
    (OrthonormalBasis.singleton (Fin 1) ℝ) hc hd hder.locallyLipschitz
  simpa [scalarPairing_eq_real_inner, hessianMatrix, Matrix.det_fin_one,
    realHessian_eq_fderiv] using H

end SGPT.Toric
