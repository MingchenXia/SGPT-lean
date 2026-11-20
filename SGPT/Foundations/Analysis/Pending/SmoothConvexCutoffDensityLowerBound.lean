import SGPT.Foundations.Analysis.Pending.SmoothMax
import SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant

set_option autoImplicit false

/-! The genuine positive chain-rule remainder and native determinant lower
bound for the fixed smooth convex cutoff. Full mathematics precedes Lean.
All dimensions, including empty matrices, are retained without division by n.
No remainder/density inequality certificate is an input. -/

noncomputable section
open scoped Topology ContDiff ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.SmoothConvexCutoffDensityLowerBound
open FirstPass FirstPass.MongeAmpere SmoothMax

variable {n : ℕ}

/-- The PSD rank-one remainder is supplied by the actual scalar chain rule. -/
theorem hessian_cutoff_sub_weight_posSemidef
    {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (b : ℝ) :
    (complexHessian (fun w => b + SmoothMax.posPart (f w - b)) z -
      trans (f z - b) • complexHessian f z).PosSemidef := by
  let φ : ℝ → ℝ := fun s => b + SmoothMax.posPart (s + (-b))
  have hφ : ContDiff ℝ ∞ φ :=
    contDiff_const.add (contDiff_posPart.comp (contDiff_id.add contDiff_const))
  have hdφ : deriv φ = fun s => trans (s + (-b)) := by
    funext s
    exact (((SmoothMax.hasDerivAt_posPart (s + (-b))).comp_add_const s (-b)).const_add b).deriv
  have hsecond : 0 ≤ deriv (fun s => trans (s + (-b))) (f z) :=
    Monotone.deriv_nonneg fun s t hst => trans_monotone (by linarith)
  have heq : (fun w => b + SmoothMax.posPart (f w - b)) = φ ∘ f := by
    funext w
    simp only [φ, Function.comp_def, sub_eq_add_neg]
  rw [heq, complexHessian_comp hφ hf, hdφ]
  have hrem : trans (f z + (-b)) • complexHessian f z +
      deriv (fun s => trans (s + (-b))) (f z) •
        Matrix.vecMulVec (delGrad f z) (star (delGrad f z)) -
        trans (f z - b) • complexHessian f z =
      deriv (fun s => trans (s + (-b))) (f z) •
        Matrix.vecMulVec (delGrad f z) (star (delGrad f z)) := by
    simp only [sub_eq_add_neg]
    abel
  rw [hrem]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul hsecond

/-- The true cutoff Hessian has at least the transition-weighted original
native determinant density; the empty dimension case is literal 1 <= 1. -/
theorem weighted_smoothDensity_le_cutoff
    {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hH : (complexHessian f z).PosSemidef) (b : ℝ) :
    trans (f z - b) ^ n * smoothDensity f z ≤
      smoothDensity (fun w => b + SmoothMax.posPart (f w - b)) z := by
  let s := trans (f z - b)
  let A := s • complexHessian f z
  let B := complexHessian (fun w => b + SmoothMax.posPart (f w - b)) z - A
  have hA : A.PosSemidef := hH.smul (trans_nonneg _)
  have hB : B.PosSemidef := hessian_cutoff_sub_weight_posSemidef hf b
  have hdet := MinkowskiDeterminant.re_det_le_re_det_add hA hB
  have hAB : A + B = complexHessian (fun w => b + SmoothMax.posPart (f w - b)) z := by
    dsimp only [B]
    abel
  rw [hAB] at hdet
  have hsm : A = (s : ℂ) • complexHessian f z := by
    ext i j
    simp only [A, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hsm, Matrix.det_smul, Fintype.card_fin] at hdet
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hdet
  have hc : 0 ≤ (n.factorial : ℝ) / Real.pi ^ n :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg Real.pi_pos.le _)
  calc
    _ = ((n.factorial : ℝ) / Real.pi ^ n) *
      (s ^ n * (complexHessian f z).det.re) := by
        simp only [smoothDensity, s]
        ring
    _ ≤ ((n.factorial : ℝ) / Real.pi ^ n) *
      (complexHessian (fun w => b + SmoothMax.posPart (f w - b)) z).det.re :=
        mul_le_mul_of_nonneg_left hdet hc
    _ = _ := rfl

end SGPT.Foundations.Analysis.Pending.SmoothConvexCutoffDensityLowerBound
