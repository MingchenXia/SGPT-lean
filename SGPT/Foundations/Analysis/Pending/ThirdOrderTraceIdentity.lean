import SGPT.Foundations.Analysis.Pending.AubinYauUniformConstants

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The trace identity for the third-order (Calabi) estimate, flat reference metric

For a smooth real `u` on `ℂⁿ` with complex Hessian `H = (u_{jk̄})` positive definite at `x`,
`P = H(x)⁻¹` and `X_i = ∂_i H(x)` (`re_trace_mul_complexHessian_trace`):

  `Δ'(tr H)(x) = ∑ᵢ (log det H)_{iī}(x) + ∑ᵢ Re tr(P X_i* P X_i)`,

where `Δ' f = Re tr(P · Hess_ℂ f)` is the Laplacian of the metric `u_{jk̄}` in flat coordinates and
`tr H = ∑ᵢ u_{iī}`. This is the flat-coordinate form of the `C²` identity used, together with
Calabi's inequality for `S = |∂³u|²_{g'}`, in the third-order estimate
(`pss07-multiplier-krf:page-0008`, "In view of the identity (2.28), we have for A sufficiently large
(Δ − ∂_t)(S + AΔ̂φ) ≥ C₃S − C₄"; elliptic case: `Δ'(S + K tr H) ≥ c S - C`). The last sum is
nonnegative (`re_trace_inv_mul_conjTranspose_mul_nonneg`); it is the `|∂³u|²_{g'}`-term.

TN.4 B5, nonlinear track N4 (a).
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.ThirdOrderTraceIdentity

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet SemiconcaveHessian
  BlockiLocalEstimate AubinYauLocalStep AubinYauUniformConstants

noncomputable section

variable {n : ℕ}

/-- `Re tr(H⁻¹ X* H⁻¹ X) ≥ 0` for positive definite `H`. -/
theorem re_trace_inv_mul_conjTranspose_mul_nonneg {H X : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) : 0 ≤ (H⁻¹ * Xᴴ * H⁻¹ * X).trace.re := by
  classical
  obtain ⟨R, hdet, hHR, -⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hH hH
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hRu
  have hSH : (star R) * H = R⁻¹ := by
    calc (star R) * H = (star R) * H * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * H * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ := by rw [hHR, Matrix.one_mul]
  have hHinv : H⁻¹ = R * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSH, hRR]
  set N : Matrix (Fin n) (Fin n) ℂ := star R * X * R with hN
  have h3 : (H⁻¹ * Xᴴ * H⁻¹ * X).trace = (Nᴴ * N).trace := by
    rw [hHinv, hN]
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [trace_mul_comm R]
    simp only [Matrix.mul_assoc]
  rw [h3, re_trace_conjTranspose_mul_self]
  positivity

variable {u : ComplexModel n → ℝ}

/-- The complex Hessian of `tr H = ∑ᵢ u_{iī}`: `∑ᵢ ∂̄_i ∂_i H`. -/
theorem complexHessian_trace (hu : ContDiff ℝ ∞ u) (x : ComplexModel n) :
    complexHessian (fun y => ∑ i, leviForm u y (coordinateVector i)) x =
      ∑ i, wirtM I (coordinateVector i)
        (fun y => wirtM (-I) (coordinateVector i) (complexHessian u) y) x := by
  have hL : ∀ i, ContDiff ℝ ∞ (fun y => leviForm u y (coordinateVector i)) := fun i =>
    contDiff_leviForm hu _
  have hS : ContDiff ℝ ∞ (fun y => ∑ i, leviForm u y (coordinateVector i)) :=
    ContDiff.sum fun i _ => hL i
  ext a b
  rw [complexHessian_eq_wirt (contDiffAt_two hS x)]
  have hfun : (fun y => ((∑ i, leviForm u y (coordinateVector i) : ℝ) : ℂ)) =
      fun y => ∑ i, (1 : ℂ) * ((leviForm u y (coordinateVector i) : ℝ) : ℂ) := by
    funext y; push_cast; simp
  rw [hfun, wirt_wirt_sum_const_mul (fun i => contDiff_ofReal_comp (hL i)), Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_mul, wirt_wirt_leviForm hu (coordinateVector i) x a b]

/-- **The trace identity** (flat reference): `Δ'(tr H) = ∑ᵢ (log det H)_{iī} + ∑ᵢ Re tr(P X_i* P X_i)`. -/
theorem re_trace_mul_complexHessian_trace (hu : ContDiff ℝ ∞ u) {x : ComplexModel n}
    (hpos : (complexHessian u x).PosDef) :
    ((complexHessian u x)⁻¹ *
        complexHessian (fun y => ∑ i, leviForm u y (coordinateVector i)) x).trace.re =
      ∑ i, leviForm (fun y => Real.log (complexHessian u y).det.re) x (coordinateVector i) +
        ∑ i, ((complexHessian u x)⁻¹ * (wirtM (-I) (coordinateVector i) (complexHessian u) x)ᴴ *
          (complexHessian u x)⁻¹ * wirtM (-I) (coordinateVector i) (complexHessian u) x).trace.re := by
  rw [complexHessian_trace hu x, Matrix.mul_sum, trace_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := leviForm_log_det_complexHessian hu hpos (coordinateVector i)
  rw [wirtM_I_complexHessian hu] at h
  have h' := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.sub_re] at h'
  linarith

end

end SGPT.Foundations.Analysis.Pending.ThirdOrderTraceIdentity
