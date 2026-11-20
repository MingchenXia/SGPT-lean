import SGPT.Foundations.Schemes.ProjectiveFubiniStudyMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # The genuine logarithmic Fubini–Study potential

The second derivative below is the native iterated Fréchet derivative.
Intrinsic logarithmic Hessian proof patterns were inspected in the sibling
LeviForm/LogLevi modules and reconstructed here using only Mathlib and this
project's literal Euclidean sums.
-/

open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false

def realSecondDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v w : E) : ℝ := iteratedFDeriv ℝ 2 u x ![v, w]

theorem realSecondDerivative_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v w : E) :
    realSecondDerivative u x v w = fderiv ℝ (fderiv ℝ u) x v w := by
  simp [realSecondDerivative, iteratedFDeriv_two_apply]

theorem realSecondDerivative_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (x v w : E) : realSecondDerivative (fun _ : E => c) x v w = 0 := by
  simp [realSecondDerivative, iteratedFDeriv_const_of_ne two_ne_zero]

theorem realSecondDerivative_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    realSecondDerivative (u + v) x a b = realSecondDerivative u x a b + realSecondDerivative v x a b := by
  simp [realSecondDerivative, iteratedFDeriv_add_apply hu hv]

theorem realSecondDerivative_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (c : ℝ) (a b : E) :
    realSecondDerivative (c • u) x a b = c * realSecondDerivative u x a b := by
  simp [realSecondDerivative, iteratedFDeriv_const_smul_apply hu]

theorem realSecondDerivative_comp_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (A : F →L[ℝ] E) (x a b : F) :
    realSecondDerivative (fun y => u (A y)) x a b = realSecondDerivative u (A x) (A a) (A b) := by
  have h := congrArg (fun B => B ![a, b]) (A.iteratedFDeriv_comp_right hu x (i := 2) le_rfl)
  have hvec : (fun i => A (![a, b] i)) = ![A a, A b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [realSecondDerivative, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hvec] using h

theorem realSecondDerivative_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x a b : H) : realSecondDerivative (fun y : H => ‖y‖ ^ 2) x a b = 2 * inner ℝ a b := by
  rw [realSecondDerivative_eq_fderiv, fderiv_norm_sq,
    fderiv_const_smul (innerSL ℝ).differentiableAt]
  simp
  rfl

theorem realSecondDerivative_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hzero : ∀ x, f x ≠ 0) (x v w : E) :
    realSecondDerivative (fun y => Real.log (f y)) x v w =
      realSecondDerivative f x v w / f x -
        (fderiv ℝ f x v * fderiv ℝ f x w) / (f x) ^ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hfirst : fderiv ℝ (fun y => Real.log (f y)) = fun y => (f y)⁻¹ • fderiv ℝ f y :=
    funext (fun y => fderiv.log (hd y) (hzero y))
  have hi : HasFDerivAt (fun y => (f y)⁻¹) (-(f x ^ 2)⁻¹ • fderiv ℝ f x) x := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv (hzero x)).comp_hasFDerivAt x (hd x).hasFDerivAt
  rw [realSecondDerivative_eq_fderiv, hfirst]
  change (fderiv ℝ ((fun y => (f y)⁻¹) • fderiv ℝ f) x) v w = _
  rw [(hi.smul hD.hasFDerivAt).fderiv]
  simp only [realSecondDerivative_eq_fderiv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem realSecondDerivative_log_norm_sq_add_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x v w : H) :
    realSecondDerivative (fun y : H => Real.log (‖y‖ ^ 2 + 1)) x v w =
      2 * inner ℝ v w / (‖x‖ ^ 2 + 1) -
        4 * inner ℝ x v * inner ℝ x w / (‖x‖ ^ 2 + 1) ^ 2 := by
  have hs : ContDiff ℝ 2 (fun y : H => ‖y‖ ^ 2 + 1) := (contDiff_norm_sq ℝ).add contDiff_const
  have hz : ∀ y : H, ‖y‖ ^ 2 + 1 ≠ 0 := fun y => by positivity
  have hH : realSecondDerivative (fun y : H => ‖y‖ ^ 2 + 1) x v w = 2 * inner ℝ v w := by
    change realSecondDerivative ((fun y : H => ‖y‖ ^ 2) + (fun _ : H => (1 : ℝ))) x v w = _
    rw [realSecondDerivative_add (contDiff_norm_sq ℝ).contDiffAt contDiffAt_const,
      realSecondDerivative_const, add_zero, realSecondDerivative_norm_sq]
  rw [realSecondDerivative_log hs hz, hH]
  simp only [fderiv_add_const, fderiv_norm_sq_apply, smul_apply, innerSL_apply_apply]
  ring

def projectiveFubiniStudyPotential {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  (n + 1 : ℝ) * Real.log (projectiveFubiniStudyDenominator z)

theorem projectiveFubiniStudyPotential_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveFubiniStudyPotential (n := n)) := by
  exact contDiff_const.mul ((projectiveFubiniStudyDenominator_contDiff n).log
    fun z => (projectiveFubiniStudyDenominator_pos z).ne')

theorem projectiveFubiniStudyPotential_realSecondDerivative {n : ℕ} (z v w : Fin n → ℂ) :
    realSecondDerivative projectiveFubiniStudyPotential z v w =
      (n + 1 : ℝ) *
        (2 * (projectiveEuclideanHermitianSum v w).re / projectiveFubiniStudyDenominator z -
          4 * (projectiveEuclideanHermitianSum z v).re * (projectiveEuclideanHermitianSum z w).re /
            projectiveFubiniStudyDenominator z ^ 2) := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) := InnerProductSpace.complexToReal
  let L : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun y => Real.log (‖y‖ ^ 2 + 1)
  have hu : ContDiff ℝ 2 u := ((contDiff_norm_sq ℝ).add contDiff_const).log fun y => by positivity
  have heq : (fun x : Fin n → ℂ => Real.log (projectiveFubiniStudyDenominator x)) = fun x => u (L x) := by
    funext x
    rw [projectiveFubiniStudyDenominator, projectiveEuclideanSquaredNorm_eq_norm_sq]
    exact congrArg Real.log (add_comm 1 _)
  have hs : ContDiffAt ℝ 2 (fun x : Fin n → ℂ => Real.log (projectiveFubiniStudyDenominator x)) z := by
    rw [heq]
    exact (hu.comp L.contDiff).contDiffAt
  change realSecondDerivative ((n + 1 : ℝ) •
    (fun x : Fin n → ℂ => Real.log (projectiveFubiniStudyDenominator x))) z v w = _
  rw [realSecondDerivative_smul hs, heq, realSecondDerivative_comp_linear hu L,
    realSecondDerivative_log_norm_sq_add_one]
  have hi : ∀ a b : Fin n → ℂ, inner ℝ (L a) (L b) = (projectiveEuclideanHermitianSum a b).re := by
    intro a b
    change (inner ℂ (WithLp.toLp 2 a) (WithLp.toLp 2 b)).re = _
    rw [← projectiveEuclideanHermitianSum_eq_inner]
  have hd : ‖L z‖ ^ 2 + 1 = projectiveFubiniStudyDenominator z := by
    rw [projectiveFubiniStudyDenominator, projectiveEuclideanSquaredNorm_eq_norm_sq]
    exact add_comm _ 1
  rw [hi, hi, hi, hd]

theorem projectiveFubiniStudyRealMetric_euclidean_formula {n : ℕ} (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z v w =
      2 * (n + 1 : ℝ) *
        (projectiveFubiniStudyDenominator z * (projectiveEuclideanHermitianSum v w).re -
          ((projectiveEuclideanHermitianSum z v).re * (projectiveEuclideanHermitianSum z w).re +
            (projectiveEuclideanHermitianSum z v).im * (projectiveEuclideanHermitianSum z w).im)) /
          projectiveFubiniStudyDenominator z ^ 2 := by
  have hc : (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [projectiveFubiniStudyRealMetric, projectiveFubiniStudyHermitian,
    ← projectiveEuclideanHermitianSum_conj_symm z v, hc, ← Complex.ofReal_pow,
    Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.sub_re,
    Complex.re_ofReal_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The actual metric is the imaginary-invariant average of the genuine potential Hessian. -/
theorem projectiveFubiniStudyRealMetric_eq_potentialHessian {n : ℕ} (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z v w =
      (realSecondDerivative projectiveFubiniStudyPotential z v w +
        realSecondDerivative projectiveFubiniStudyPotential z (Complex.I • v) (Complex.I • w)) / 2 := by
  have hB : projectiveEuclideanHermitianSum (Complex.I • v) (Complex.I • w) =
      projectiveEuclideanHermitianSum v w := by
    rw [projectiveEuclideanHermitianSum_smul_left, projectiveEuclideanHermitianSum_smul_right]
    simp [Complex.conj_I, ← mul_assoc]
  have hv : (projectiveEuclideanHermitianSum z (Complex.I • v)).re =
      -(projectiveEuclideanHermitianSum z v).im := by
    rw [projectiveEuclideanHermitianSum_smul_right, Complex.I_mul_re]
  have hw : (projectiveEuclideanHermitianSum z (Complex.I • w)).re =
      -(projectiveEuclideanHermitianSum z w).im := by
    rw [projectiveEuclideanHermitianSum_smul_right, Complex.I_mul_re]
  rw [projectiveFubiniStudyRealMetric_euclidean_formula,
    projectiveFubiniStudyPotential_realSecondDerivative,
    projectiveFubiniStudyPotential_realSecondDerivative, hB, hv, hw]
  field_simp [(projectiveFubiniStudyDenominator_pos z).ne']
  ring

/-- The metric's actual fundamental form is twice the imaginary part of the literal Hermitian form. -/
theorem projectiveFubiniStudyRealMetric_imaginary_left {n : ℕ} (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z (Complex.I • v) w =
      2 * (projectiveFubiniStudyHermitian z v w).im := by
  rw [projectiveFubiniStudyRealMetric, projectiveFubiniStudyHermitian_smul_left]
  simp [Complex.conj_I, Complex.mul_re]

theorem realSecondDerivative_neg_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v w : E) : realSecondDerivative u x (-v) w = -realSecondDerivative u x v w := by
  simp [realSecondDerivative_eq_fderiv]

theorem realSecondDerivative_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    realSecondDerivative u x v w = realSecondDerivative u x w v := by
  rw [realSecondDerivative_eq_fderiv, realSecondDerivative_eq_fderiv]
  exact (hu.isSymmSndFDerivAt (by simp)).eq v w

/-- The actual fundamental form is the antisymmetrized second derivative of the literal potential. -/
theorem projectiveFubiniStudyRealMetric_imaginary_left_eq_potentialHessian {n : ℕ}
    (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z (Complex.I • v) w =
      -(realSecondDerivative projectiveFubiniStudyPotential z v (Complex.I • w) -
        realSecondDerivative projectiveFubiniStudyPotential z w (Complex.I • v)) / 2 := by
  rw [projectiveFubiniStudyRealMetric_eq_potentialHessian]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, realSecondDerivative_neg_left]
  have hs : ContDiffAt ℝ 2 projectiveFubiniStudyPotential z :=
    (projectiveFubiniStudyPotential_contDiff n).contDiffAt.of_le
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [realSecondDerivative_symm hs (Complex.I • v) w]
  ring

end

end SGPT.Foundations.Schemes
