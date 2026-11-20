import SGPT.Foundations.Schemes.ProjectiveFubiniStudyPotential
import SGPT.Foundations.Schemes.ProjectiveRatioDifferential
import SGPT.Foundations.Schemes.SchemeComplexStructure
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! # The actual closed coordinate Fubini–Study two-form

The one-form is the native real differential of the actual logarithmic
potential composed with multiplication by I. Its exterior derivative is
the actual fundamental two-form of the previously constructed metric.
The intrinsic Fin-two exterior derivative calculation was inspected in
a sibling source and reconstructed here with only Mathlib and our data.
-/

open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false

def projectiveFubiniStudyDcPotential (n : ℕ) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    ((-1 / 2 : ℝ) • (fderiv ℝ projectiveFubiniStudyPotential z).comp (smoothComplexModelJ n))

theorem projectiveFubiniStudyDcPotential_apply (n : ℕ) (z : Fin n → ℂ)
    (v : Fin 1 → (Fin n → ℂ)) :
    projectiveFubiniStudyDcPotential n z v =
      (-1 / 2 : ℝ) * fderiv ℝ projectiveFubiniStudyPotential z (Complex.I • v 0) := rfl

theorem projectiveFubiniStudyDcPotential_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveFubiniStudyDcPotential n) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (projectiveFubiniStudyPotential (n := n))) :=
    (projectiveFubiniStudyPotential_contDiff n).fderiv_right (by simp)
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Fin n → ℂ) (F := ℝ) (0 : Fin 1)).contDiff.comp
      ((hD.clm_comp contDiff_const).const_smul (-1 / 2 : ℝ))

def projectiveFubiniStudyCoordinateForm (n : ℕ) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  extDeriv (projectiveFubiniStudyDcPotential n) z

theorem projectiveFubiniStudyCoordinateForm_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (projectiveFubiniStudyCoordinateForm n) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin n → ℂ) ℝ).contDiff.comp
    ((projectiveFubiniStudyDcPotential_contDiff n).fderiv_right (by simp))

theorem projectiveFubiniStudyCoordinateForm_hessian (n : ℕ) (z v w : Fin n → ℂ) :
    projectiveFubiniStudyCoordinateForm n z ![v, w] =
      -(realSecondDerivative projectiveFubiniStudyPotential z v (Complex.I • w) -
        realSecondDerivative projectiveFubiniStudyPotential z w (Complex.I • v)) / 2 := by
  have hu : ContDiffAt ℝ 2 projectiveFubiniStudyPotential z :=
    (projectiveFubiniStudyPotential_contDiff n).contDiffAt.of_le
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  unfold projectiveFubiniStudyCoordinateForm
  rw [extDeriv_apply ((projectiveFubiniStudyDcPotential_contDiff n).differentiable
    (by simp) z)]
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.removeNth_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, projectiveFubiniStudyDcPotential_apply]
  have htail : Fin.tail ![v, w] 0 = w := rfl
  have hremove : Fin.removeNth 1 ![v, w] 0 = v := rfl
  rw [htail, hremove]
  norm_num
  have hfd : DifferentiableAt ℝ (fderiv ℝ projectiveFubiniStudyPotential) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv : DifferentiableAt ℝ
      (fun y => fderiv ℝ projectiveFubiniStudyPotential y (Complex.I • v)) z := by fun_prop
  have hw : DifferentiableAt ℝ
      (fun y => fderiv ℝ projectiveFubiniStudyPotential y (Complex.I • w)) z := by fun_prop
  rw [fderiv_const_mul hw (1 / 2), fderiv_const_mul hv (1 / 2),
    fderiv_clm_apply hfd (differentiableAt_const (c := Complex.I • w)),
    fderiv_clm_apply hfd (differentiableAt_const (c := Complex.I • v))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, smul_apply,
    ContinuousLinearMap.flip_apply, realSecondDerivative_eq_fderiv]
  ring

/-- The actual exterior derivative is the metric's genuine fundamental form. -/
theorem projectiveFubiniStudyCoordinateForm_apply (n : ℕ) (z v w : Fin n → ℂ) :
    projectiveFubiniStudyCoordinateForm n z ![v, w] =
      projectiveFubiniStudyRealMetric z (Complex.I • v) w := by
  rw [projectiveFubiniStudyCoordinateForm_hessian,
    projectiveFubiniStudyRealMetric_imaginary_left_eq_potentialHessian]

/-- Genuine native exterior differentiation vanishes, by d squared equals zero. -/
theorem projectiveFubiniStudyCoordinateForm_closed (n : ℕ) (z : Fin n → ℂ) :
    extDeriv (projectiveFubiniStudyCoordinateForm n) z = 0 :=
  extDeriv_extDeriv_apply (projectiveFubiniStudyDcPotential_contDiff n).contDiffAt
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem projectiveRatioTransition_real_fderiv_commutes_J (n : ℕ) (i j : Fin (n + 1))
    (z v : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    fderiv ℝ (projectiveRatioTransition n i j) z (Complex.I • v) =
      Complex.I • fderiv ℝ (projectiveRatioTransition n i j) z v := by
  rw [projectiveRatioTransition_real_fderiv n i j z u hu]
  change projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u
      (Complex.I • v) = _
  exact map_smul _ _ _

theorem projectiveFubiniStudyCoordinateForm_ratio_covariance (n : ℕ) (i j : Fin (n + 1))
    (z v w : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    projectiveFubiniStudyCoordinateForm n (projectiveRatioTransition n i j z)
      ![fderiv ℝ (projectiveRatioTransition n i j) z v,
        fderiv ℝ (projectiveRatioTransition n i j) z w] =
      projectiveFubiniStudyCoordinateForm n z ![v, w] := by
  rw [projectiveFubiniStudyCoordinateForm_apply, projectiveFubiniStudyCoordinateForm_apply,
    ← projectiveRatioTransition_real_fderiv_commutes_J n i j z v u hu]
  exact projectiveRatioTransition_metric_real_fderiv n i j z (Complex.I • v) w u hu

/-- The actual alternating tensors transform by pullback of the actual derivative. -/
theorem projectiveFubiniStudyCoordinateForm_ratio_pullback (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    (projectiveFubiniStudyCoordinateForm n (projectiveRatioTransition n i j z)).compContinuousLinearMap
      (fderiv ℝ (projectiveRatioTransition n i j) z) = projectiveFubiniStudyCoordinateForm n z := by
  ext v
  have hv : v = ![v 0, v 1] := by ext a; fin_cases a <;> rfl
  rw [hv]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  have hm : (fun a => fderiv ℝ (projectiveRatioTransition n i j) z (![v 0, v 1] a)) =
      ![fderiv ℝ (projectiveRatioTransition n i j) z (v 0),
        fderiv ℝ (projectiveRatioTransition n i j) z (v 1)] := by
    ext a; fin_cases a <;> rfl
  rw [hm]
  exact projectiveFubiniStudyCoordinateForm_ratio_covariance n i j z (v 0) (v 1) u hu

theorem projectiveFubiniStudyCoordinateForm_complex_diagonal (n : ℕ) (z v : Fin n → ℂ) :
    projectiveFubiniStudyCoordinateForm n z ![v, Complex.I • v] =
      projectiveFubiniStudyRealMetric z v v := by
  rw [projectiveFubiniStudyCoordinateForm_apply, projectiveFubiniStudyRealMetric_imaginary n]

theorem projectiveFubiniStudyCoordinateForm_complex_diagonal_pos (n : ℕ) (z v : Fin n → ℂ)
    (hv : v ≠ 0) : 0 < projectiveFubiniStudyCoordinateForm n z ![v, Complex.I • v] := by
  rw [projectiveFubiniStudyCoordinateForm_complex_diagonal]
  exact projectiveFubiniStudyRealMetric_pos z v hv

end

end SGPT.Foundations.Schemes
