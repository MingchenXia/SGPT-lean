import SGPT.Foundations.Schemes.ProjectiveFubiniStudyOverlap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Actual Fréchet derivatives of projective quotient coordinates

The affine normalization has a literal inserted coordinate one. Its actual
Fréchet derivative inserts zero, and the quotient rule yields precisely the
already proved new-row/old-column projective Jacobian.
-/

open scoped BigOperators ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false

namespace SGPT.Foundations.Schemes

noncomputable section

/-- Insert the actual fixed homogeneous coordinate one. -/
def projectiveRatioCoordinateVector (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    Fin (n + 1) → ℂ := Fin.insertNth i 1 z

/-- The literal normalized tangent lift inserts zero at the distinguished coordinate. -/
def projectiveRatioTangentLift (n : ℕ) (i : Fin (n + 1)) :
    (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Fin.insertNth (α := fun _ => ℂ) i 0 v
      map_add' := by
        intro v w
        funext k
        refine Fin.succAboveCases i ?_ (fun a => ?_) k <;> simp
      map_smul' := by
        intro c v
        funext k
        refine Fin.succAboveCases i ?_ (fun a => ?_) k <;> simp }

theorem projectiveRatioTangentLift_apply (n : ℕ) (i : Fin (n + 1)) (v : Fin n → ℂ) :
    projectiveRatioTangentLift n i v = Fin.insertNth i 0 v := rfl

theorem projectiveRatioCoordinateVector_hasFDerivAt (n : ℕ) (i : Fin (n + 1))
    (z : Fin n → ℂ) :
    HasFDerivAt (projectiveRatioCoordinateVector n i) (projectiveRatioTangentLift n i) z := by
  have h := ((projectiveRatioTangentLift n i).hasFDerivAt (x := z)).const_add
    (Fin.insertNth i 1 (0 : Fin n → ℂ))
  have hf : projectiveRatioCoordinateVector n i =
      (fun w => Fin.insertNth i 1 (0 : Fin n → ℂ) + projectiveRatioTangentLift n i w) := by
    funext w k
    refine Fin.succAboveCases i ?_ (fun a => ?_) k <;>
      simp [projectiveRatioCoordinateVector, projectiveRatioTangentLift_apply]
  rw [hf]
  exact h

/-- The literal quotient-coordinate transition with the true `Fin.succAbove` ordering. -/
def projectiveRatioTransition (n : ℕ) (i j : Fin (n + 1)) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun a => projectiveRatioCoordinateVector n i z (j.succAbove a) /
    projectiveRatioCoordinateVector n i z j

/-- The native complex continuous linear map of the actual ratio Jacobian. -/
def projectiveRatioJacobianCLM (n : ℕ) (i j : Fin (n + 1))
    (q : Fin (n + 1) → ℂ) (u : ℂˣ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun a => ∑ b : Fin n,
    projectiveQuotientJacobian n i j q u a b • ContinuousLinearMap.proj b

theorem projectiveRatioJacobianCLM_apply (n : ℕ) (i j : Fin (n + 1))
    (q : Fin (n + 1) → ℂ) (u : ℂˣ) (v : Fin n → ℂ) (a : Fin n) :
    projectiveRatioJacobianCLM n i j q u v a =
      ∑ b : Fin n, projectiveQuotientJacobian n i j q u a b * v b := by
  simp [projectiveRatioJacobianCLM]

/-- The literal complex quotient Jacobian is the genuine complex Fréchet derivative. -/
theorem projectiveRatioTransition_hasFDerivAt (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    HasFDerivAt (projectiveRatioTransition n i j)
      (projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u) z := by
  classical
  apply hasFDerivAt_pi''
  intro a
  have hq := projectiveRatioCoordinateVector_hasFDerivAt n i z
  have hn := (ContinuousLinearMap.proj (j.succAbove a) :
    (Fin (n + 1) → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hq
  have hd := (ContinuousLinearMap.proj j :
    (Fin (n + 1) → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp z hq
  have hzero : projectiveRatioCoordinateVector n i z j ≠ 0 := hu ▸ Units.ne_zero u
  have h := hn.mul ((hasFDerivAt_inv hzero).comp z hd)
  convert! h using 1
  ext v
  have hv := projectiveFubiniStudyQuotientTangent_jacobian n i j
    (projectiveRatioCoordinateVector n i z) (projectiveRatioTangentLift n i v)
    (by simp [projectiveRatioTangentLift_apply]) u a
  simp only [projectiveRatioTangentLift_apply, Fin.insertNth_apply_succAbove] at hv
  rw [← projectiveRatioJacobianCLM_apply] at hv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [← hv, projectiveFubiniStudyQuotientTangent_apply]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply, projectiveRatioTangentLift_apply,
    Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [← hu]
  simp only [Units.val_inv_eq_inv_val, inv_pow]
  ring

theorem projectiveRatioTransition_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    fderiv ℂ (projectiveRatioTransition n i j) z =
      projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u :=
  (projectiveRatioTransition_hasFDerivAt n i j z u hu).fderiv

/-- The genuine real Fréchet derivative is the scalar restriction of the same literal matrix. -/
theorem projectiveRatioTransition_real_hasFDerivAt (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    HasFDerivAt (projectiveRatioTransition n i j)
      ((projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u).restrictScalars ℝ) z :=
  (projectiveRatioTransition_hasFDerivAt n i j z u hu).restrictScalars ℝ

theorem projectiveRatioTransition_real_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    fderiv ℝ (projectiveRatioTransition n i j) z =
      (projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u).restrictScalars ℝ :=
  (projectiveRatioTransition_real_hasFDerivAt n i j z u hu).fderiv

/-- The actual inserted homogeneous coordinate map is smooth in every complex order. -/
theorem projectiveRatioCoordinateVector_contDiff (n : ℕ) (i : Fin (n + 1))
    (k : WithTop ℕ∞) : ContDiff ℂ k (projectiveRatioCoordinateVector n i) := by
  apply contDiff_pi.mpr
  intro a
  refine Fin.succAboveCases i ?_ (fun b => ?_) a
  · simpa only [projectiveRatioCoordinateVector, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℂ k (fun _ : Fin n → ℂ => (1 : ℂ)))
  · simpa only [projectiveRatioCoordinateVector, Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℂ ℂ b : ContDiff ℂ k (fun z : Fin n → ℂ => z b))

theorem projectiveRatioTransition_contDiffOn (n : ℕ) (i j : Fin (n + 1))
    (k : WithTop ℕ∞) :
    ContDiffOn ℂ k (projectiveRatioTransition n i j)
      {z | projectiveRatioCoordinateVector n i z j ≠ 0} := by
  apply contDiffOn_pi.mpr
  intro a
  exact (((contDiff_apply ℂ ℂ (j.succAbove a)).comp
    (projectiveRatioCoordinateVector_contDiff n i k)).contDiffOn).div
    (((contDiff_apply ℂ ℂ j).comp (projectiveRatioCoordinateVector_contDiff n i k)).contDiffOn)
    (fun _ hz => hz)

/-- Covariance holds for the genuine complex Fréchet derivative, without a derivative premise. -/
theorem projectiveRatioTransition_metric_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z v w : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    projectiveFubiniStudyRealMetric (projectiveRatioTransition n i j z)
      (fderiv ℂ (projectiveRatioTransition n i j) z v)
      (fderiv ℂ (projectiveRatioTransition n i j) z w) =
      projectiveFubiniStudyRealMetric z v w := by
  rw [projectiveRatioTransition_fderiv n i j z u hu]
  change projectiveFubiniStudyRealMetric (projectiveRatioTransition n i j z)
    (fun a => projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u v a)
    (fun a => projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u w a) = _
  simp only [projectiveRatioJacobianCLM_apply]
  have ht : projectiveRatioTransition n i j z =
      (fun a => (↑(u⁻¹) : ℂ) * projectiveRatioCoordinateVector n i z (j.succAbove a)) := by
    funext a
    rw [projectiveRatioTransition, ← hu]
    simp only [div_eq_mul_inv, Units.val_inv_eq_inv_val, mul_comm]
  rw [ht]
  have h := projectiveFubiniStudyRealMetric_jacobian n i j
    (projectiveRatioCoordinateVector n i z) (Fin.insertNth i 0 v) (Fin.insertNth i 0 w)
    (by simp [projectiveRatioCoordinateVector]) (by simp) (by simp) u hu
  simpa only [projectiveRatioCoordinateVector, Fin.insertNth_apply_succAbove] using h

/-- Covariance holds for the actual real derivative on the existing real coordinate model. -/
theorem projectiveRatioTransition_metric_real_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z v w : Fin n → ℂ) (u : ℂˣ) (hu : (u : ℂ) = projectiveRatioCoordinateVector n i z j) :
    projectiveFubiniStudyRealMetric (projectiveRatioTransition n i j z)
      (fderiv ℝ (projectiveRatioTransition n i j) z v)
      (fderiv ℝ (projectiveRatioTransition n i j) z w) =
      projectiveFubiniStudyRealMetric z v w := by
  rw [projectiveRatioTransition_real_fderiv n i j z u hu]
  change projectiveFubiniStudyRealMetric (projectiveRatioTransition n i j z)
    (projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u v)
    (projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z) u w) = _
  simpa only [projectiveRatioTransition_fderiv n i j z u hu] using
    projectiveRatioTransition_metric_fderiv n i j z v w u hu

/-- Multiplication by the actual imaginary unit preserves the coordinate Hermitian metric. -/
theorem projectiveFubiniStudyHermitian_imaginary (n : ℕ) (z v w : Fin n → ℂ) :
    projectiveFubiniStudyHermitian z (Complex.I • v) (Complex.I • w) =
      projectiveFubiniStudyHermitian z v w := by
  rw [projectiveFubiniStudyHermitian_smul_left, projectiveFubiniStudyHermitian_smul_right]
  rw [← mul_assoc]
  simp

theorem projectiveFubiniStudyRealMetric_imaginary (n : ℕ) (z v w : Fin n → ℂ) :
    projectiveFubiniStudyRealMetric z (Complex.I • v) (Complex.I • w) =
      projectiveFubiniStudyRealMetric z v w :=
  congrArg (fun x : ℂ => 2 * x.re) (projectiveFubiniStudyHermitian_imaginary n z v w)

end

end SGPT.Foundations.Schemes
