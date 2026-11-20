import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-! Actual complex determinant/Gram identities for the original real normal
Jacobian, without geometric/current comparison certificates. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalDeterminant
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped ComplexConjugate InnerProductSpace

/-- The genuine real determinant of the SAME complex endomorphism is the
literal squared complex norm of its actual complex determinant. -/
theorem real_det_eq_normSq {m : ℕ}
    (T : ComplexModel m →L[ℂ] ComplexModel m) :
    (T.restrictScalars ℝ).det = Complex.normSq T.det := by
  change (T.toLinearMap.restrictScalars ℝ).det = Complex.normSq T.toLinearMap.det
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- Complex linear endomorphisms preserve the actual real orientation,
including singular maps and the zero-dimensional model. -/
theorem real_det_nonneg {m : ℕ} (T : ComplexModel m →L[ℂ] ComplexModel m) :
    0 ≤ (T.restrictScalars ℝ).det := by
  rw [real_det_eq_normSq]
  exact Complex.normSq_nonneg _

/-- The SAME real norm determinant has no sign ambiguity for an actual
square complex linear map. -/
theorem normDet_restrictScalars_eq_det {m : ℕ}
    (T : ComplexModel m →L[ℂ] ComplexModel m) :
    (T.restrictScalars ℝ).toLinearMap.normDet = (T.restrictScalars ℝ).det := by
  rw [LinearMap.normDet_eq_abs_det, abs_of_nonneg (real_det_nonneg T)]

/-- The actual real determinant of a genuine original complex unitary
isometry is exactly one, not merely of absolute value one. -/
theorem unitary_real_det_eq_one {n : ℕ}
    (U : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) :
    (U.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).det = 1 := by
  rw [← normDet_restrictScalars_eq_det]
  let UR : ComplexModel n →ₗᵢ[ℝ] ComplexModel n := {
    toLinearMap := U.toLinearEquiv.toLinearMap.restrictScalars ℝ
    norm_map' := U.norm_map }
  exact UR.normDet_eq_one

/-- Literal equality of original complex Gram forms implies equality of
actual real norm determinants, by the SAME actual real orthonormal basis. -/
theorem normDet_eq_of_complex_inner {m n : ℕ}
    (D : ComplexModel m →L[ℂ] ComplexModel n)
    (T : ComplexModel m →L[ℂ] ComplexModel m)
    (h : ∀ x y, inner ℂ (D x) (D y) = inner ℂ (T x) (T y)) :
    (D.restrictScalars ℝ).toLinearMap.normDet = (T.restrictScalars ℝ).toLinearMap.normDet := by
  let DR := (D.restrictScalars ℝ).toLinearMap
  let TR := (T.restrictScalars ℝ).toLinearMap
  let b := stdOrthonormalBasis ℝ (ComplexModel m)
  have hgram : Matrix.gram ℝ (fun i => DR (b i)) = Matrix.gram ℝ (fun i => TR (b i)) := by
    ext i j
    change inner ℝ (D (b i)) (D (b j)) = inner ℝ (T (b i)) (T (b j))
    simpa only [PiLp.inner_apply, real_inner_eq_re_inner, map_sum] using
      congrArg (RCLike.re : ℂ →+ ℝ) (h (b i) (b j))
  have hD := DR.normDet_sq_eq_det_gram b
  have hT := TR.normDet_sq_eq_det_gram b
  have hD' : DR.normDet ^ 2 = (Matrix.gram ℝ (fun i => DR (b i))).det := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hD
  have hT' : TR.normDet ^ 2 = (Matrix.gram ℝ (fun i => TR (b i))).det := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hT
  have heq : DR.normDet ^ 2 = TR.normDet ^ 2 :=
    hD'.trans ((congrArg Matrix.det hgram).trans hT'.symm)
  exact (sq_eq_sq₀ (LinearMap.normDet_nonneg DR) (LinearMap.normDet_nonneg TR)).mp heq

/-- The actual rectangular complex map's normal Jacobian is the actual
real determinant of its SAME-domain square complex Gram factor. -/
theorem normDet_eq_real_det_of_complex_inner {m n : ℕ}
    (D : ComplexModel m →L[ℂ] ComplexModel n)
    (T : ComplexModel m →L[ℂ] ComplexModel m)
    (h : ∀ x y, inner ℂ (D x) (D y) = inner ℂ (T x) (T y)) :
    (D.restrictScalars ℝ).toLinearMap.normDet = (T.restrictScalars ℝ).det :=
  (normDet_eq_of_complex_inner D T h).trans (normDet_restrictScalars_eq_det T)

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalDeterminant
