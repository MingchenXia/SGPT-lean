import SGPT.Bergman.SourceAndreiefExpansion
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.Andreief
open scoped BigOperators ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact physical half-weight scaling of each actual scalar evaluation. -/
def tiltedEvaluations (f : ι → K → ℂ) (u : K → ℝ) (a t : ℝ) : ι → K → ℂ :=
  fun i x => (Real.exp (a * t * u x / 2) : ℂ) * f i x

private theorem real_scaled_pair (r : ℝ) (z w : ℂ) :
    conj ((r : ℂ) * z) * ((r : ℂ) * w) =
      ((r ^ 2 : ℝ) : ℂ) * (conj z * w) := by
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Genuine exponential pair scaling, with the full original k-weight
coming from two half-weights rather than a supplied identity. -/
theorem tilted_pair (f : ι → K → ℂ) (u : K → ℝ) (a t : ℝ) (i j : ι) (x : K) :
    conj (tiltedEvaluations f u a t i x) * tiltedEvaluations f u a t j x =
      (Real.exp (a * t * u x) : ℂ) * (conj (f i x) * f j x) := by
  change conj ((Real.exp (a * t * u x / 2) : ℂ) * f i x) *
    ((Real.exp (a * t * u x / 2) : ℂ) * f j x) = _
  rw [real_scaled_pair]
  have he : Real.exp (a * t * u x / 2) ^ 2 = Real.exp (a * t * u x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]

/-- Exact determinant-density tilt on original point tuples, internally
derived from actual column scaling and the complex determinant norm-square. -/
theorem squaredEvaluationDet_tilt (f : ι → K → ℂ) (u : K → ℝ) (a t : ℝ)
    (x : ι → K) :
    squaredEvaluationDet (tiltedEvaluations f u a t) x =
      Real.exp (a * t * ∑ j, u (x j)) * squaredEvaluationDet f x := by
  have hm : evaluationMatrix (tiltedEvaluations f u a t) x =
      evaluationMatrix f x * Matrix.diagonal (fun j => (Real.exp (a * t * u (x j) / 2) : ℂ)) := by
    ext i j
    simp only [evaluationMatrix, tiltedEvaluations, Matrix.mul_diagonal]
    exact mul_comm _ _
  unfold squaredEvaluationDet
  rw [hm, Matrix.det_mul, Complex.normSq_mul, Matrix.det_diagonal]
  simp only [map_prod, Complex.normSq_ofReal]
  have he (j : ι) : Real.exp (a * t * u (x j) / 2) *
      Real.exp (a * t * u (x j) / 2) = Real.exp (a * t * u (x j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Real.exp_sum]
  have hs : (∑ j, a * t * u (x j)) = a * t * ∑ j, u (x j) := by
    rw [Finset.mul_sum]
  rw [hs, mul_comm]

end SGPT.Bergman.Andreief
