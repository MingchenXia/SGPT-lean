import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.Andreief
open scoped BigOperators ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual scalar matrix of the entire internally produced evaluation
basis at a tuple of original points, with no determinant-density input. -/
def evaluationMatrix (f : ι → K → ℂ) (x : ι → K) : Matrix ι ι ℂ :=
  fun i j => f i (x j)

/-- Genuine nonnegative squared complex determinant, including empty matrices. -/
def squaredEvaluationDet (f : ι → K → ℂ) (x : ι → K) : ℝ :=
  Complex.normSq (evaluationMatrix f x).det

def permutationSign (σ : Equiv.Perm ι) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

private theorem permutationSign_mul_self (σ : Equiv.Perm ι) : permutationSign σ * permutationSign σ = 1 := by
  have h : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using
      congrArg (fun z : ℤˣ => (z : ℤ)) (Int.units_mul_self (Equiv.Perm.sign σ))
  dsimp only [permutationSign]
  exact_mod_cast h

/-- Exact determinant/conjugate expansion into paired scalar products.
Only pair products will be needed to prove genuine continuity later. -/
theorem ofReal_squaredEvaluationDet (f : ι → K → ℂ) (x : ι → K) :
    Complex.ofReal (squaredEvaluationDet f x) =
      ∑ σ : Equiv.Perm ι, ∑ τ : Equiv.Perm ι,
        permutationSign σ * permutationSign τ *
          ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j) := by
  simp only [squaredEvaluationDet, Complex.normSq_eq_conj_mul_self,
    Matrix.det_apply', map_sum, map_mul, map_intCast, map_prod,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp only [permutationSign, evaluationMatrix, Finset.prod_mul_distrib]
  ring

/-- The integrated double-permutation polynomial is exactly factorial
times the original Gram determinant. There is no nonempty index premise. -/
theorem double_perm_pair_sum (G : Matrix ι ι ℂ) :
    (∑ σ : Equiv.Perm ι, ∑ τ : Equiv.Perm ι,
      permutationSign σ * permutationSign τ * ∏ j, G (σ j) (τ j)) =
      ((Fintype.card ι).factorial : ℂ) * G.det := by
  have hrow (σ : Equiv.Perm ι) :
      (∑ τ : Equiv.Perm ι, permutationSign τ * ∏ j, G (σ j) (τ j)) =
        (G.submatrix σ id).det := by
    rw [← Matrix.det_transpose (G.submatrix σ id), Matrix.det_apply']
    rfl
  have hinner (σ : Equiv.Perm ι) :
      (∑ τ : Equiv.Perm ι, permutationSign σ * permutationSign τ * ∏ j, G (σ j) (τ j)) = G.det := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, hrow, Matrix.det_permute]
    change permutationSign σ * (permutationSign σ * G.det) = G.det
    rw [← mul_assoc, permutationSign_mul_self, one_mul]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm]

end SGPT.Bergman.Andreief
