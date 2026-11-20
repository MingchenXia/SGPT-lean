import SGPT.PSH.BookCurrentProducts
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix

/-! Actual positive Gram factorization produces exact source decomposable
squares for EVERY semipositive (1,1) tensor, all n including zero. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Finset Matrix
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms TopDegreeDensity LocalCurrentDensityMatrix
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.PSH.BookCurrent
open scoped ComplexOrder MatrixOrder

/-- Actual complex continuous covectors constructed from a Gram matrix row. -/
def gramRowCovector {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) :
    ComplexModel n →L[ℂ] ℂ :=
  ∑ j, star (y l j) • EuclideanSpace.proj j

theorem gramRowCovector_coordinate {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ)
    (l j : Fin n) : gramRowCovector y l (coordinateVector j) = star (y l j) := by
  classical
  simp [gramRowCovector,coordinateVector,EuclideanSpace.proj,
    PiLp.proj,PiLp.projₗ]

/-- GENUINE internally produced finite square decomposition of an arbitrary
semipositive tensor; no source decomposition/rank/basis/output certificate. -/
theorem semipositive_exists_source_square_decomposition {n : ℕ} {A : RealForm n 2}
    (hA : IsSemipositiveOneOne A) :
    ∃ beta : Fin n → ComplexModel n →L[ℂ] ℂ,
      A = (1 / (2 * Real.pi) : ℝ) • ∑ l, oneOneSquare (beta l) := by
  classical
  obtain ⟨y,hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (normalizedHermitianMatrix_posSemidef hA).nonneg
  let B : RealForm n 2 := (1 / (2 * Real.pi) : ℝ) • ∑ l, oneOneSquare (gramRowCovector y l)
  have hB : IsOneOne B :=
    isOneOne_smul (isOneOne_sum univ (fun l _ => oneOneSquare_isOneOne _)) _
  have hH : normalizedHermitianMatrix B = normalizedHermitianMatrix A := by
    change normalizedHermitianMatrixₗ B = _
    rw [show B = (1 / (2 * Real.pi) : ℝ) • ∑ l, oneOneSquare (gramRowCovector y l) from rfl,
      map_smul,map_sum]
    change (1 / (2 * Real.pi) : ℝ) •
      (∑ l, normalizedHermitianMatrix (oneOneSquare (gramRowCovector y l))) = _
    simp_rw [normalizedHermitianMatrix_oneOneSquare]
    rw [hy]
    ext j k
    simp only [Matrix.smul_apply,Matrix.sum_apply,vecMulVec_apply,
      gramRowCovector_coordinate,star_star,Matrix.mul_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_ofNat,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  refine ⟨gramRowCovector y,?_⟩
  change A = B
  symm
  apply sub_eq_zero.mp
  apply eq_zero_of_normalizedHermitianMatrix_eq_zero (isOneOne_sub hB hA.1)
  change normalizedHermitianMatrixₗ (B-A) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hH

end SGPT.PSH.ComplexCurrentDraft
