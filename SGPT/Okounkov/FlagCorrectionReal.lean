import SGPT.Okounkov.FlagCorrectionComposition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open scoped Matrix

/-- The same independent geometric Cartier correction has determinant one;
only the actual zero first column and the genuine restricted tail are used. -/
theorem flagLiftingCorrectionMatrix_det :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π),
      (flagLiftingCorrectionMatrix n F W π hπ).det = 1 := by
  intro n
  induction n with
  | zero =>
      intro F W π hπ
      exact Matrix.det_isEmpty
  | succ m ih =>
      intro F W π hπ
      have hminor :
          (flagLiftingCorrectionMatrix (m + 1) F W π hπ).submatrix
            (0 : Fin (m + 1)).succAbove Fin.succ =
          flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap
            hπ.tailMap_isFlagLifting := by
        ext i j
        simp only [Matrix.submatrix, Matrix.of_apply, Fin.succAbove_zero,
          flagLiftingCorrectionMatrix, Fin.cons_succ]
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, hminor]
      simpa only [flagLiftingCorrectionMatrix, Fin.cons_zero, Fin.cons_succ,
        Fin.val_zero, pow_zero, mul_one, one_mul, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero] using
        ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting

/-- The literal integer-to-real image of that same matrix retains determinant one. -/
theorem flagLiftingCorrectionMatrix_real_det
    (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    ((Int.castRingHom ℝ).mapMatrix (flagLiftingCorrectionMatrix n F W π hπ)).det = 1 := by
  rw [← (Int.castRingHom ℝ).map_det, flagLiftingCorrectionMatrix_det]
  exact map_one _

/-- A genuine linear equivalence on ALL signed real vectors. Its inverse is
manufactured from determinant one, not supplied by a nonnegative certificate. -/
def flagLiftingCorrectionReal (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := by
  let A := (Int.castRingHom ℝ).mapMatrix (flagLiftingCorrectionMatrix n F W π hπ)
  have hA : IsUnit A.det := by
    rw [show A.det = 1 from flagLiftingCorrectionMatrix_real_det n F W π hπ]
    exact isUnit_one
  exact Matrix.toLinearEquivRight'OfInv (M := A⁻¹) (M' := A)
    (Matrix.nonsing_inv_mul A hA) (Matrix.mul_nonsing_inv A hA)

/-- Literal original right multiplication by the real image of the integer matrix. -/
theorem flagLiftingCorrectionReal_apply
    (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (v : Fin n → ℝ) :
    flagLiftingCorrectionReal n F W π hπ v =
      v ᵥ* ((Int.castRingHom ℝ).mapMatrix (flagLiftingCorrectionMatrix n F W π hπ)) := rfl

/-- Literal original right multiplication by its genuine nonsingular inverse. -/
theorem flagLiftingCorrectionReal_symm_apply
    (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (v : Fin n → ℝ) :
    (flagLiftingCorrectionReal n F W π hπ).symm v =
      v ᵥ* ((Int.castRingHom ℝ).mapMatrix (flagLiftingCorrectionMatrix n F W π hπ))⁻¹ := rfl

/-- The existing genuine integer matrix product, read on every signed vector,
gives exactly the source order of real-linear correction composition. -/
theorem flagLiftingCorrectionReal_comp
    (n : ℕ) (F W V : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    flagLiftingCorrectionReal n F V (π ∘ p) (hπ.comp hp) =
      (flagLiftingCorrectionReal n F W π hπ).trans
        (flagLiftingCorrectionReal n W V p hp) := by
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.trans_apply, flagLiftingCorrectionReal_apply]
  rw [flagLiftingCorrectionMatrix_comp n F W V π p hπ hp, map_mul,
    Matrix.vecMul_vecMul]

/-- The actual inverse cancels the further-model action on arbitrary signed
vectors, with inverse composition order retained. -/
theorem flagLiftingCorrectionReal_comp_symm_apply
    (n : ℕ) (F W V : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) (v : Fin n → ℝ) :
    (flagLiftingCorrectionReal n F V (π ∘ p) (hπ.comp hp)).symm
      (flagLiftingCorrectionReal n W V p hp v) =
        (flagLiftingCorrectionReal n F W π hπ).symm v := by
  rw [flagLiftingCorrectionReal_comp n F W V π p hπ hp]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]

end SGPT.Okounkov
