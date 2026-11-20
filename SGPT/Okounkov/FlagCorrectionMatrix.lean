import SGPT.Okounkov.FlagCorrectionNonnegative
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set
open scoped NNReal Matrix

/-- The literal integer row-vector block matrix of the same independent
geometric correction; it is not defined by a current valuation identity. -/
def flagLiftingCorrectionMatrix : (n : ℕ) → (F W : OriginalFlagGeometry.{u} n) →
    (π : W.carrier → F.carrier) → IsFlagLifting F W π → Matrix (Fin n) (Fin n) ℤ
  | 0, _, _, _, _ => fun i => Fin.elim0 i
  | m + 1, F, W, _π, hπ =>
    Fin.cons (Fin.cons 1 (flagLiftingCorrectionRow hπ))
      (fun i => Fin.cons 0
        (flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting i))

private theorem correctionMatrix_succ {m : ℕ}
    (F W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
    (hπ : IsFlagLifting F W π) :
    flagLiftingCorrectionMatrix (m + 1) F W π hπ =
      Fin.cons (Fin.cons 1 (flagLiftingCorrectionRow hπ))
        (fun i => Fin.cons 0
          (flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting i)) := rfl

/-- Actual finite-sum coordinate readback gives the same already-produced
integer ordered additive automorphism, in the source row-vector convention. -/
theorem flagLiftingCorrectionMatrix_vecMul_int :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (v : Fin n → ℤ),
      v ᵥ* flagLiftingCorrectionMatrix n F W π hπ =
        ofLex (flagLiftingCorrection n F W π hπ (toLex v)) := by
  intro n
  induction n with
  | zero =>
      intro F W π hπ v
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      intro F W π hπ v
      rw [correctionMatrix_succ]
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
        rfl
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
        have htail := congrFun (ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
          (fun i => v i.succ)) k
        change (∑ i : Fin m, v i.succ *
          flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting i k) =
          ofLex (flagLiftingCorrection m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
            (toLex (fun i => v i.succ))) k at htail
        rw [htail]
        change v 0 * flagLiftingCorrectionRow hπ k + _ =
          ofLex (flagLiftingCorrection m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
            (toLex (fun i => v i.succ))) k + v 0 * flagLiftingCorrectionRow hπ k
        exact add_comm _ _

private theorem correctionRow_real_eq {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (i : Fin m) :
    (flagLiftingCorrectionRow hπ i : ℝ) = (flagLiftingCorrectionRowNNReal hπ i : ℝ) := by
  obtain ⟨D, hDI, RT, hC, η, hη, hrow⟩ := flagLiftingCorrectionRow_spec hπ
  simp only [flagLiftingCorrectionRowNNReal, hrow, Int.toNat_natCast]
  norm_cast

/-- The real right product of the SAME integer coefficients is the literal
nonnegative action, including all real finite values and the empty vector. -/
theorem flagLiftingCorrectionMatrix_vecMul_nnreal :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (v : Fin n → ℝ≥0),
      (fun i => (v i : ℝ)) ᵥ*
        (fun i j => (flagLiftingCorrectionMatrix n F W π hπ i j : ℝ)) =
          fun j => (flagLiftingCorrectionNNReal n F W π hπ v j : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro F W π hπ v
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      intro F W π hπ v
      rw [correctionMatrix_succ, flagLiftingCorrectionNNReal_succ]
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ, Int.cast_one, Int.cast_zero,
          mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ, NNReal.coe_add, NNReal.coe_mul]
        have htail := congrFun (ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
          (fun i => v i.succ)) k
        change (∑ i : Fin m, (v i.succ : ℝ) *
          (flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting i k : ℝ)) =
          (flagLiftingCorrectionNNReal m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
            (fun i => v i.succ) k : ℝ) at htail
        rw [htail, correctionRow_real_eq hπ k]
        exact add_comm _ _

end SGPT.Okounkov
