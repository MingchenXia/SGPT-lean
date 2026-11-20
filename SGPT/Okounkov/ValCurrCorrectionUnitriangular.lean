import SGPT.Okounkov.FlagCorrectionMatrix
import SGPT.Okounkov.ValCurrLexEquivalence

/-!
# The correction matrix of a flag lifting is unitriangular

Source: chapter *The theory of Okounkov bodies*, `def:lifting`: for a lifting `W•` of the smooth
flag `Y•` along `π : Z → X`, the correction `cor(Y•, π)` lies in `Aut(ℤⁿ_lex)`, i.e. (with the
identification stated before `rmk:Abhyankar`) it is a matrix `I + U` with `U` strictly upper
triangular and integral.

* `isUnitUpperTriangular_flagLiftingCorrectionMatrix`: the block recursion `eq:correcur`
  defining `flagLiftingCorrectionMatrix` produces a unitriangular matrix.
* `unitriangularLexEquiv_flagLiftingCorrectionMatrix`: the associated automorphism of `ℤⁿ_lex`
  (`x ↦ x cor(Y•, π)`) is the ordered additive automorphism `flagLiftingCorrection`.

Hence (with `prop:cormatrix`) the current valuation of the lifted flag is the original one
followed by an automorphism `I + U` of `ℤⁿ_lex`, in the sense of the footnote of `rmk:Abhyankar`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.ValCurr

open Matrix
open scoped Matrix

/-- **`cor(Y•, π)` is unitriangular**: the matrix of `eq:correcur` is `I + U`, `U` strictly
upper triangular. -/
theorem isUnitUpperTriangular_flagLiftingCorrectionMatrix :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π),
      IsUnitUpperTriangular (flagLiftingCorrectionMatrix n F W π hπ)
  | 0, _, _, _, _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, F, W, π, hπ => by
      have ih := isUnitUpperTriangular_flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap
        hπ.tailMap_isFlagLifting
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [flagLiftingCorrectionMatrix]
        · simpa [flagLiftingCorrectionMatrix] using ih.diag i
      · revert hij
        refine Fin.cases ?_ (fun i => ?_) i
        · intro hij
          exact absurd hij (Fin.not_lt_zero j)
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro _
            simp [flagLiftingCorrectionMatrix]
          · intro hij
            have hij' : j < i := Fin.succ_lt_succ_iff.mp hij
            simpa [flagLiftingCorrectionMatrix] using ih.lower hij'

/-- The automorphism `x ↦ x cor(Y•, π)` of `ℤⁿ_lex` is `flagLiftingCorrection`. -/
theorem unitriangularLexEquiv_flagLiftingCorrectionMatrix (n : ℕ)
    (F W : OriginalFlagGeometry.{u} n) (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    unitriangularLexEquiv (flagLiftingCorrectionMatrix n F W π hπ)
        (isUnitUpperTriangular_flagLiftingCorrectionMatrix n F W π hπ) =
      flagLiftingCorrection n F W π hπ := by
  ext x
  rw [unitriangularLexEquiv_apply, flagLiftingCorrectionMatrix_vecMul_int, toLex_ofLex,
    toLex_ofLex]

end SGPT.Okounkov.ValCurr
