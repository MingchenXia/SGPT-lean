import SGPT.Okounkov.IntegerCorrection
import SGPT.Okounkov.FlagLiftingTail
import SGPT.Okounkov.FlagCorrectionRow

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set

/-- The actual literal level-one restriction and corestriction of the
original lifting; only the genuine containment proof is selected. -/
def IsFlagLifting.tailMap {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    W.tail.carrier → F.tail.carrier :=
  flagComponentMap F W π (1 : Fin (m + 2)) (Classical.choose (hπ.2 (1 : Fin (m + 2))))

/-- Reuse the completed genuine tail geometry for this same literal map. -/
theorem IsFlagLifting.tailMap_isFlagLifting {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) : IsFlagLifting F.tail W.tail hπ.tailMap :=
  hπ.tail (Classical.choose (hπ.2 (1 : Fin (m + 2))))

/-- Actual finite-dimensional source correction recursion: a manufactured
integer Cartier row and the genuine recursively lifted tail automorphism. -/
def flagLiftingCorrection : (n : ℕ) → (F W : OriginalFlagGeometry.{u} n) →
    (π : W.carrier → F.carrier) → IsFlagLifting F W π →
    (Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
  | 0, _, _, _, _ => OrderAddMonoidIso.refl _
  | m + 1, F, W, _π, hπ =>
    integerCorrectionStep (flagLiftingCorrectionRow hπ)
      (flagLiftingCorrection m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting)

theorem flagLiftingCorrection_zero (F W : OriginalFlagGeometry.{u} 0)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    flagLiftingCorrection 0 F W π hπ = OrderAddMonoidIso.refl (Lex (Fin 0 → ℤ)) := rfl

/-- The actual one-dimensional source branch is literally [1]. -/
theorem flagLiftingCorrection_one (F W : OriginalFlagGeometry.{u} 1)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    flagLiftingCorrection 1 F W π hπ = OrderAddMonoidIso.refl (Lex (Fin 1 → ℤ)) := by
  change integerCorrectionStep _ _ = _
  exact integerCorrectionStep_dim_one _ _

/-- The literal source block recursion, with the actual geometric Cartier
row and the actual original restricted map, without a target certificate. -/
theorem flagLiftingCorrection_succ {m : ℕ}
    (F W : OriginalFlagGeometry.{u} (m + 1))
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) :
    flagLiftingCorrection (m + 1) F W π hπ =
      integerCorrectionStep (flagLiftingCorrectionRow hπ)
        (flagLiftingCorrection m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting) := rfl

end SGPT.Okounkov
