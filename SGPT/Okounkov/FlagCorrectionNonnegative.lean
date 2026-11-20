import SGPT.Okounkov.FlagCorrection

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set
open scoped NNReal

/-- Read the actual nonnegative Cartier row from the independently produced
integer correction row; its natural realization is proved below. -/
def flagLiftingCorrectionRowNNReal {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) : Fin m → ℝ≥0 :=
  fun i => ((flagLiftingCorrectionRow hπ i).toNat : ℝ≥0)

/-- Every genuine original Cartier realization reads as the same nonnegative
row, without an assumed positivity or vector equality certificate. -/
theorem flagLiftingCorrectionRowNNReal_eq_of_spec {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {ν : Fin m → ℕ}
    (hν : OriginalFlagCorrectionRow hπ (fun i => (ν i : ℤ))) :
    flagLiftingCorrectionRowNNReal hπ = fun i => (ν i : ℝ≥0) := by
  have hrow := flagLiftingCorrectionRow_eq_of_spec hπ hν
  funext i
  simp only [flagLiftingCorrectionRowNNReal, hrow, Int.toNat_natCast]

/-- The same genuine geometric block recursion acts on nonnegative finite
real vectors, using the actual inherited original tail lifting. -/
def flagLiftingCorrectionNNReal : (n : ℕ) → (F W : OriginalFlagGeometry.{u} n) →
    (π : W.carrier → F.carrier) → IsFlagLifting F W π →
    (Fin n → ℝ≥0) → (Fin n → ℝ≥0)
  | 0, _, _, _, _, ν => ν
  | m + 1, F, W, _π, hπ, ν =>
    Fin.cons (ν 0) (fun i =>
      flagLiftingCorrectionNNReal m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
        (fun j => ν j.succ) i + ν 0 * flagLiftingCorrectionRowNNReal hπ i)

theorem flagLiftingCorrectionNNReal_zero (F W : OriginalFlagGeometry.{u} 0)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (ν : Fin 0 → ℝ≥0) :
    flagLiftingCorrectionNNReal 0 F W π hπ ν = ν := rfl

theorem flagLiftingCorrectionNNReal_succ {m : ℕ}
    (F W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
    (hπ : IsFlagLifting F W π) (ν : Fin (m + 1) → ℝ≥0) :
    flagLiftingCorrectionNNReal (m + 1) F W π hπ ν =
      Fin.cons (ν 0) (fun i =>
        flagLiftingCorrectionNNReal m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
          (fun j => ν j.succ) i + ν 0 * flagLiftingCorrectionRowNNReal hπ i) := rfl

/-- The actual dimension-one action is the identity with a genuine empty tail. -/
theorem flagLiftingCorrectionNNReal_one (F W : OriginalFlagGeometry.{u} 1)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (ν : Fin 1 → ℝ≥0) :
    flagLiftingCorrectionNNReal 1 F W π hπ ν = ν := by
  funext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rfl

end SGPT.Okounkov
