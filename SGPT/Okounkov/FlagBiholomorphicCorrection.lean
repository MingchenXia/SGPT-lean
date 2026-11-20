import SGPT.Okounkov.SourceSliceResolvedTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set Matrix
open scoped BigOperators NNReal
open SGPT.Okounkov.TranscendentalLifting

/-- Every entry of the ACTUAL source correction matrix is nonnegative.
Evaluate the existing genuine nonnegative action on each coordinate vector;
no nonnegativity or matrix-presentation certificate is assumed. -/
theorem correctionMatrixReal_nonneg {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (i j : Fin n) :
    0 ≤ correctionMatrixReal hπ i j := by
  have h := congrFun (flagLiftingCorrectionMatrix_vecMul_nnreal n F W π hπ (Pi.single i 1)) j
  have heq : correctionMatrixReal hπ i j =
      (flagLiftingCorrectionNNReal n F W π hπ (Pi.single i 1) j : ℝ) := by
    have hc : (fun x : Fin n => ((Pi.single i (1 : ℝ≥0) : Fin n → ℝ≥0) x : ℝ)) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      funext x
      by_cases hx : x = i <;> simp [hx]
    change ((fun x : Fin n => ((Pi.single i (1 : ℝ≥0) : Fin n → ℝ≥0) x : ℝ)) ᵥ*
      correctionMatrixReal hπ) j = _ at h
    rw [hc] at h
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h
  rw [heq]
  exact NNReal.coe_nonneg _

/-- Every diagonal entry of the ACTUAL source correction matrix is1,
by its literal recursively manufactured Cartier block matrix. -/
theorem correctionMatrixReal_diag : ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (hπ : IsFlagLifting F W π) (i : Fin n),
    correctionMatrixReal hπ i i = 1 := by
  intro n
  induction n with
  | zero => intro F W π hπ i; exact Fin.elim0 i
  | succ m ih =>
    intro F W π hπ i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((1 : ℤ) : ℝ) = 1
      exact Int.cast_one
    · exact ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting j

/-- Actual mutually inverse full-flag liftings have IDENTITY source
correction matrices. Native composition gives A B=1; genuine entry
nonnegativity and actual diagonal1 then force every off-diagonal entry0. -/
theorem correctionMatrixReal_eq_one_of_inverse
    {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {σ : F.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hσ : IsFlagLifting W F σ)
    (hinverse : π ∘ σ = id) : correctionMatrixReal hπ = 1 := by
  have hcomp : IsFlagLifting F F (π ∘ σ) := by
    rw [hinverse]
    exact SourceSlice.identityFlagLifting F
  have hprod : correctionMatrixReal hπ * correctionMatrixReal hσ = 1 := by
    have h := (correctionMatrixReal_comp hπ hσ hcomp).symm
    have heq : (⟨π ∘ σ, hcomp⟩ : {f : F.carrier → F.carrier // IsFlagLifting F F f}) =
        ⟨id, SourceSlice.identityFlagLifting F⟩ := Subtype.ext hinverse
    have hmatrix := congrArg (fun z : {f : F.carrier → F.carrier // IsFlagLifting F F f} =>
      correctionMatrixReal z.property) heq
    exact h.trans (hmatrix.trans (SourceSlice.correctionMatrixReal_identity F))
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using correctionMatrixReal_diag n F W π hπ i
  · have hle : correctionMatrixReal hπ i j * correctionMatrixReal hσ j j ≤
        (correctionMatrixReal hπ * correctionMatrixReal hσ) i j :=
      Finset.single_le_sum
        (fun k _ => mul_nonneg (correctionMatrixReal_nonneg hπ i k)
          (correctionMatrixReal_nonneg hσ k j)) (Finset.mem_univ j)
    rw [correctionMatrixReal_diag, mul_one, hprod, Matrix.one_apply, if_neg hij] at hle
    simp only [Matrix.one_apply, if_neg hij]
    exact le_antisymm hle (correctionMatrixReal_nonneg hπ i j)

end SGPT.Okounkov.ToricTransport
