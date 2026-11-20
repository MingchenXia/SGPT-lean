import SGPT.NPP.CodexC11OriginalHermitianDensity

/-! Finite coordinate symmetry yields a single a.e. Hermitian matrix.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11HermitianPointwise.lean` (module `C11HermitianPointwise`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter

namespace SGPT.NPP.Codex.C11HermitianPointwise
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}

/-- The finitely many pairwise a.e. identities hold together, so the matrix
formed from the same real and imaginary representatives is Hermitian a.e. -/
theorem ae_matrix_isHermitian
    (R I : Fin n → Fin n → X → ℝ)
    (hs : ∀ j k, (R j k =ᵐ[μ] R k j) ∧ (I j k =ᵐ[μ] fun x => -I k j x)) :
    ∀ᵐ x ∂μ, Matrix.IsHermitian (fun j k => (R j k x : ℂ) + Complex.I * (I j k x : ℂ)) := by
  have hR : ∀ᵐ x ∂μ, ∀ j k, R j k x = R k j x := by
    simp only [ae_all_iff]
    exact fun j k => (hs j k).1
  have hI : ∀ᵐ x ∂μ, ∀ j k, I j k x = -I k j x := by
    simp only [ae_all_iff]
    exact fun j k => (hs j k).2
  filter_upwards [hR,hI] with x hR hI
  apply Matrix.IsHermitian.ext
  intro j k
  apply Complex.ext
  · simpa using (hR j k).symm
  · simpa using (hI j k).symm

end SGPT.NPP.Codex.C11HermitianPointwise
