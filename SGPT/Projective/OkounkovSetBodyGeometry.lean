import SGPT.Okounkov.ValGenSections

/-! Actual geometry of EXISTING setBody, retaining its true domain and original empty junk value.
Blueprint: okounkov-set-body-geometry.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.ValGen
open Set SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class

/-- EXISTING setBody is always genuinely compact; outside its actual domain it is truly empty. -/
theorem isCompact_setBody {n : ℕ} (C : AdmissibleCone n) (S : Set ((Fin n → ℤ)×ℤ)) :
    IsCompact (setBody C S) := by
  classical
  unfold setBody
  split_ifs with h
  · exact (SGPT.AlmostSemigroup.OkounkovExtension.bodyExtension (⟨⟨S,h.1⟩,h.2⟩ : AlmostSpace C)).isCompact
  · exact isCompact_empty

/-- EXISTING setBody is always genuinely convex; no invalid subset is declared to lie in the almost locus. -/
theorem convex_setBody {n : ℕ} (C : AdmissibleCone n) (S : Set ((Fin n → ℤ)×ℤ)) :
    Convex ℝ (setBody C S) := by
  classical
  unfold setBody
  split_ifs with h
  · exact (SGPT.AlmostSemigroup.OkounkovExtension.bodyExtension (⟨⟨S,h.1⟩,h.2⟩ : AlmostSpace C)).convex
  · exact convex_empty
end SGPT.Okounkov.ValGen
