import SGPT.PSH.SourceCanonicalAssociatedRay

/-!
# The corrected display `eq:lvarphigeq_temp1` of `ex:testcurve:L843` (snapshot `c88c7ff4`)

Source `ex:testcurve:L843` (chapter *Test curves*, `author/chapter_testcurve.tex:832–872` of
`c88c7ff4`; ERRATA E17, corrected upstream). The book now keeps the constant branch of the
canonical test curve at slope `-1` and writes, for `t > 0`,

`ℓ^φ_t ≥ (V_θ - t) ∨ sup_{τ ∈ (-1,0)} ((1+τ)φ - τV_θ + tτ) = φ ∨ (V_θ - t)`,

"where `φ` is finite, the expression in the supremum is affine in `τ` with endpoint values
`V_θ - t` and `φ`; where `φ = -∞`, the term `V_θ - t` gives the displayed maximum."

`max_sub_iSup_Ioo_rawCanonicalAffine` is this scalar identity, pointwise in `EReal`
(`a = φ(x) ≤ b = V_θ(x) < +∞`, poles included). It is the corrected display in the form printed
by the new source; it is equivalent to the closed-left form
`SGPT.PSH.CanonicalRayDraft.rawCanonicalAffine_iSup_closed_left` used by the existing proof of
the example (`sourceCanonicalAssociatedRay_eq`), from which it is derived.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.CanonicalRayDraft

open Set

/-- **`ex:testcurve:L843`, display `eq:lvarphigeq_temp1` (`c88c7ff4`)**: for `a ≤ b < +∞` in
`EReal` (`a = φ(x)`, `b = V_θ(x)`) and real `t`,
`(b - t) ∨ sup_{τ ∈ (-1,0)} ((1+τ)a - τb + tτ) = a ∨ (b - t)`. -/
theorem max_sub_iSup_Ioo_rawCanonicalAffine {a b : EReal} (hab : a ≤ b) (hb : b ≠ ⊤) (t : ℝ) :
    max (b - (t : EReal)) (⨆ τ : Ioo (-1 : ℝ) 0, rawCanonicalAffine a b t τ.val) =
      max a (b - (t : EReal)) := by
  rw [← rawCanonicalAffine_iSup_closed_left hab hb t]
  apply le_antisymm
  · apply max_le
    · have h := le_iSup (fun τ : Ico (-1 : ℝ) 0 => rawCanonicalAffine a b t τ.val)
        ⟨-1, ⟨le_rfl, by norm_num⟩⟩
      simpa only [rawCanonicalAffine_neg_one] using h
    · exact iSup_le fun τ => le_iSup_of_le
        (⟨τ.val, ⟨τ.property.1.le, τ.property.2⟩⟩ : Ico (-1 : ℝ) 0) le_rfl
  · refine iSup_le fun τ => ?_
    rcases eq_or_lt_of_le τ.property.1 with h | h
    · rw [← h, rawCanonicalAffine_neg_one]
      exact le_max_left _ _
    · exact le_max_of_le_right
        (le_iSup_of_le (⟨τ.val, ⟨h, τ.property.2⟩⟩ : Ioo (-1 : ℝ) 0) le_rfl)

end SGPT.PSH.CanonicalRayDraft

end
