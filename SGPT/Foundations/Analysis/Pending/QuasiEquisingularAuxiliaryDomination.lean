import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination

set_option autoImplicit false

/-! # Full QEA data under actual auxiliary Kähler domination -/

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularAuxiliaryDomination

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine nonnegative stage errors multiply the actual semipositive
auxiliary difference. All other full-QEA clauses remain the original ones. -/
theorem isQuasiEquisingularApproximation_of_auxiliary_domination
    {omega κ : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hsemi : (κ.form - omega.form).val.IsSemipositive) :
    IsQuasiEquisingularApproximation κ θ u ε uSeq := by
  refine ⟨h.target, h.error, fun j => ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hform : θ + ε j • omega.form + ε j • (κ.form - omega.form) =
      θ + ε j • κ.form := by module
  simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
    (h.term j) (KahlerDomination.isSemipositive_smul hsemi (h.error_nonneg j))

/-- Compact domination of the two actual smooth Kähler forms produces
one auxiliary form that simultaneously dominates both. -/
theorem exists_common_auxiliary_kahler_background [CompactSpace M]
    (omega₀ omega₁ : KahlerBackground n M) :
    ∃ κ : KahlerBackground n M,
      (κ.form - omega₀.form).val.IsSemipositive ∧
      (κ.form - omega₁.form).val.IsSemipositive := by
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omega₀ (fun b : Bool => -(if b then omega₁.form else omega₀.form))
  let κ : KahlerBackground n M := KahlerBackground.smul hC omega₀
  have h₀ : (κ.form - omega₀.form).val.IsSemipositive := by
    have hform : -omega₀.form + C • omega₀.form = κ.form - omega₀.form := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [Bool.false_eq_true, if_false, hform] using hsemi false
  have h₁ : (κ.form - omega₁.form).val.IsSemipositive := by
    have hform : -omega₁.form + C • omega₀.form = κ.form - omega₁.form := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [if_true, hform] using hsemi true
  exact ⟨κ, h₀, h₁⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularAuxiliaryDomination
