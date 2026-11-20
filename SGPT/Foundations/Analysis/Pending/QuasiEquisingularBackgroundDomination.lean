import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

set_option autoImplicit false

/-! # Genuine QEA fields survive actual background domination -/

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Enlarge the actual target and every varying-stage background, preserving
every other full approximation clause and the same actual functions and errors. -/
theorem isQuasiEquisingularApproximation_of_background_domination
    {omega : KahlerBackground n M} {θ σ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hsemi : (σ - θ).val.IsSemipositive) :
    IsQuasiEquisingularApproximation omega σ u ε uSeq := by
  have hu : IsThetaPshPotential σ.val u := by
    have hform : θ + (σ - θ) = σ := by module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive h.target hsemi
  refine ⟨hu, h.error, fun j => ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hform : θ + ε j • omega.form + (σ - θ) = σ + ε j • omega.form := by module
  simpa only [hform] using
    LocalPotentials.isThetaPshPotential_add_of_semipositive (h.term j) hsemi

/-- Compact finite-form domination internally produces one actual Kähler
background for two full approximations with possibly different original backgrounds. -/
theorem exists_common_kahler_background [CompactSpace M]
    {omega : KahlerBackground n M} {θ₀ θ₁ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ₀ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ₁ u δ vSeq) :
    ∃ κ : KahlerBackground n M,
      IsQuasiEquisingularApproximation omega κ.form u ε uSeq ∧
      IsQuasiEquisingularApproximation omega κ.form u δ vSeq := by
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omega (fun b : Bool => -(if b then θ₁ else θ₀))
  let κ : KahlerBackground n M := KahlerBackground.smul hC omega
  have h₀ : (κ.form - θ₀).val.IsSemipositive := by
    have hform : -θ₀ + C • omega.form = κ.form - θ₀ := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [Bool.false_eq_true, if_false, hform] using hsemi false
  have h₁ : (κ.form - θ₁).val.IsSemipositive := by
    have hform : -θ₁ + C • omega.form = κ.form - θ₁ := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [if_true, hform] using hsemi true
  exact ⟨κ, isQuasiEquisingularApproximation_of_background_domination hu h₀,
    isQuasiEquisingularApproximation_of_background_domination hv h₁⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination
