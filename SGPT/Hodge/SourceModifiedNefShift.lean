import SGPT.Hodge.BDivChainReal
import SGPT.Hodge.ConePositive
import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- The same actual modified-nef potentials survive smooth semipositive addition. -/
theorem classModifiedNef_add_semipositive (ω : KahlerBackground (m + 1) X)
    {α : RealBottChern (m + 1) X} (hα : SGPT.Siu.ClassModifiedNefWithRespectTo ω α)
    (σ : ClosedRealOneOneForm (m + 1) X) (hσ : σ.val.IsSemipositive) :
    SGPT.Siu.ClassModifiedNefWithRespectTo ω (α + RealBottChern.ofRepresentative σ) := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change SGPT.Siu.ModifiedNefWithRespectTo ω θ at hα
    change SGPT.Siu.ClassModifiedNefWithRespectTo ω
      (RealBottChern.ofRepresentative θ + RealBottChern.ofRepresentative σ)
    rw [← RealBottChern.ofRepresentative_add]
    change SGPT.Siu.ModifiedNefWithRespectTo ω (θ + σ)
    intro ε hε
    obtain ⟨φ, hφ, hD⟩ := hα ε hε
    refine ⟨φ, ?_, hD⟩
    have heq : θ + σ + ε • ω.form = (θ + ε • ω.form) + σ := by abel
    rw [heq]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hσ

/-- Actual Kähler classes are genuinely big, without any caller bigness certificate. -/
theorem isBigClass_kahler (κ : KahlerBackground (m + 1) X) :
    IsBigClass (RealBottChern.ofRepresentative κ.form) := by
  have hs : (0 : ClosedRealOneOneForm (m + 1) X).val.IsSemipositive := by
    simpa only [zero_smul] using
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (show (0 : ℝ) ≤ 0 by norm_num))
  have h0 : IsThetaPshPotential (0 : ClosedRealOneOneForm (m + 1) X).val
      (fun _ : X => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff _).mpr hs
  simpa only [one_smul, zero_add] using
    (PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential κ
      (0 : ClosedRealOneOneForm (m + 1) X) h0 zero_lt_one)

variable [CompactSpace X]

/-- The genuine pseudo-effective limit follows from the actual epsilon-PSH witnesses
of modified nefness and the established weak-current compactness theorem. -/
theorem classPseudoeffective_of_modifiedNef (ω : KahlerBackground (m + 1) X)
    {α : RealBottChern (m + 1) X} (hα : SGPT.Siu.ClassModifiedNefWithRespectTo ω α) :
    ClassPseudoeffectiveViaPotentials α := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change SGPT.Siu.ModifiedNefWithRespectTo ω θ at hα
    apply SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_of_forall_add_smul
      ω (RealBottChern.ofRepresentative θ)
    intro ε hε
    obtain ⟨φ, hφ, -⟩ := hα ε hε
    rw [← RealBottChern.ofRepresentative_smul, ← RealBottChern.ofRepresentative_add]
    exact ⟨φ, hφ⟩

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
