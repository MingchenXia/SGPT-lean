import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.PSH.SourceGenericLelong
import SGPT.PSH.StrongOpenness
import SGPT.Foundations.Analysis.Pending.PointBlowupLelong
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

/-! The original source PSH point reader and the actual exceptional point-ideal
carrier on an admissible point blowup. There is no compactness or Kahler
hypothesis and no intrinsic prime-class quotient construction.
The source-zero-dimensional interpretation is explicit in the accompanying
scope review.
-/

set_option autoImplicit false
noncomputable section
universe u

open Set
open scoped Topology ENNReal

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SquaredLogLelongSourceNormalization
open PointBlowupLelong

/-- Original whole point-blowup Lelong identity on arbitrary smooth complex
manifolds. The source PSH domain internally produces zero-background native
regularity; the exceptional divisor is the actual pulled-back point ideal. -/
theorem sourceLelong_eq_sourceGenericLelong_pointBlowup
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong n ({x} : Set X) π)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    (ofFixedModel n X).sourceLelong φ x =
      (ofFixedModel n Y).sourceGenericLelong (φ ∘ π)
        (BlowupExceptionalDivisor.exceptionalDivisor hπ).support := by
  have hnativePSH : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  have hn : n ≠ 0 := Nat.ne_of_gt (dimension_pos_of_pointBlowup hπ)
  have hnative := lelongNumber_eq_iInf_pointBlowup hπ hnativePSH.isThetaPshPotential_zero.1
  simp only [sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    BlowupExceptionalDivisor.support_exceptionalDivisor]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn,
    ← iInf_lelongNumber_eq_two_mul_squaredLog hn]
  simpa only [Function.comp_def] using hnative


/-- The actual exceptional prime carrier supplies an attained source generic
reader from source PSH and genuine pullback geometry alone. Infinite Lelong
values and the admissible dimension-one point divisor remain included. -/
theorem exists_sourceGenericLelong_pointBlowup_minimum
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {x : X} {π : Y → X} (hπ : IsBlowupAlong n ({x} : Set X) π)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsPSH φ) :
    ∃ y ∈ (BlowupExceptionalDivisor.exceptionalDivisor hπ).support,
      (ofFixedModel n Y).sourceGenericLelong (φ ∘ π)
          (BlowupExceptionalDivisor.exceptionalDivisor hπ).support =
        (ofFixedModel n Y).sourceLelong (φ ∘ π) y ∧
      ∀ z ∈ (BlowupExceptionalDivisor.exceptionalDivisor hπ).support,
        (ofFixedModel n Y).sourceGenericLelong (φ ∘ π)
            (BlowupExceptionalDivisor.exceptionalDivisor hπ).support ≤
          (ofFixedModel n Y).sourceLelong (φ ∘ π) z := by
  have hn : 0 < n := dimension_pos_of_pointBlowup hπ
  cases n with
  | zero => omega
  | succ m =>
      have hnativePSH : ManifoldPSH (n := m + 1) φ :=
        (ofFixedModel_isPSH_iff (m + 1) X φ).mp hφ
      have hpull : ManifoldQuasiPlurisubharmonic (n := m + 1) (φ ∘ π) :=
        GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.contMDiff
          hnativePSH.isThetaPshPotential_zero.1.quasiPlurisubharmonic
      obtain ⟨y, hy⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum
        hpull (point_exceptional_carrier_is_prime hπ)
      refine ⟨y, y.property, ?_, ?_⟩
      · rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf] at hy
        simpa only [sourceGenericLelong, sourceLelong_ofFixedModel_eq] using hy.symm
      · intro z hz
        exact iInf_le_of_le z (iInf_le_of_le hz le_rfl)

end SGPT.PSH.VariableComplexAtlas
