import SGPT.Foundations.Analysis.Pending.CoherentIdealCommonModelOrder
import SGPT.Foundations.Analysis.Pending.MultiplierIdealLowerBound


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IntrinsicMultiplierOrder

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  MultiplierIdealLowerBound CoherentIdealCommonModelOrder

universe u

/-- Actual whole-ideal common-model geometry produces the genuine multiplier coefficient equality. -/
theorem actualMultiplierCoefficient_eq_of_common_resolution {m : ℕ} {X Y₀ Y₁ W : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀] [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁] [IsComplexManifold (m + 1) Y₁]
    [TopologicalSpace W] [ChartedSpace (ComplexModel (m + 1)) W] [IsComplexManifold (m + 1) W]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : W → Y₀} {g₁ : W → Y₁}
    (hπ₀ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π₀)
    (hπ₁ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π₁)
    (hg₀ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁) {E₀ : Set Y₀} {E₁ : Set Y₁}
    (hE₀ : IsClosedConnectedSubmanifold (m + 1) E₀ m)
    (hE₁ : IsClosedConnectedSubmanifold (m + 1) E₁ m)
    (hstrict : strictTransform (m + 1) g₀ E₀ = strictTransform (m + 1) g₁ E₁)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) {c : ℝ} (hc : 0 < c) :
    actualMultiplierCoefficient hπ₀ hE₀ hφ hc = actualMultiplierCoefficient hπ₁ hE₁ hφ hc := by
  obtain ⟨V₀, hV₀, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hE₀
  obtain ⟨V₁, hV₁, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hE₁
  subst E₀
  subst E₁
  have hA := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.succ_pos m) hφ.1 hc
  obtain ⟨z, Φ₀, Φ₁, hz₀, hz₁, horder⟩ := exists_common_originalStalkNormalOrder_eq
    hπ₀.1 hπ₁.1 hg₀ hg₁ hcomm V₀ V₁ hE₀.2.2 hE₁.2.2 hstrict _ hA
  apply ENat.natCast_inj.mp
  exact (originalStalkNormalOrder_eq_actualMultiplierCoefficient hπ₀ hE₀ hφ hc (g₀ z) hz₀ Φ₀).symm.trans
    (horder.trans (originalStalkNormalOrder_eq_actualMultiplierCoefficient hπ₁ hE₁ hφ hc (g₁ z) hz₁ Φ₁))

end SGPT.Foundations.Analysis.Pending.IntrinsicMultiplierOrder
