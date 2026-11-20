import SGPT.Foundations.Analysis.Pending.RawGlobalPrimeIdealOrderCharacterization
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

set_option autoImplicit false

/-! # Original raw all-chart ideal order is invariant under genuine modifications -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierOrderModificationInvariance

open FirstPass FirstPass.IEnvelope FirstPass.NonKahlerLocus
  AnalyticModificationLocalDiscrepancy

noncomputable section

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- Genuine whole-source composition supplies all prime tests for the pullback order. -/
theorem iOrder_comp_of_iOrder {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hI : IOrderOnManifold (n := m + 1) u v) :
    IOrderOnManifold (n := m + 1) (fun y => u (π y)) (fun y => v (π y)) := by
  have huP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu
  have hvP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hv
  apply RawGlobalPrimeIdealOrderCharacterization.iOrder_of_all_global_prime_orders huP hvP
  intro Z _ _ _ σ hσ V hdim
  exact (RawGlobalPrimeIdealOrderCharacterization.iOrder_iff_all_global_prime_orders hu hv).mp hI
    Z (π ∘ σ) (AnalyticModificationComposition.isAnalyticModification_comp hπ hσ) V hdim

/-- Both directions retain the actual original ALL-level, ALL-chart weighted order. -/
theorem iOrder_iff_comp {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) :
    IOrderOnManifold (n := m + 1) u v ↔
      IOrderOnManifold (n := m + 1) (fun y => u (π y)) (fun y => v (π y)) := by
  exact ⟨iOrder_comp_of_iOrder hπ hu hv,
    RawMultiplierIdealOrderModificationDescent.iOrder_of_pullback_iOrder hπ hu hv⟩

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierOrderModificationInvariance
