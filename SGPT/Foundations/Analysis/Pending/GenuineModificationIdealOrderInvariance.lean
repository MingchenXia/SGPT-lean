import SGPT.Foundations.Analysis.Pending.RawMultiplierOrderModificationInvariance
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

set_option autoImplicit false

/-! # Genuine right potentials and modification order in every dimension -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance

open FirstPass FirstPass.IEnvelope AnalyticModificationLocalDiscrepancy

noncomputable section

private theorem genuine_comp_of_dim_zero
    {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel 0) ∞ π)
    {v : X → EReal} (hv : IsGlobalQuasiPshPotential (n := 0) v) :
    IsGlobalQuasiPshPotential (n := 0) (fun y => v (π y)) := by
  apply GlobalPotentialPullback.isGlobalQuasiPshPotential_comp hπ hv.1
  intro y U _hU hy
  let e : ComplexChart 0 X := complexChartAt (n := 0) (π y)
  have he : π y ∈ e.val.source := mem_complexChartAt_source (π y)
  obtain ⟨x, hx, hnon⟩ := hv.2 (π y) e.val.source e.val.open_source he
  have hxy : x = π y := e.val.injOn hx he (Subsingleton.elim _ _)
  refine ⟨y, hy, ?_⟩
  simpa only [hxy] using hnon

/-- Genuine source nondegeneracy internally supplies both actual zero-dimensional
weighted orders; positive dimension retains the raw modification-order theorem. -/
theorem iOrder_iff_comp
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    IOrderOnManifold (n := n) u v ↔
      IOrderOnManifold (n := n) (fun y => u (π y)) (fun y => v (π y)) := by
  cases n with
  | zero =>
    have hvπ := genuine_comp_of_dim_zero hπ.1 hv
    exact ⟨fun _ => ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right
      (fun y => u (π y)) hvπ,
      fun _ => ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right u hv⟩
  | succ m =>
    exact RawMultiplierOrderModificationInvariance.iOrder_iff_comp hπ hu hv.1

end
end SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance
