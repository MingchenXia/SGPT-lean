import SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationPointComparison
import SGPT.Foundations.Analysis.Pending.IrreducibleDivisorIdealOrderLelong

set_option autoImplicit false

/-! # Raw ideal order compares whole divisors on genuine global modifications

The original raw functions, actual all-level ideals and genuine modification
geometry supply every regular-point comparison. The actual regular-locus
reader takes the whole divisor infimum, without a local-piece minimum.
-/

open Set Filter
open scoped Topology Manifold ENNReal NNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationGenericComparison

open FirstPass FirstPass.IEnvelope FirstPass.NonKahlerLocus
  DemaillyApproximantDivisorialLelong

noncomputable section

/-- Every genuine global analytic modification and actual whole irreducible
divisor satisfies forward comparison for the original raw all-level ideals. -/
theorem divisorialLelongNumber_comp_le_of_iOrder
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hI : IOrderOnManifold (n := m + 1) u v)
    (E : ClosedIrreducibleAnalyticSubvariety (m + 1) Y) (hEdim : E.dim = m) :
    divisorialLelongNumber m (fun y => v (π y)) E.carrier ≤
      divisorialLelongNumber m (fun y => u (π y)) E.carrier := by
  have huP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu
  have hreader := IrreducibleDivisorIdealOrderLelong.iInf_lelongNumber_eq_regularLocus huP E
  rw [hEdim] at hreader
  change (⨅ z ∈ E.carrier, lelongNumber (n := m + 1) (fun y => v (π y)) z) ≤
    ⨅ z ∈ E.carrier, lelongNumber (n := m + 1) (fun y => u (π y)) z
  rw [hreader]
  refine le_iInf₂ fun y hy => ?_
  exact RawIdealOrderModificationPointComparison.generic_lelong_le_point_of_iOrder
    hπ hu hv hI hy

end
end SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationGenericComparison
