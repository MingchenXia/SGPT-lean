import SGPT.PSH.SourceModificationOrders

/-! # Original multiplier equivalence under a proper modification

The two actual all-chart, all-positive-exponent orders give the entire
original `prop:Ienvbimero`, without extra mass or output-domain assumptions.
-/

set_option autoImplicit false

namespace SGPT.PSH.ModificationOrders

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Both directions of the original multiplier-equivalence pullback criterion. -/
theorem sourceIEquivalent_modification_pullback_iff {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIEquivalent (ofFixedModel n X) u v ↔
      sourceIEquivalent (ofFixedModel n Y) (u ∘ π) (v ∘ π) :=
  and_congr (sourceIOrder_modification_pullback_iff hπ hu hv)
    (sourceIOrder_modification_pullback_iff hπ hv hu)

end SGPT.PSH.ModificationOrders
