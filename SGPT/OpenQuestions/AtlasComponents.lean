import SGPT.PSH.VariableNativeComponent
import Mathlib.Topology.Connected.LocallyConnected

/-! Actual finite clopen components of a compact varying-dimensional source
manifold. This supplies the topological step for disconnected trace questions;
it does not assert a current-restriction or trace-assembly theorem. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.OpenQuestions.VariableAtlasComponents

open Set Filter Metric
open scoped Topology
open SGPT.PSH
open SGPT.Foundations.Analysis.FirstPass

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual fiber of the original connected-component quotient. -/
def componentCarrier (c : ConnectedComponents X) : Set X :=
  {x | ConnectedComponents.mk x = c}

/-- Literal finite component index, actual clopen connected compact carriers,
pairwise disjointness and the whole-space cover, all produced from the atlas. -/
theorem finite_component_decomposition (A : VariableComplexAtlas X) [CompactSpace X] :
    Finite (ConnectedComponents X) ∧
      (∀ c : ConnectedComponents X,
        IsClopen (componentCarrier c) ∧ IsConnected (componentCarrier c) ∧
          IsCompact (componentCarrier c)) ∧
      Pairwise (fun c d : ConnectedComponents X ↦
        Disjoint (componentCarrier c) (componentCarrier d)) ∧
      (⋃ c : ConnectedComponents X, componentCarrier c) = univ := by
  let : LocallyConnectedSpace X := A.locallyConnectedSpace_of_variableAtlas
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have heq : componentCarrier (ConnectedComponents.mk x) = connectedComponent x := by
      ext y
      exact ConnectedComponents.coe_eq_coe'
    rw [heq]
    exact ⟨isClopen_connectedComponent, isConnected_connectedComponent,
      isClosed_connectedComponent.isCompact⟩
  · intro c d hcd
    apply disjoint_left.mpr
    intro x hxc hxd
    exact hcd (hxc.symm.trans hxd)
  · apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk x, rfl⟩

end SGPT.OpenQuestions.VariableAtlasComponents
