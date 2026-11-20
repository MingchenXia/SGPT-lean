import SGPT.PSH.VariableNativeComponent
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

private theorem countable_refinement_neighbors {M I : Type*} [TopologicalSpace M]
    (U : I → Set M) (hU : ∀ i, IsOpen (U i)) (hfin : LocallyFinite U)
    (i : I) [SecondCountableTopology (U i)] :
    {j | (U i ∩ U j).Nonempty}.Countable := by
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense (U i)
  have hcount : (⋃ (p : U i) (_ : p ∈ D), {j | p.val ∈ U j}).Countable :=
    hD.biUnion fun p _ ↦ (hfin.point_finite p.val).countable
  apply hcount.mono
  intro j hj
  obtain ⟨y, hyi, hyj⟩ := hj
  obtain ⟨p, hpD, hpj⟩ := hdense.exists_mem_open
    ((hU j).preimage continuous_subtype_val) ⟨⟨y, hyi⟩, hyj⟩
  exact mem_iUnion₂.mpr ⟨p, hpD, hpj⟩

private def refinementReach {M I : Type*} (U : I → Set M) (i : I) : ℕ → Set I
  | 0 => {i}
  | k + 1 => ⋃ j ∈ refinementReach U i k, {l | (U j ∩ U l).Nonempty}

private theorem countable_refinementReach {M I : Type*} [TopologicalSpace M]
    (U : I → Set M) (hU : ∀ i, IsOpen (U i)) (hfin : LocallyFinite U)
    (hsc : ∀ i, SecondCountableTopology (U i)) (i : I) (k : ℕ) :
    (refinementReach U i k).Countable := by
  induction k with
  | zero => exact countable_singleton i
  | succ k hk =>
    exact hk.biUnion fun j _ ↦ by
      let := hsc j
      exact countable_refinement_neighbors U hU hfin j

/-- Paracompactness and connectedness produce a genuine countable cover by original charts. -/
theorem secondCountable_of_paracompact_connected_charted
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [SecondCountableTopology H] [ParacompactSpace M] [ConnectedSpace M] :
    SecondCountableTopology M := by
  classical
  obtain ⟨U, hU, hcover, hfin, hsub⟩ := precise_refinement
    (fun p : M ↦ (chartAt H p).source) (fun p ↦ (chartAt H p).open_source)
      (iUnion_eq_univ_iff.mpr fun p ↦ ⟨p, mem_chart_source H p⟩)
  have hsc (i : M) : SecondCountableTopology (U i) := by
    let := (chartAt H i).secondCountableTopology_source
    exact (Topology.IsEmbedding.inclusion (hsub i)).secondCountableTopology
  let p : M := Classical.arbitrary M
  obtain ⟨i, hpi⟩ := iUnion_eq_univ_iff.mp hcover p
  let R : Set M := ⋃ k : ℕ, refinementReach U i k
  have hR : R.Countable := countable_iUnion fun k ↦
    countable_refinementReach U hU hfin hsc i k
  have hiR : i ∈ R := mem_iUnion.mpr ⟨0, mem_singleton i⟩
  have hneighbor {j l : M} (hj : j ∈ R) (hl : (U j ∩ U l).Nonempty) : l ∈ R := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨k + 1, mem_iUnion₂.mpr ⟨j, hk, hl⟩⟩
  let W : Set M := ⋃ j ∈ R, U j
  have hWo : IsOpen W := isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hU j
  have hcomp : Wᶜ = ⋃ j ∈ Rᶜ, U j := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hzj⟩ := iUnion_eq_univ_iff.mp hcover z
      exact mem_iUnion₂.mpr ⟨j, fun hj ↦ hz (mem_iUnion₂.mpr ⟨j, hj, hzj⟩), hzj⟩
    · intro hzoutside hz
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzoutside
      obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hz
      exact hj (hneighbor hl ⟨z, hzl, hzj⟩)
  have hWc : IsClosed W := by
    rw [← isOpen_compl_iff, hcomp]
    exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hU j
  have hWall : W = univ := (show IsClopen W from ⟨hWc, hWo⟩).eq_univ
    ⟨p, mem_iUnion₂.mpr ⟨i, hiR, hpi⟩⟩
  apply ChartedSpace.secondCountable_of_countable_cover H
    (s := R) _ hR
  apply eq_univ_of_forall
  intro z
  have hz : z ∈ W := hWall.symm ▸ mem_univ z
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨j, hj, hsub j hzj⟩

namespace VariableComplexAtlas

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- The original closed connected component inherits paracompactness and acquires a countable atlas. -/
theorem componentSecondCountable [ParacompactSpace X] (x : X) :
    SecondCountableTopology (A.componentOpen x) := by
  let := A.componentChartedSpace x
  have hclosed : IsClosed (A.componentOpen x : Set X) := isClosed_connectedComponent
  let := hclosed.isClosedEmbedding_subtypeVal.paracompactSpace
  have hconn : IsConnected (A.componentOpen x : Set X) := isConnected_connectedComponent
  let := Subtype.connectedSpace hconn
  exact secondCountable_of_paracompact_connected_charted
    (ComplexModel (A.pointDimension x)) (A.componentOpen x)

/-- The book's original Hausdorff/paracompact assumptions supply every native manifold field. -/
theorem componentComplexManifold_of_paracompact [T2Space X] [ParacompactSpace X] (x : X) :
    letI := A.componentChartedSpace x
    IsComplexManifold (A.pointDimension x) (A.componentOpen x) := by
  let := A.componentChartedSpace x
  let := A.componentSecondCountable x
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := inferInstance
    toIsManifold := A.componentIsManifold x }

end VariableComplexAtlas
end SGPT.PSH
