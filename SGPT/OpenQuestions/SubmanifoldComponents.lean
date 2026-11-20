import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import SGPT.Foundations.Analysis.Pending.RegularPointDimension
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-!
# Connected components of a closed complex submanifold

For a closed complex submanifold `Y ⊆ X` (closed, and regular of some dimension
at each of its points; the dimension may vary), every connected component of `Y`
is a closed connected complex submanifold of a (unique) dimension. This is used
to see that `SGPT.OpenQuestions.naturalKahlerTraceExtensionStatement`
(`conj:exttracegeneral`) quantifies over all connected components of `Y`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.OpenQuestions

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped Topology

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The points at which `Y` is regular of dimension `k`. -/
def submanifoldDimPart (Y : Set M) (k : ℕ) : Set M := {x | RegularAtDim (n := n) Y x k}

omit [IsComplexManifold n M] in
theorem submanifoldDimPart_subset (Y : Set M) (k : ℕ) : submanifoldDimPart (n := n) Y k ⊆ Y :=
  fun _ hx => hx.2.1

theorem exists_open_subset_submanifoldDimPart {Y : Set M} {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) Y x k) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Y ∩ U ⊆ submanifoldDimPart (n := n) Y k := by
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp (RegularPatchNeighborhood.eventually_regularAtDim hx)
  exact ⟨U, hUo, hxU, fun y hy => hUsub hy.2 hy.1⟩

theorem regularAtDim_submanifoldDimPart {Y : Set M} {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) Y x k) :
    RegularAtDim (n := n) (submanifoldDimPart (n := n) Y k) x k := by
  obtain ⟨U, hUo, hxU, hsub⟩ := exists_open_subset_submanifoldDimPart hx
  refine RegularPointDimension.regularAtDim_of_inter_eq hUo hxU ?_ hx
  ext y
  exact ⟨fun h => ⟨hsub h, h.2⟩, fun h => ⟨submanifoldDimPart_subset Y k h.1, h.2⟩⟩

theorem isClosed_submanifoldDimPart {Y : Set M} (hY : IsClosedSubmanifold n Y) (k : ℕ) :
    IsClosed (submanifoldDimPart (n := n) Y k) := by
  apply isClosed_of_closure_subset
  intro x hx
  have hxY : x ∈ Y := hY.1.closure_subset_iff.mpr (submanifoldDimPart_subset Y k) hx
  obtain ⟨j, hj⟩ := hY.2 x hxY
  obtain ⟨U, hUo, hxU, hsub⟩ := exists_open_subset_submanifoldDimPart hj
  obtain ⟨z, hzU, hzk⟩ := mem_closure_iff.mp hx U hUo hxU
  have hzj : z ∈ submanifoldDimPart (n := n) Y j := hsub ⟨submanifoldDimPart_subset Y k hzk, hzU⟩
  have hjk : j = k := RegularPointDimension.eq_of_regularAtDim hzj hzk
  subst hjk
  exact hj

/-- The dimension parts are relatively clopen in `Y`. -/
theorem isClopen_preimage_submanifoldDimPart {Y : Set M} (hY : IsClosedSubmanifold n Y)
    (k : ℕ) : IsClopen ((Subtype.val : Y → M) ⁻¹' submanifoldDimPart (n := n) Y k) := by
  refine ⟨(isClosed_submanifoldDimPart hY k).preimage continuous_subtype_val, ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨U, hUo, hxU, hsub⟩ := exists_open_subset_submanifoldDimPart hp
  exact ⟨(Subtype.val : Y → M) ⁻¹' U, fun q hq => hsub ⟨q.2, hq⟩,
    hUo.preimage continuous_subtype_val, hxU⟩

/-- Every connected component of a closed complex submanifold is a closed
connected complex submanifold, of the dimension of `Y` at any of its points. -/
theorem isClosedConnectedSubmanifold_connectedComponentIn {Y : Set M}
    (hY : IsClosedSubmanifold n Y) {y : M} {k : ℕ} (hyk : RegularAtDim (n := n) Y y k) :
    IsClosedConnectedSubmanifold n (connectedComponentIn Y y) k := by
  have hy : y ∈ Y := hyk.2.1
  set D := submanifoldDimPart (n := n) Y k with hD
  have hyD : y ∈ D := hyk
  -- the component of `Y` lies in the dimension part
  have hCD : connectedComponentIn Y y ⊆ D := by
    rw [connectedComponentIn_eq_image hy]
    rintro _ ⟨q, hq, rfl⟩
    exact (isClopen_preimage_submanifoldDimPart hY k).connectedComponent_subset hyD hq
  have hCeq : connectedComponentIn Y y = connectedComponentIn D y := by
    apply Subset.antisymm
    · exact (isConnected_connectedComponentIn_iff.mpr hy).isPreconnected.subset_connectedComponentIn
        (mem_connectedComponentIn hy) hCD
    · exact connectedComponentIn_mono y (submanifoldDimPart_subset Y k)
  have hDreg : ∀ x ∈ D, RegularAtDim (n := n) D x k := fun x hx =>
    regularAtDim_submanifoldDimPart hx
  have hk : k ≤ n := hyk.1
  let : ChartedSpace (ComplexModel k) D := SubmanifoldChartedSpace.chartedSpace hk hDreg
  have : LocallyConnectedSpace D := ChartedSpace.locallyConnectedSpace (ComplexModel k) D
  have hDc : IsClosed D := isClosed_submanifoldDimPart hY k
  rw [hCeq]
  refine ⟨?_, isConnected_connectedComponentIn_iff.mpr hyD, ?_⟩
  · rw [connectedComponentIn_eq_image hyD]
    exact hDc.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · intro x hx
    have hxD : x ∈ D := connectedComponentIn_subset D y hx
    have hcomp := connectedComponentIn_eq hx
    obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp
      (isOpen_connectedComponent (x := (⟨x, hxD⟩ : D)))
    have hxW : x ∈ W := by
      have : (⟨x, hxD⟩ : D) ∈ (Subtype.val : D → M) ⁻¹' W := by
        rw [hWeq]; exact mem_connectedComponent
      exact this
    refine RegularPointDimension.regularAtDim_of_inter_eq hWo hxW ?_ (hDreg x hxD)
    ext z
    constructor
    · rintro ⟨hzD, hzW⟩
      refine ⟨?_, hzW⟩
      rw [hcomp, connectedComponentIn_eq_image hxD]
      refine ⟨⟨z, hzD⟩, ?_, rfl⟩
      have : (⟨z, hzD⟩ : D) ∈ (Subtype.val : D → M) ⁻¹' W := hzW
      rwa [hWeq] at this
    · rintro ⟨hzC, hzW⟩
      exact ⟨connectedComponentIn_subset D y hzC, hzW⟩

/-- Every point of a closed complex submanifold lies in a connected component
that is a closed connected complex submanifold. -/
theorem exists_isClosedConnectedSubmanifold_connectedComponentIn {Y : Set M}
    (hY : IsClosedSubmanifold n Y) {y : M} (hy : y ∈ Y) :
    ∃ k, IsClosedConnectedSubmanifold n (connectedComponentIn Y y) k := by
  obtain ⟨k, hk⟩ := hY.2 y hy
  exact ⟨k, isClosedConnectedSubmanifold_connectedComponentIn hY hk⟩

variable (n) in
/-- The connected components of `Y ⊆ X`, each together with a dimension in which
it is a closed connected complex submanifold of `X`. For a closed complex
submanifold `Y` every connected component is a closed connected submanifold of a
unique dimension, so this indexes all connected components of `Y`. -/
def ClosedSubmanifoldComponent (Y : Set M) : Type u :=
  {p : Set M × ℕ // (∃ y ∈ Y, p.1 = connectedComponentIn Y y) ∧
    IsClosedConnectedSubmanifold n p.1 p.2}

/-- For a closed complex submanifold `Y`, every connected component of `Y` occurs
in `ClosedSubmanifoldComponent n Y`. -/
theorem exists_closedSubmanifoldComponent {Y : Set M} (hY : IsClosedSubmanifold n Y)
    {y : M} (hy : y ∈ Y) :
    ∃ c : ClosedSubmanifoldComponent n Y, c.1.1 = connectedComponentIn Y y := by
  obtain ⟨k, hk⟩ := exists_isClosedConnectedSubmanifold_connectedComponentIn hY hy
  exact ⟨⟨(connectedComponentIn Y y, k), ⟨y, hy, rfl⟩, hk⟩, rfl⟩

omit [IsComplexManifold n M] in
/-- Each connected component occurs exactly once: the dimension is determined. -/
theorem ClosedSubmanifoldComponent.ext_of_set {Y : Set M}
    (c c' : ClosedSubmanifoldComponent n Y) (h : c.1.1 = c'.1.1) : c = c' := by
  obtain ⟨x, hx⟩ := c.2.2.2.1.nonempty
  have hx' : x ∈ c'.1.1 := h ▸ hx
  have hk : c.1.2 = c'.1.2 := by
    have h1 := c.2.2.2.2 x hx
    have h2 := c'.2.2.2.2 x hx'
    rw [← h] at h2
    exact RegularPointDimension.eq_of_regularAtDim h1 h2
  exact Subtype.ext (Prod.ext h hk)

end SGPT.OpenQuestions
