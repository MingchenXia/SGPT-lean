import SGPT.Bergman.SiuNativeSectionCartier
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

/-! An actual global generating family manufactures one actual native
holomorphic section nonzero on a dense locus, on disconnected manifolds too. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Pick an actual original section nonzero on each original connected
component and glue it on those genuine open components. Every nonempty
open set meets its nonzero locus, by the actual analytic identity theorem. -/
theorem exists_dense_native_section_of_global_generation {ι : Type}
    (L : HermitianHolomorphicLineBundle n X)
    (t : ι → HolomorphicSections (n := n) L.Fiber)
    (hgen : ∀ p : X, ∃ i : ι, t i p ≠ 0) :
    ∃ s : HolomorphicSections (n := n) L.Fiber,
      ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0 := by
  classical
  let _ : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel n) X
  let anchor : ConnectedComponents X → X := Quotient.out
  have hanchor : ∀ c : ConnectedComponents X, ConnectedComponents.mk (anchor c) = c :=
    Quotient.out_eq
  choose j hj using fun c : ConnectedComponents X => hgen (anchor c)
  have heq : ∀ {p y : X}, y ∈ connectedComponent p →
      ConnectedComponents.mk y = ConnectedComponents.mk p := fun {_ _} hy =>
    ConnectedComponents.coe_eq_coe'.mpr hy
  let s : HolomorphicSections (n := n) L.Fiber := {
    toFun := fun p => t (j (ConnectedComponents.mk p)) p
    contMDiff_toFun := by
      intro p
      apply (t (j (ConnectedComponents.mk p))).contMDiff p |>.congr_of_eventuallyEq
      filter_upwards [(isOpen_connectedComponent (x := p)).mem_nhds mem_connectedComponent] with y hy
      rw [heq hy] }
  refine ⟨s, fun U hU hUne => ?_⟩
  obtain ⟨p, hpU⟩ := hUne
  let c := ConnectedComponents.mk p
  let v := t (j c)
  let Z := sectionZeroSet L.Fiber v
  have hZ : IsClosed (interior Z) :=
    (sectionZeroSet_isComplexAnalytic L.Fiber v).isClosed_interior
  by_contra hnone
  push Not at hnone
  have hsub : U ∩ connectedComponent p ⊆ Z := by
    intro y hy
    have hyzero := hnone y hy.1
    change t (j (ConnectedComponents.mk y)) y = 0 at hyzero
    change t (j (ConnectedComponents.mk p)) y = 0
    rwa [heq hy.2] at hyzero
  have hpZ : p ∈ interior Z := mem_interior.mpr
    ⟨U ∩ connectedComponent p, hsub, hU.inter (isOpen_connectedComponent (x := p)), hpU, mem_connectedComponent⟩
  have haZ : anchor c ∈ interior Z :=
    (IsClopen.connectedComponent_subset ⟨hZ, isOpen_interior⟩ hpZ)
      (ConnectedComponents.coe_eq_coe'.mp (hanchor c))
  have haZ' : anchor c ∈ Z := interior_subset haZ
  exact hj c haZ'

end SGPT.BDivisor.NSKodaira
