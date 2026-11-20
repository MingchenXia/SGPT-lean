import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Opens

set_option autoImplicit false
namespace SGPT.PSH
open Set Filter TopologicalSpace
open scoped Topology

/-- A genuine locally finite family on an actual clopen subtype retains local
finiteness of its literal inclusion images on the original topology. -/
theorem locallyFinite_clopen_subtype_images {X ι : Type*} [TopologicalSpace X]
    (U : Opens X) (hclosed : IsClosed (U : Set X)) (f : ι → Set U)
    (hf : LocallyFinite f) : LocallyFinite (fun i => Subtype.val '' f i) := by
  intro x
  by_cases hx : x ∈ U
  · let p : U := ⟨x, hx⟩
    obtain ⟨N, hN, hfinite⟩ := hf p
    refine ⟨Subtype.val '' N, U.isOpen.isOpenMap_subtype_val.image_mem_nhds hN,
      hfinite.subset ?_⟩
    intro i hi
    obtain ⟨y, ⟨q, hq, hqy⟩, ⟨r, hr, hry⟩⟩ := hi
    have hqr : q = r := Subtype.ext (hqy.trans hry.symm)
    exact ⟨q, hq, hqr.symm ▸ hr⟩
  · refine ⟨(U : Set X)ᶜ, hclosed.isOpen_compl.mem_nhds hx, Set.finite_empty.subset ?_⟩
    intro i hi
    obtain ⟨y, ⟨p, _hp, rfl⟩, hy⟩ := hi
    exact (hy p.property).elim

end SGPT.PSH
