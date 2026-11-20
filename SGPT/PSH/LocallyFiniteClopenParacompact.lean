import SGPT.PSH.LocallyFiniteClopenImage
import SGPT.PSH.LocallyFiniteSubordinate
import Mathlib.Topology.Compactness.Paracompact

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open scoped Topology

universe u

/-- Honest pure topology: an ACTUAL locally finite clopen cover with ACTUAL
paracompact subtypes internally manufactures every whole-space refinement. -/
theorem paracompactSpace_of_locallyFinite_clopen_cover {X ι : Type u}
    [TopologicalSpace X] (U : ι → Opens X) (hclosed : ∀ c, IsClosed (U c : Set X))
    (hU : LocallyFinite (fun c => (U c : Set X))) (hcover : ⋃ c, (U c : Set X) = univ)
    (hPara : ∀ c, ParacompactSpace (U c)) : ParacompactSpace X where
  locallyFinite_refinement α s ho hc := by
    classical
    have href : ∀ c, ∃ v : α → Set (U c), (∀ i, IsOpen (v i)) ∧ (⋃ i, v i) = univ ∧
        LocallyFinite v ∧ ∀ i, v i ⊆ (Subtype.val : U c → X) ⁻¹' s i := by
      intro c
      let := hPara c
      apply precise_refinement (fun i => (Subtype.val : U c → X) ⁻¹' s i)
        (fun i => (ho i).preimage continuous_subtype_val)
      exact iUnion_eq_univ_iff.mpr fun p => iUnion_eq_univ_iff.mp hc p.val
    choose v hvopen hvcover hvLF hvsub using href
    refine ⟨(c : ι) × α, fun t => (Subtype.val : U t.1 → X) '' v t.1 t.2, ?_, ?_, ?_, ?_⟩
    · intro t
      exact (U t.1).isOpen.isOpenMap_subtype_val _ (hvopen t.1 t.2)
    · apply iUnion_eq_univ_iff.mpr
      intro x
      obtain ⟨c, hxc⟩ := iUnion_eq_univ_iff.mp hcover x
      obtain ⟨i, hxi⟩ := iUnion_eq_univ_iff.mp (hvcover c) ⟨x, hxc⟩
      exact ⟨⟨c, i⟩, ⟨x, hxc⟩, hxi, rfl⟩
    · apply locallyFinite_sigma_of_subordinate (fun c => (U c : Set X))
        (fun c i => (Subtype.val : U c → X) '' v c i) hU
      · intro c
        exact locallyFinite_clopen_subtype_images (U c) (hclosed c) (v c) (hvLF c)
      · intro c i x hx
        obtain ⟨p, _hp, rfl⟩ := hx
        exact p.property
    · rintro ⟨c, i⟩
      refine ⟨i, ?_⟩
      rintro x ⟨p, hp, rfl⟩
      exact hvsub c i hp

end SGPT.PSH
