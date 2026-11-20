import SGPT.Unibranch.ComplexSpaceUnibranchComplement

/-! Genuine global analytic-complement connectedness in the ORIGINAL
unibranch topology. Blueprint: complex-space-unibranch-global-complement.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Actual original connected-complement neighborhoods produce literal
complement density in EVERY original open set. -/
theorem IsUnibranch.subset_closure_diff_of_isOpen {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z U : Set X.obj.left} (hZa : X.IsAnalyticSubset Z)
    (hZ : interior Z = ∅) (hU : IsOpen U) : U ⊆ closure (U \ Z) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro O hO
  obtain ⟨V,_hV,_hxV,hVU,_hVc,hVD⟩ := hX.exists_connected_neighborhood_diff hZa hZ x
    (hU.inter isOpen_interior) ⟨hx,mem_interior_iff_mem_nhds.mpr hO⟩
  obtain ⟨z,hzV,hzZ⟩ := hVD.nonempty
  exact ⟨z,interior_subset (hVU hzV).2,(hVU hzV).1,hzZ⟩

/-- The ENTIRE actual complement in a connected original open set is
connected, internally from original unibranch germs and actual closure geometry. -/
theorem IsUnibranch.isConnected_diff_of_isConnected_open {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z U : Set X.obj.left} (hZa : X.IsAnalyticSubset Z)
    (hZ : interior Z = ∅) (hU : IsOpen U) (hUc : IsConnected U) :
    IsConnected (U \ Z) := by
  have hdense := hX.subset_closure_diff_of_isOpen hZa hZ hU
  have hne : (U \ Z).Nonempty := by
    obtain ⟨x,hx⟩ := hUc.nonempty
    obtain ⟨V,_hV,_hxV,hVU,_hVc,hVD⟩ := hX.exists_connected_neighborhood_diff hZa hZ x hU hx
    obtain ⟨z,hzV,hzZ⟩ := hVD.nonempty
    exact ⟨z,hVU hzV,hzZ⟩
  refine ⟨hne,isPreconnected_closed_iff.mpr ?_⟩
  intro K L hK hL hcover hmeetK hmeetL
  let A : Set X.obj.left := (U \ Z) ∩ K
  let B : Set X.obj.left := (U \ Z) ∩ L
  have hcoverAB : U \ Z ⊆ A ∪ B := by
    intro z hz
    rcases hcover hz with hzk | hzl
    · exact Or.inl ⟨hz,hzk⟩
    · exact Or.inr ⟨hz,hzl⟩
  have hcoverU : U ⊆ closure A ∪ closure B := by
    intro z hz
    have h := closure_mono hcoverAB (hdense hz)
    rwa [closure_union] at h
  have hmA : (U ∩ closure A).Nonempty := by
    obtain ⟨z,hzU,hzK⟩ := hmeetK
    exact ⟨z,hzU.1,subset_closure ⟨hzU,hzK⟩⟩
  have hmB : (U ∩ closure B).Nonempty := by
    obtain ⟨z,hzU,hzL⟩ := hmeetL
    exact ⟨z,hzU.1,subset_closure ⟨hzU,hzL⟩⟩
  obtain ⟨x,hxU,hxA,hxB⟩ := isPreconnected_closed_iff.mp hUc.isPreconnected _ _
    isClosed_closure isClosed_closure hcoverU hmA hmB
  obtain ⟨V,hV,hxV,hVU,_hVc,hVD⟩ := hX.exists_connected_neighborhood_diff hZa hZ x hU hxU
  have hcoverV : V \ Z ⊆ K ∪ L := fun z hz => hcover ⟨hVU hz.1,hz.2⟩
  have hmVK : ((V \ Z) ∩ K).Nonempty := by
    obtain ⟨z,hzV,hzA⟩ := mem_closure_iff.mp hxA V hV hxV
    exact ⟨z,⟨hzV,hzA.1.2⟩,hzA.2⟩
  have hmVL : ((V \ Z) ∩ L).Nonempty := by
    obtain ⟨z,hzV,hzB⟩ := mem_closure_iff.mp hxB V hV hxV
    exact ⟨z,⟨hzV,hzB.1.2⟩,hzB.2⟩
  obtain ⟨z,hzV,hzK,hzL⟩ := isPreconnected_closed_iff.mp hVD.isPreconnected _ _
    hK hL hcoverV hmVK hmVL
  exact ⟨z,⟨hVU hzV.1,hzV.2⟩,hzK,hzL⟩

end SGPT.Unibranch.SourceReducedComplexSpace
