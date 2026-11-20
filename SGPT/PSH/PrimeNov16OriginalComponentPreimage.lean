import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-! Exact full original component preimages, not merely generic pairing.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.PSH.PrimeNov16OriginalComponentPreimage
open SGPT.Unibranch SourceReducedComplexSpace

private theorem identity_pb (Y : SourceReducedComplexSpace) : IsProperBimeromorphic (𝟙 Y) := by
  refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
  exact IsIsoOver.id_of_isOpen Y (by simp)

theorem exists_actual_component_preimage_pairing
    {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (G : S ⟶ Y) (hG : IsProperBimeromorphic G) :
    ∃ pair : ConnectedComponents Y.obj.left ≃ ConnectedComponents S.obj.left,
      ∀ c, G.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet c =
        OriginalSmoothComponents.componentSet (pair c) := by
  obtain ⟨E₀, E₁, _hE₀, _hE₁, _hi₀, _hi₁, _ht₀, ht₁, pair, hpair⟩ :=
    PrimeNov16OriginalComponentPairing.exists_original_good_component_pairing hS hY G (𝟙 Y) hG (identity_pb Y)
  let B := E₀ ∪ E₁
  have hBt : interior B = ∅ := ht₁
  have hmap (c : ConnectedComponents Y.obj.left) (z : S.obj.left)
      (hz : z ∈ OriginalSmoothComponents.componentSet (pair c)) :
      G.hom.left.base z ∈ OriginalSmoothComponents.componentSet c := by
    have hnot : ¬ OriginalSmoothComponents.componentSet c ⊆ B := by
      intro hsub
      obtain ⟨x, hx⟩ := (OriginalSmoothComponents.component_isConnected c).nonempty
      have hi := interior_maximal hsub (OriginalSmoothComponents.component_isClopen hY c).2 hx
      rw [hBt] at hi
      exact hi
    obtain ⟨x, hxc, hxB⟩ := not_subset.mp hnot
    have hximage : x ∈ PrimeNov16OriginalComponentPairing.componentGoodImage (𝟙 Y) B c :=
      ⟨x, ⟨hxc, hxB⟩, rfl⟩
    have hxsource : x ∈ PrimeNov16OriginalComponentPairing.componentGoodImage G B (pair c) :=
      (hpair c).symm ▸ hximage
    obtain ⟨u, ⟨huc, _huGood⟩, hGu⟩ := hxsource
    have hcomp : OriginalSmoothComponents.componentSet (pair c) = connectedComponent u := by
      change ConnectedComponents.mk u = pair c at huc
      rw [← huc, OriginalSmoothComponents.componentSet_eq_connectedComponent]
    have hzconn : z ∈ connectedComponent u := hcomp ▸ hz
    have hGconn : G.hom.left.base z ∈ connectedComponent (G.hom.left.base u) :=
      G.hom.left.base.hom.continuous.image_connectedComponent_subset u ⟨z, hzconn, rfl⟩
    have hlabels : ConnectedComponents.mk (G.hom.left.base z) = ConnectedComponents.mk (G.hom.left.base u) :=
      ConnectedComponents.coe_eq_coe'.mpr hGconn
    change ConnectedComponents.mk (G.hom.left.base z) = c
    exact hlabels.trans ((congrArg ConnectedComponents.mk hGu).trans hxc)
  refine ⟨pair, ?_⟩
  intro c
  ext z
  constructor
  · intro hz
    let d := pair.symm (ConnectedComponents.mk z)
    have hzd : z ∈ OriginalSmoothComponents.componentSet (pair d) := (pair.apply_symm_apply _).symm
    have hgd := hmap d z hzd
    have heq : d = c := (show ConnectedComponents.mk (G.hom.left.base z) = d from hgd).symm.trans hz
    exact heq ▸ hzd
  · intro hz
    exact hmap c z hz

end SGPT.PSH.PrimeNov16OriginalComponentPreimage
