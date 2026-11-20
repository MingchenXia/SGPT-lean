import SGPT.Unibranch.ComplexSpaceUnibranchComplement
import SGPT.Unibranch.HironakaG11ModificationCalculus

/-! Actual full connected fibers over the ORIGINAL intrinsic unibranch
space, with no incoming connected-fiber certificate or Hironaka development.
Blueprint: complex-space-unibranch-fibers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Actual original isomorphism-over data transport connectedness of a
subset to its LITERAL full inverse image. -/
theorem IsIsoOver.isConnected_preimage_of_subset {X Y : SourceReducedComplexSpace}
    {π : Y ⟶ X} {T : Set X.obj.left} (hπ : IsIsoOver π T)
    {U : Set X.obj.left} (hU : IsConnected U) (hUT : U ⊆ T) :
    IsConnected (π.hom.left.base ⁻¹' U) := by
  obtain ⟨V,j,hj,hjr,hk,hkr⟩ := hπ
  let H : V ≃ₜ T := hk.base_open.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hkr)
  let R : U → V := fun u => H.symm ⟨u.val,hUT u.property⟩
  have hR : Continuous R := H.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  let F : U → Y.obj.left := fun u => j.base (R u)
  have hF : Continuous F := j.base.hom.continuous.comp hR
  have hread (u : U) : π.hom.left.base (F u) = u.val := by
    have h := congrArg Subtype.val (H.apply_symm_apply (⟨u.val,hUT u.property⟩ : T))
    exact h
  have hrange : range F = π.hom.left.base ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      change π.hom.left.base (F u) ∈ U
      rw [hread]
      exact u.property
    · intro hy
      have hyj : y ∈ range j.base := by rw [hjr];exact hUT hy
      obtain ⟨v,hv⟩ := hyj
      let u : U := ⟨π.hom.left.base y,hy⟩
      have hRv : R u = v := by
        apply H.injective
        apply Subtype.ext
        have h := congrArg Subtype.val (H.apply_symm_apply (⟨u.val,hUT u.property⟩ : T))
        change (j ≫ π.hom.left).base (R u) = (j ≫ π.hom.left).base v
        exact h.trans (by change π.hom.left.base y = π.hom.left.base (j.base v);rw [hv])
      exact ⟨u,by change j.base (R u) = y;rw [hRv,hv]⟩
  let singularIsoSubsetConnected : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  rw [← hrange]
  exact isConnected_range hF

/-- The literal FULL inverse is connected in arbitrarily small original
neighborhoods, internally using actual unibranch thin-complement geometry. -/
theorem IsProperBimeromorphic.exists_connected_preimage_neighborhood
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) (x : X.obj.left) {N : Set X.obj.left} (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ U : Set X.obj.left,IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧ IsConnected (π.hom.left.base ⁻¹' U) := by
  obtain ⟨Z,hZa,hZ,hpre,hiso⟩ := hπ.2
  obtain ⟨U,hU,hxU,hUN,_hUc,hUdiff⟩ := hX.exists_connected_neighborhood_diff hZa hZ x hN hxN
  have hconn := hiso.isConnected_preimage_of_subset hUdiff (fun y hy => hy.2)
  have hconn' : IsConnected ((π.hom.left.base ⁻¹' U) \ (π.hom.left.base ⁻¹' Z)) := by
    simpa only [preimage_sdiff] using hconn
  have hdense : (π.hom.left.base ⁻¹' U) ⊆
      closure ((π.hom.left.base ⁻¹' U) \ (π.hom.left.base ⁻¹' Z)) := by
    intro y hy
    rw [mem_closure_iff_nhds]
    intro O hO
    have hopen : IsOpen (interior O ∩ π.hom.left.base ⁻¹' U) :=
      isOpen_interior.inter (hU.preimage π.hom.left.base.hom.continuous)
    have hyopen : y ∈ interior O ∩ π.hom.left.base ⁻¹' U :=
      ⟨mem_interior_iff_mem_nhds.mpr hO,hy⟩
    have hnot : ¬ interior O ∩ π.hom.left.base ⁻¹' U ⊆ π.hom.left.base ⁻¹' Z := by
      intro hsub
      have h := interior_maximal hsub hopen hyopen
      rw [hpre] at h
      exact h
    obtain ⟨z,⟨hzO,hzU⟩,hzZ⟩ := not_subset.mp hnot
    exact ⟨z,interior_subset hzO,hzU,hzZ⟩
  exact ⟨U,hU,hxU,hUN,hconn'.subset_closure sdiff_subset hdense⟩

/-- The ORIGINAL intrinsic unibranch condition actually produces connected
literal proper-bimeromorphic fibers; no fiber connectedness input. -/
theorem IsProperBimeromorphic.isConnected_fiber_of_isUnibranch
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) (x : X.obj.left) : IsConnected (π.hom.left.base ⁻¹' {x}) := by
  let singularOriginalFiberHausdorff : T2Space Y.obj.left.toPresheafedSpace := Y.property.1
  have hFc : IsCompact (π.hom.left.base ⁻¹' ({x} : Set X.obj.left)) :=
    hπ.1.isCompact_preimage isCompact_singleton
  have hFne : (π.hom.left.base ⁻¹' ({x} : Set X.obj.left)).Nonempty := by
    obtain ⟨y,hy⟩ := hπ.surjective x
    exact ⟨y,hy⟩
  refine ⟨hFne,isPreconnected_closed_iff.mpr ?_⟩
  intro K L hK hL hcover hFK hFL
  by_contra hnot
  have hd : Disjoint ((π.hom.left.base ⁻¹' {x}) ∩ K) ((π.hom.left.base ⁻¹' {x}) ∩ L) := by
    rw [disjoint_left]
    intro y hyK hyL
    exact hnot ⟨y,hyK.1,hyK.2,hyL.2⟩
  obtain ⟨O₁,O₂,hO₁,hO₂,hKO₁,hLO₂,hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed (hFc.inter_right hK)
      (hFc.inter_right hL) (hFc.inter_right hL).isClosed hd
  have hFO : π.hom.left.base ⁻¹' {x} ⊆ O₁ ∪ O₂ := by
    intro y hy
    rcases hcover hy with hyK | hyL
    · exact Or.inl (hKO₁ ⟨hy,hyK⟩)
    · exact Or.inr (hLO₂ ⟨hy,hyL⟩)
  have hNo : IsOpen (π.hom.left.base '' (O₁ ∪ O₂)ᶜ)ᶜ :=
    (hπ.1.isClosedMap _ (hO₁.union hO₂).isClosed_compl).isOpen_compl
  have hxN : x ∈ (π.hom.left.base '' (O₁ ∪ O₂)ᶜ)ᶜ := by
    rintro ⟨y,hyO,hyx⟩
    exact hyO (hFO hyx)
  have hpreN : π.hom.left.base ⁻¹' (π.hom.left.base '' (O₁ ∪ O₂)ᶜ)ᶜ ⊆ O₁ ∪ O₂ := by
    intro y hy
    by_contra hyO
    exact hy ⟨y,hyO,rfl⟩
  obtain ⟨U,_hU,hxU,hUN,hpreU⟩ := hπ.exists_connected_preimage_neighborhood hX x hNo hxN
  have hsub : π.hom.left.base ⁻¹' U ⊆ O₁ ∪ O₂ := fun y hy => hpreN (hUN hy)
  have hmeet₁ : (π.hom.left.base ⁻¹' U ∩ O₁).Nonempty := by
    obtain ⟨y,hyF,hyK⟩ := hFK
    refine ⟨y,?_,hKO₁ ⟨hyF,hyK⟩⟩
    change π.hom.left.base y ∈ U
    change π.hom.left.base y = x at hyF
    rwa [hyF]
  have hmeet₂ : (π.hom.left.base ⁻¹' U ∩ O₂).Nonempty := by
    obtain ⟨y,hyF,hyL⟩ := hFL
    refine ⟨y,?_,hLO₂ ⟨hyF,hyL⟩⟩
    change π.hom.left.base y ∈ U
    change π.hom.left.base y = x at hyF
    rwa [hyF]
  obtain ⟨y,_,hy₁,hy₂⟩ := hpreU.isPreconnected O₁ O₂ hO₁ hO₂ hsub hmeet₁ hmeet₂
  exact disjoint_left.mp hdisj hy₁ hy₂

end SGPT.Unibranch.SourceReducedComplexSpace
