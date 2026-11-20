import SGPT.Unibranch.ComplexSpaceUnibranchGlobalComplement
import SGPT.Unibranch.ComplexSpaceUnibranchOnOpen
import SGPT.Unibranch.ComplexSpacePSH

/-! Actual ORIGINAL component dictionary and genuine target nondegeneracy.
Blueprint: complex-space-bimeromorphic-components.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Actual clopen irreducibility internally gives ORIGINAL component maximality. -/
theorem isIrreducibleComponent_of_clopen_irreducible {X : SourceReducedComplexSpace}
    {A : Set X.obj.left} (hAc : IsClopen A) (hA : X.IsIrreducibleAnalyticSubset A) :
    X.IsIrreducibleComponent A := by
  refine ⟨hA,fun D hD hAD => ?_⟩
  have hD1 := OriginalAnalyticClopen.isAnalyticSubset_inter hD.1 hAc
  have hD2 := OriginalAnalyticClopen.isAnalyticSubset_inter hD.1 hAc.compl
  have hUnion : D = D ∩ A ∪ D ∩ Aᶜ := by
    rw [← inter_union_distrib_left,union_compl_self,inter_univ]
  rcases hD.2.2 _ _ hD1 hD2 inter_subset_left inter_subset_left hUnion with h | h
  · apply Subset.antisymm _ hAD
    rw [h]
    exact inter_subset_right
  · exfalso
    obtain ⟨x,hxA⟩ := hA.2.1
    have hxD := hAD hxA
    rw [h] at hxD
    exact hxD.2 hxA

/-- ORIGINAL components equal the literal connected components on the SAME
intrinsically unibranch topology, not a component-certificate proxy. -/
theorem IsUnibranch.eq_connectedComponent_of_isIrreducibleComponent
    {X : SourceReducedComplexSpace} (hX : X.IsUnibranch) {Z : Set X.obj.left}
    (hZ : X.IsIrreducibleComponent Z) (x : X.obj.left) (hxZ : x ∈ Z) :
    Z = connectedComponent x := by
  let singularComponentLocallyConnected := hX.locallyConnectedSpace
  have hK : IsClopen (connectedComponent x) := ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩
  have hB := OriginalAnalyticClopen.isAnalyticSubset_inter hZ.1.1 hK
  have hC := OriginalAnalyticClopen.isAnalyticSubset_inter hZ.1.1 hK.compl
  have hUnion : Z = Z ∩ connectedComponent x ∪ Z ∩ (connectedComponent x)ᶜ := by
    rw [← inter_union_distrib_left,union_compl_self,inter_univ]
  have hZK : Z ⊆ connectedComponent x := by
    rcases hZ.1.2.2 _ _ hB hC inter_subset_left inter_subset_left hUnion with h | h
    · rw [h]
      exact inter_subset_right
    · exfalso
      rw [h] at hxZ
      exact hxZ.2 mem_connectedComponent
  exact (hZ.2 _ (hX.isIrreducibleComponent_connectedComponent x).1 hZK).symm

/-- The ENTIRE actual inverse of the target component is an ORIGINAL source
component, manufactured from actual exceptional/iso/stalk/density geometry. -/
theorem IsProperBimeromorphic.isIrreducibleComponent_preimage_connectedComponent
    {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) (x : X.obj.left) :
    Y.IsIrreducibleComponent (π.hom.left.base ⁻¹' connectedComponent x) := by
  let singularBirationalComponentLocallyConnected := hX.locallyConnectedSpace
  let K : Set X.obj.left := connectedComponent x
  have hK : IsClopen K := ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩
  let A : Set Y.obj.left := π.hom.left.base ⁻¹' K
  have hA : IsClopen A :=
    ⟨hK.isClosed.preimage π.hom.left.base.hom.continuous,hK.isOpen.preimage π.hom.left.base.hom.continuous⟩
  obtain ⟨Z,hZa,hZ,hpre,hiso⟩ := hπ.2
  let G : Set Y.obj.left := π.hom.left.base ⁻¹' (K \ Z)
  have hKG : IsConnected (K \ Z) := hX.isConnected_diff_of_isConnected_open hZa hZ hK.isOpen
    isConnected_connectedComponent
  have hGc : IsConnected G := hiso.isConnected_preimage_of_subset hKG (fun _ hz => hz.2)
  have hGo : IsOpen G := (hK.isOpen.sdiff hZa.isClosed).preimage π.hom.left.base.hom.continuous
  have hAt : ∀ y ∈ G,SourceUnibranchReducedRing (Y.obj.left.presheaf.stalk y).carrier :=
    fun y hy => hiso.isUnibranch_stalk_of_isUnibranch hX y hy.2
  have hd : Dense ((π.hom.left.base ⁻¹' Z)ᶜ) := interior_eq_empty_iff_dense_compl.mp hpre
  have hdA : Dense ((Subtype.val : A → Y.obj.left) ⁻¹' (π.hom.left.base ⁻¹' Z)ᶜ) :=
    hd.preimage hA.isOpen.isOpenMap_subtype_val
  have hMaps : MapsTo (Subtype.val : A → Y.obj.left)
      ((Subtype.val : A → Y.obj.left) ⁻¹' (π.hom.left.base ⁻¹' Z)ᶜ) G := by
    intro y hy
    exact ⟨y.property,hy⟩
  have hDense : A ⊆ closure G := fun y hy => (hMaps.closure continuous_subtype_val) (hdA ⟨y,hy⟩)
  have hGA : G ⊆ A := fun _ hy => hy.1
  have hAirr : Y.IsIrreducibleAnalyticSubset A := by
    refine ⟨OriginalAnalyticClopen.isAnalyticSubset hA,?_,?_⟩
    · obtain ⟨y,hy⟩ := hπ.surjective x
      exact ⟨y,by change π.hom.left.base y ∈ K;rw [hy];exact mem_connectedComponent⟩
    · intro B C hB hC hBA hCA hUnion
      have hcover : G ⊆ B ∪ C := fun y hy => hUnion ▸ hGA hy
      rcases subset_left_or_right_of_connected_unibranch_open hGo hGc hAt hB hC hcover with h | h
      · exact Or.inl (Subset.antisymm (fun y hy => closure_minimal h hB.isClosed (hDense hy)) hBA)
      · exact Or.inr (Subset.antisymm (fun y hy => closure_minimal h hC.isClosed (hDense hy)) hCA)
  exact isIrreducibleComponent_of_clopen_irreducible hA hAirr

/-- The ORIGINAL upstairs PSH component clause internally yields target
component nondegeneracy for the SAME actual pointwise descended function. -/
theorem IsPSH.componentNondegenerate_descent_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} {ψ : Y.obj.left → EReal} (hψ : Y.IsPSH ψ)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {φ : X.obj.left → EReal} (hcoh : ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) :
    ∀ Z : Set X.obj.left,X.IsIrreducibleComponent Z → ∃ z ∈ Z,φ z ≠ ⊥ := by
  intro Z hZ
  obtain ⟨x,hxZ⟩ := hZ.1.2.1
  have hZK := hX.eq_connectedComponent_of_isIrreducibleComponent hZ x hxZ
  have hSource := hπ.isIrreducibleComponent_preimage_connectedComponent hX x
  obtain ⟨y,hyK,hyFin⟩ := hψ.1 _ hSource
  refine ⟨π.hom.left.base y,?_,?_⟩
  · rw [hZK]
    exact hyK
  · rw [hcoh]
    exact hyFin

end SGPT.Unibranch.SourceReducedComplexSpace
