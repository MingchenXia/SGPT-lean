import SGPT.Unibranch.ComplexSpaceUnibranchComponents
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.ComplexSpaceUnibranchFibers

/-! Actual ORIGINAL local unibranch stalks give relative analytic continuation.
Blueprint: complex-space-unibranch-on-open.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch
namespace LocalEmbedding

/-- The SAME actual chart model inherits intrinsic unibranchness from
original stalks on its actual range, with no analytic-germ certificate. -/
theorem model_isUnibranch_of_range {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    {U : Set X.obj.left}
    (hAt : ∀ x ∈ U,SourceUnibranchReducedRing (X.obj.left.presheaf.stalk x).carrier)
    (hRange : range e.toPoint ⊆ U) :
    (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsUnibranch := by
  let singularRangeOpenImmersion : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  intro c
  let E := (asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv
  exact (sourceUnibranchReducedRing_iff_of_ringEquiv E).mp (hAt (e.toPoint c) (hRange ⟨c,rfl⟩))

end LocalEmbedding
namespace SourceReducedComplexSpace

/-- Genuine original identity theorem RELATIVE to the actual unibranch open locus. -/
theorem isClosed_preimage_interior_of_unibranch_on_open {X : SourceReducedComplexSpace}
    {U B : Set X.obj.left} (hU : IsOpen U)
    (hAt : ∀ x ∈ U,SourceUnibranchReducedRing (X.obj.left.presheaf.stalk x).carrier)
    (hB : X.IsAnalyticSubset B) :
    IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' interior B) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxX : x.val ∈ closure (interior B) :=
    continuous_subtype_val.closure_preimage_subset (interior B) hx
  obtain ⟨e,⟨c,hc⟩,hRange,_hconn⟩ := LocalEmbedding.exists_domain (X := X) x.val hU x.property
  have hM := e.model_isUnibranch_of_range hAt hRange
  let j : sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic ⟶ X :=
    ObjectProperty.homMk (Over.homMk e.map e.overPoint)
  have hBpre := hB.preimage j
  have hClose : IsClosed (interior (e.toPoint ⁻¹' B)) :=
    hM.isClosed_interior_of_isAnalyticSubset hBpre
  have hccl : c ∈ closure (e.toPoint ⁻¹' interior B) := by
    apply e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_subset_closure_preimage
    change e.toPoint c ∈ closure (interior B)
    rw [hc]
    exact hxX
  rw [e.isOpenEmbedding_toPoint.isOpenMap.preimage_interior_eq_interior_preimage
    e.isOpenEmbedding_toPoint.continuous B,hClose.closure_eq] at hccl
  have hci : e.toPoint c ∈ interior B :=
    e.isOpenEmbedding_toPoint.isOpenMap.interior_preimage_subset_preimage_interior hccl
  change x.val ∈ interior B
  rw [← hc]
  exact hci

/-- A connected ORIGINAL open unibranch locus cannot be split by two
ORIGINAL analytic traces; continuation is internally manufactured. -/
theorem subset_left_or_right_of_connected_unibranch_open {X : SourceReducedComplexSpace}
    {U B C : Set X.obj.left} (hU : IsOpen U) (hUc : IsConnected U)
    (hAt : ∀ x ∈ U,SourceUnibranchReducedRing (X.obj.left.presheaf.stalk x).carrier)
    (hB : X.IsAnalyticSubset B) (hC : X.IsAnalyticSubset C) (hcover : U ⊆ B ∪ C) :
    U ⊆ B ∨ U ⊆ C := by
  by_cases hUB : U ⊆ B
  · exact Or.inl hUB
  right
  obtain ⟨p,hpU,hpB⟩ := not_subset.mp hUB
  have hpint : p ∈ interior C := by
    refine mem_interior.mpr ⟨U ∩ Bᶜ,?_,hU.inter hB.isClosed.isOpen_compl,hpU,hpB⟩
    intro z hz
    exact (hcover hz.1).resolve_left hz.2
  let singularUnibranchOpenTraceConnected : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUc
  let V : Set U := (Subtype.val : U → X.obj.left) ⁻¹' interior C
  have hV : IsClopen V :=
    ⟨isClosed_preimage_interior_of_unibranch_on_open hU hAt hC,
      isOpen_interior.preimage continuous_subtype_val⟩
  have hVall : V = univ := hV.eq_univ ⟨⟨p,hpU⟩,hpint⟩
  intro z hz
  have hzV : (⟨z,hz⟩ : U) ∈ V := by rw [hVall];trivial
  exact interior_subset hzV

/-- The actual ORIGINAL two-open-immersion stalk square gives unibranchness
at every SAME source point over the genuine isomorphism locus. -/
theorem IsIsoOver.isUnibranch_stalk_of_isUnibranch {X Y : SourceReducedComplexSpace}
    {π : Y ⟶ X} {U : Set X.obj.left} (hiso : IsIsoOver π U) (hX : X.IsUnibranch)
    (y : Y.obj.left) (hy : π.hom.left.base y ∈ U) :
    SourceUnibranchReducedRing (Y.obj.left.presheaf.stalk y).carrier := by
  obtain ⟨V,j,hj,hjr,hk,_hkr⟩ := hiso
  have hyj : y ∈ range j.base := by rw [hjr];exact hy
  obtain ⟨v,hv⟩ := hyj
  let singularIsoSourceOpenImmersion : LocallyRingedSpace.IsOpenImmersion j := hj
  let singularIsoTargetOpenImmersion : LocallyRingedSpace.IsOpenImmersion (j ≫ π.hom.left) := hk
  let EJ := (asIso (j.stalkMap v)).commRingCatIsoToRingEquiv
  let EK := (asIso ((j ≫ π.hom.left).stalkMap v)).commRingCatIsoToRingEquiv
  have hV := (sourceUnibranchReducedRing_iff_of_ringEquiv EK).mp (hX ((j ≫ π.hom.left).base v))
  have hY := (sourceUnibranchReducedRing_iff_of_ringEquiv EJ).mpr hV
  exact hv ▸ hY

end SourceReducedComplexSpace
end SGPT.Unibranch
