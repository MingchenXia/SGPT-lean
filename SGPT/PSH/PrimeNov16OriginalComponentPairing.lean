import SGPT.Unibranch.HironakaG1NoncompactSmoothComponentModel
import SGPT.Unibranch.OriginalCommonResolution
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected

/-! Actual noncompact original component pairing. Blueprint first:
`prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalComponentPairing
open SGPT.Unibranch SourceReducedComplexSpace OriginalSmoothSourceAnalytic
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaEmbeddedNativeMorphism
open OriginalNativeModification
private theorem component_good_connected {X Y : SourceReducedComplexSpace}
    (hY : Y.IsSmooth) (F : Y ⟶ X)
    (E₀ E₁ : Set X.obj.left) (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hthin : interior (F.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (c : ConnectedComponents Y.obj.left) :
    IsConnected ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left.base ⁻¹'
      (F.hom.left.base ⁻¹' (E₀ ∪ E₁)ᶜ)) := by
  let C := HironakaG1NoncompactSmoothComponentModel.componentObject hY c
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  obtain ⟨n, M, ⟨E⟩⟩ := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hY c
  let H : M ≃ₜ C.obj.left := (Homeomorph.Set.univ M).symm.trans (isoHomeomorph E)
  let : ConnectedSpace C.obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected c)
  let : ConnectedSpace M := H.connectedSpace_iff.mpr inferInstance
  let F' : wholeModel (n := n) M ⟶ X := E.hom ≫ j ≫ F
  let D := pointMap F' ⁻¹' (E₀ ∪ E₁)
  have hDa : IsComplexAnalyticSubset (n := n) D := by
    change IsComplexAnalyticSubset (n := n) (pointMap F' ⁻¹' (E₀ ∪ E₁))
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F' hE₀) (isComplexAnalyticSubset_preimage F' hE₁)
  have hjo : IsOpenMap (j.hom.left.base ∘ H) :=
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY c).base_open.isOpenMap.comp H.isOpenMap
  have hjc : Continuous (j.hom.left.base ∘ H) := j.hom.left.base.hom.continuous.comp H.continuous
  have hDi : interior D = ∅ := by
    have hi := hjo.preimage_interior_eq_interior_preimage hjc (F.hom.left.base ⁻¹' (E₀ ∪ E₁))
    exact hi.symm.trans (congrArg (fun A : Set Y.obj.left => (j.hom.left.base ∘ H) ⁻¹' A) hthin)
  have hDne : D ≠ univ := by
    intro heq
    have : interior D = univ := by rw [heq, interior_univ]
    exact Set.univ_nonempty.ne_empty (this.symm.trans hDi)
  have hg : IsConnected Dᶜ :=
    ⟨(interior_eq_empty_iff_dense_compl.mp hDi).nonempty,
      AnalyticComplementConnected.isPreconnected_compl hDa hDne⟩
  exact H.isConnected_preimage.mp hg

private theorem exists_partition_pairing
    {S I J : Type} [TopologicalSpace S] (P : I → Set S) (Q : J → Set S)
    (hPc : ∀ i, IsClopen (P i)) (hQc : ∀ j, IsClopen (Q j))
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hPu : ⋃ i, P i = univ) (hQu : ⋃ j, Q j = univ)
    (hPconn : ∀ i, IsConnected (P i)) (hQconn : ∀ j, IsConnected (Q j)) :
    ∃ e : I ≃ J, ∀ x i, x ∈ P i ↔ x ∈ Q (e i) := by
  let eP := ConnectedComponents.equivOfIsClopenOfIsConnected hPc hPd hPu hPconn
  let eQ := ConnectedComponents.equivOfIsClopenOfIsConnected hQc hQd hQu hQconn
  let e := eP.symm.trans eQ
  have hPoint (x : S) (i : I) (j : J) (hp : x ∈ P i) (hq : x ∈ Q j) : e i = j := by
    have hp' := ConnectedComponents.equivOfIsClopenOfIsConnected_mk hPc hPd hPu hPconn x hp
    have hq' := ConnectedComponents.equivOfIsClopenOfIsConnected_mk hQc hQd hQu hQconn x hq
    change eQ (eP.symm i) = j
    rw [← hp', eP.symm_apply_apply]
    exact hq'
  refine ⟨e, ?_⟩
  intro x i
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hQu ▸ mem_univ x)
    rwa [hPoint x i j hp hj]
  · intro hq
    obtain ⟨i', hi'⟩ := mem_iUnion.mp (hPu ▸ mem_univ x)
    have he : e i' = e i := hPoint x i' (e i) hi' hq
    exact e.injective he ▸ hi'

variable {X Y Y₀ Y₁ : SourceReducedComplexSpace}

private def originalGoodOpen (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    Opens Y.obj.left :=
  ⟨F.hom.left.base ⁻¹' Bᶜ, hBc.isOpen_compl.preimage F.hom.left.base.hom.continuous⟩

private def goodRestriction (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    LocallyRingedSpace := Y.obj.left.restrict (originalGoodOpen F B hBc).isOpenEmbedding

private def goodInclusion (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    goodRestriction F B hBc ⟶ Y.obj.left :=
  Y.obj.left.ofRestrict (originalGoodOpen F B hBc).isOpenEmbedding

private def goodMap (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    goodRestriction F B hBc ⟶ X.obj.left := goodInclusion F B hBc ≫ F.hom.left

-- Same actual OI range comparison as the accepted native-source consumer,
-- now on literal ORIGINAL raw restrictions. No new comparison engine credit.
private theorem goodMap_isOpenImmersion (F : Y ⟶ X) (B : Set X.obj.left)
    (hBc : IsClosed B) (hiso : IsIsoOver F Bᶜ) :
    LocallyRingedSpace.IsOpenImmersion (goodMap F B hBc) ∧
      range (goodMap F B hBc).base = Bᶜ := by
  obtain ⟨V, j, hj, hjrange, hjF, hjFrange⟩ := hiso
  let I := goodInclusion F B hBc
  have hI : LocallyRingedSpace.IsOpenImmersion I := by
    exact LocallyRingedSpace.IsOpenImmersion.ofRestrict Y.obj.left
      (originalGoodOpen F B hBc).isOpenEmbedding
  have hIr : range I.base = F.hom.left.base ⁻¹' Bᶜ := Subtype.range_coe
  let E := @openImmersionIsoOfRangeEq _ _ _ I j hI hj (hIr.trans hjrange.symm)
  have hE : E.hom ≫ j = I :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ I j hI hj (hIr.trans hjrange.symm)
  have hR : goodMap F B hBc = E.hom ≫ (j ≫ F.hom.left) := by
    rw [← Category.assoc, hE]
    rfl
  constructor
  · rw [hR]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance)
      (j ≫ F.hom.left) hjF
  · exact (congrArg (fun K : goodRestriction F B hBc ⟶ X.obj.left => range K.base) hR).trans
      ((range_iso_hom_comp_base E (j ≫ F.hom.left)).trans hjFrange)

private def originalGoodIso
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    goodRestriction F₁ B hBc ≅ goodRestriction F₀ B hBc :=
  @openImmersionIsoOfRangeEq _ _ _ (goodMap F₁ B hBc) (goodMap F₀ B hBc)
    (goodMap_isOpenImmersion F₁ B hBc hiso₁).1 (goodMap_isOpenImmersion F₀ B hBc hiso₀).1
    ((goodMap_isOpenImmersion F₁ B hBc hiso₁).2.trans
      (goodMap_isOpenImmersion F₀ B hBc hiso₀).2.symm)

private theorem originalGoodIso_fac
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom ≫ goodMap F₀ B hBc = goodMap F₁ B hBc :=
  @openImmersionIsoOfRangeEq_hom_fac _ _ _ (goodMap F₁ B hBc) (goodMap F₀ B hBc)
    (goodMap_isOpenImmersion F₁ B hBc hiso₁).1 (goodMap_isOpenImmersion F₀ B hBc hiso₀).1
    ((goodMap_isOpenImmersion F₁ B hBc hiso₁).2.trans
      (goodMap_isOpenImmersion F₀ B hBc hiso₀).2.symm)

private def originalGoodHomeomorph
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    originalGoodOpen F₁ B hBc ≃ₜ originalGoodOpen F₀ B hBc where
  toFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom.base
  invFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv.base
  left_inv x := congrArg (fun f => f.base x) (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom_inv_id
  right_inv x := congrArg (fun f => f.base x) (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv_hom_id
  continuous_toFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom.base.hom.continuous
  continuous_invFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv.base.hom.continuous

private theorem originalGoodHomeomorph_square
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ)
    (y : originalGoodOpen F₁ B hBc) :
    F₀.hom.left.base (originalGoodHomeomorph F₀ F₁ B hBc hiso₀ hiso₁ y).val =
      F₁.hom.left.base y.val :=
  congrArg (fun f => f.base y) (originalGoodIso_fac F₀ F₁ B hBc hiso₀ hiso₁)

private def componentGoodPiece (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (c : ConnectedComponents Y.obj.left) : Set (originalGoodOpen F B hBc) :=
  {y | ConnectedComponents.mk y.val = c}

private theorem componentGoodPiece_isClopen (hY : Y.IsSmooth) (F : Y ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) (c : ConnectedComponents Y.obj.left) :
    IsClopen (componentGoodPiece F B hBc c) :=
  (OriginalSmoothComponents.component_isClopen hY c).preimage continuous_subtype_val

private theorem componentGoodPiece_pairwise (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    Pairwise (fun c d => Disjoint (componentGoodPiece F B hBc c) (componentGoodPiece F B hBc d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro y hc hd
  exact hcd (hc.symm.trans hd)

private theorem componentGoodPiece_union (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    ⋃ c, componentGoodPiece F B hBc c = univ := by
  apply eq_univ_of_forall
  intro y
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk y.val, rfl⟩

private theorem componentGoodPiece_connected
    (hY : Y.IsSmooth) (F : Y ⟶ X) (E₀ E₁ : Set X.obj.left)
    (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hthin : interior (F.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (c : ConnectedComponents Y.obj.left) :
    IsConnected (componentGoodPiece F (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed) c) := by
  let B := E₀ ∪ E₁
  let hBc := hE₀.isClosed.union hE₁.isClosed
  let j := (HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left
  let A := j.base ⁻¹' (F.hom.left.base ⁻¹' Bᶜ)
  have hA : IsConnected A := component_good_connected hY F E₀ E₁ hE₀ hE₁ hthin c
  have : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
  let f : A → originalGoodOpen F B hBc := fun y => ⟨j.base y.val, y.property⟩
  have hf : Continuous f := (j.base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hr : range f = componentGoodPiece F B hBc c := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change ConnectedComponents.mk z.val.val = c
      exact z.val.property
    · intro hy
      let p : (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left := ⟨y.val, hy⟩
      exact ⟨⟨p, y.property⟩, rfl⟩
  rw [← hr]
  exact isConnected_range hf

/-- The literal target image of an actual original component's entire good set. -/
def componentGoodImage (F : Y ⟶ X) (B : Set X.obj.left)
    (c : ConnectedComponents Y.obj.left) : Set X.obj.left :=
  F.hom.left.base '' (OriginalSmoothComponents.componentSet c ∩ (F.hom.left.base ⁻¹' Bᶜ))

/-- ONLY actual original smooth sources and their ORIGINAL PB maps derive
the common actual exceptional union, its thin pullbacks, and a BIJECTIVE
pairing with equality of the ENTIRE actual matched good images. -/
theorem exists_original_good_component_pairing

    (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth) (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (E₀ E₁ : Set X.obj.left) (_hE₀ : X.IsAnalyticSubset E₀) (_hE₁ : X.IsAnalyticSubset E₁),
      IsIsoOver F₀ (E₀ ∪ E₁)ᶜ ∧ IsIsoOver F₁ (E₀ ∪ E₁)ᶜ ∧
      interior (F₀.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ ∧
      interior (F₁.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ ∧
      ∃ pair : ConnectedComponents Y₁.obj.left ≃ ConnectedComponents Y₀.obj.left,
        ∀ c, componentGoodImage F₀ (E₀ ∪ E₁) (pair c) = componentGoodImage F₁ (E₀ ∪ E₁) c := by
  obtain ⟨_hp₀, E₀, hE₀, htE₀, hown₀, hiso₀⟩ := hF₀
  obtain ⟨_hp₁, E₁, hE₁, htE₁, hown₁, hiso₁⟩ := hF₁
  let B := E₀ ∪ E₁
  have hBc : IsClosed B := hE₀.isClosed.union hE₁.isClosed
  have hi₀ : IsIsoOver F₀ Bᶜ :=
    hiso₀.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inl h))
  have hi₁ : IsIsoOver F₁ Bᶜ :=
    hiso₁.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inr h))
  have hc₀ : interior (F₀.hom.left.base ⁻¹' E₁) = ∅ :=
    hiso₀.interior_preimage_eq_empty hown₀ htE₁
  have hc₁ : interior (F₁.hom.left.base ⁻¹' E₀) = ∅ :=
    hiso₁.interior_preimage_eq_empty hown₁ htE₀
  have ht₀ : interior (F₀.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀.isClosed.preimage F₀.hom.left.base.hom.continuous) hc₀]
    exact hown₀
  have ht₁ : interior (F₁.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀.isClosed.preimage F₁.hom.left.base.hom.continuous) hown₁]
    exact hc₁
  let e := originalGoodHomeomorph F₀ F₁ B hBc hi₀ hi₁
  let P := componentGoodPiece F₁ B hBc
  let Q := fun c => e ⁻¹' componentGoodPiece F₀ B hBc c
  have hPc : ∀ c, IsClopen (P c) := componentGoodPiece_isClopen hY₁ F₁ B hBc
  have hQc : ∀ c, IsClopen (Q c) :=
    fun c => (componentGoodPiece_isClopen hY₀ F₀ B hBc c).preimage e.continuous
  have hPd := componentGoodPiece_pairwise F₁ B hBc
  have hQd : Pairwise (fun c d => Disjoint (Q c) (Q d)) := by
    intro c d hcd
    exact (componentGoodPiece_pairwise F₀ B hBc hcd).preimage e
  have hPu : ⋃ c, P c = univ := componentGoodPiece_union F₁ B hBc
  have hQu : ⋃ c, Q c = univ := by
    apply eq_univ_of_forall
    intro y
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk (e y).val, rfl⟩
  have hPconn : ∀ c, IsConnected (P c) :=
    componentGoodPiece_connected hY₁ F₁ E₀ E₁ hE₀ hE₁ ht₁
  have hQconn : ∀ c, IsConnected (Q c) := fun c => e.isConnected_preimage.mpr
    (componentGoodPiece_connected hY₀ F₀ E₀ E₁ hE₀ hE₁ ht₀ c)
  obtain ⟨pair, hPair⟩ := exists_partition_pairing P Q hPc hQc hPd hQd hPu hQu hPconn hQconn
  refine ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, ?_⟩
  intro c
  ext z
  constructor
  · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
    let y₀ : originalGoodOpen F₀ B hBc := ⟨y, hyg⟩
    let y₁ := e.symm y₀
    have hq : y₁ ∈ Q (pair c) := by
      change ConnectedComponents.mk (e y₁).val = pair c
      rw [e.apply_symm_apply]
      exact hyc
    have hp : y₁ ∈ P c := (hPair y₁ c).mpr hq
    refine ⟨y₁.val, ⟨hp, y₁.property⟩, ?_⟩
    have hs := originalGoodHomeomorph_square F₀ F₁ B hBc hi₀ hi₁ y₁
    change F₀.hom.left.base (e y₁).val = F₁.hom.left.base y₁.val at hs
    have heq : e y₁ = y₀ := e.apply_symm_apply y₀
    simpa only [heq] using hs.symm
  · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
    let y₁ : originalGoodOpen F₁ B hBc := ⟨y, hyg⟩
    have hq : y₁ ∈ Q (pair c) := (hPair y₁ c).mp hyc
    refine ⟨(e y₁).val, ⟨hq, (e y₁).property⟩, ?_⟩
    exact originalGoodHomeomorph_square F₀ F₁ B hBc hi₀ hi₁ y₁


end SGPT.PSH.PrimeNov16OriginalComponentPairing
