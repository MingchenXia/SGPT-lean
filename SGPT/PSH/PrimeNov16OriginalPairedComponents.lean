import SGPT.PSH.PrimeNov16OriginalComponentGoodRestriction
import SGPT.PSH.PrimeNov16OriginalGoodTransition
import SGPT.PSH.PrimeNov16OriginalPairedCommon

/-! Actual original paired-component common maps; full BP first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalPairedComponents
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

private theorem native_bad_thin {X Y : SourceReducedComplexSpace}
    (hY : Y.IsSmooth) (F : Y ⟶ X) (B : Set X.obj.left)
    (ht : interior (F.hom.left.base ⁻¹' B) = ∅)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (E : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    interior (pointMap (E.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c ≫ F) ⁻¹' B) = ∅ := by
  let C := HironakaG1NoncompactSmoothComponentModel.componentObject hY c
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let H : M ≃ₜ C.obj.left := (Homeomorph.Set.univ M).symm.trans (isoHomeomorph E)
  have hjo : IsOpenMap (j.hom.left.base ∘ H) :=
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY c).base_open.isOpenMap.comp H.isOpenMap
  have hjc : Continuous (j.hom.left.base ∘ H) := j.hom.left.base.hom.continuous.comp H.continuous
  have hi := hjo.preimage_interior_eq_interior_preimage hjc (F.hom.left.base ⁻¹' B)
  exact hi.symm.trans (congrArg (fun A : Set Y.obj.left => (j.hom.left.base ∘ H) ⁻¹' A) ht)

private theorem component_proper {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) :
    IsProperMap (HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left.base :=
  (OriginalSmoothComponents.component_isClopen hY c).1.isClosedEmbedding_subtypeVal.isProperMap

theorem exists_actual_paired_component_common_maps
    {X Y₀ Y₁ : SourceReducedComplexSpace} (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth)
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hp₀ : IsProperMap F₀.hom.left.base) (hp₁ : IsProperMap F₁.hom.left.base)
    (E₀ E₁ : Set X.obj.left) (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hi₀ : IsIsoOver F₀ (E₀ ∪ E₁)ᶜ) (hi₁ : IsIsoOver F₁ (E₀ ∪ E₁)ᶜ)
    (ht₀ : interior (F₀.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (ht₁ : interior (F₁.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (c₀ : ConnectedComponents Y₀.obj.left) (c₁ : ConnectedComponents Y₁.obj.left)
    (hpair : PrimeNov16OriginalComponentPairing.componentGoodImage F₀ (E₀ ∪ E₁) c₀ =
      PrimeNov16OriginalComponentPairing.componentGoodImage F₁ (E₀ ∪ E₁) c₁)
    {n₀ n₁ : ℕ} (M₀ : CMfd n₀) (M₁ : CMfd n₁)
    (I₀ : wholeModel (n := n₀) M₀ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY₀ c₀)
    (I₁ : wholeModel (n := n₁) M₁ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ c₁) :
    let P₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₀ c₀ ≫ F₀
    let P₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ c₁ ≫ F₁
    ∃ S : SourceReducedComplexSpace, S.IsSmooth ∧
      ∃ (G₀ : S ⟶ wholeModel (n := n₀) M₀) (G₁ : S ⟶ wholeModel (n := n₁) M₁),
        IsProperBimeromorphic G₀ ∧ IsProperBimeromorphic G₁ ∧
        G₀ ≫ P₀ = G₁ ≫ P₁ ∧
        IsIsoOver G₀ (P₀.hom.left.base ⁻¹' (E₀ ∪ E₁)ᶜ) ∧
        IsIsoOver G₁ (P₁.hom.left.base ⁻¹' (E₀ ∪ E₁)ᶜ) ∧
        interior ((G₁ ≫ P₁).hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ := by
  let B := E₀ ∪ E₁
  have hBc : IsClosed B := hE₀.isClosed.union hE₁.isClosed
  let P₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₀ c₀ ≫ F₀
  let P₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ c₁ ≫ F₁
  have hn₀ := native_bad_thin hY₀ F₀ B ht₀ c₀ M₀ I₀
  have hn₁ := native_bad_thin hY₁ F₁ B ht₁ c₁ M₁ I₁
  let H₁ : M₁ ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ c₁).obj.left :=
    (Homeomorph.Set.univ M₁).symm.trans (isoHomeomorph I₁)
  let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ c₁).obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected c₁)
  let : ConnectedSpace M₁ := H₁.connectedSpace_iff.mpr inferInstance
  obtain ⟨r₀, hr₀⟩ := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction hY₀ F₀ B hBc hi₀ c₀ M₀ I₀
  obtain ⟨r₁, hr₁⟩ := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction hY₁ F₁ B hBc hi₁ c₁ M₁ I₁
  have hrange := hr₁.trans (hpair.symm.trans hr₀.symm)
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
  have hdim := PrimeNov16OriginalGoodDimension.native_dimensions_eq_of_actual_good_restrictions
    P₀ P₁ B hBc r₀ r₁ hrange ⟨x, hx⟩
  subst n₀
  obtain ⟨e, he, hinj⟩ := PrimeNov16OriginalGoodTransition.exists_actual_good_transition P₀ P₁ B hBc r₀ r₁ hrange
  have hA₀ : IsComplexAnalyticSubset (n := n₁) (pointMap P₀ ⁻¹' B) := by
    rw [show B = E₀ ∪ E₁ from rfl, preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage P₀ hE₀) (isComplexAnalyticSubset_preimage P₀ hE₁)
  have hA₁ : IsComplexAnalyticSubset (n := n₁) (pointMap P₁ ⁻¹' B) := by
    rw [show B = E₀ ∪ E₁ from rfl, preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage P₁ hE₀) (isComplexAnalyticSubset_preimage P₁ hE₁)
  have hpP₀ : IsProperMap P₀.hom.left.base := hp₀.comp ((component_proper hY₀ c₀).comp (isoHomeomorph I₀).isProperMap)
  have hpP₁ : IsProperMap P₁.hom.left.base := hp₁.comp ((component_proper hY₁ c₁).comp (isoHomeomorph I₁).isProperMap)
  obtain ⟨M, _hM, g₀, g₁, hg₀, hg₁, hsquare, hiso₀, hiso₁, hthin⟩ :=
    PrimeNov16OriginalPairedCommon.exists_actual_paired_common_maps P₀ P₁ hpP₀ hpP₁ B hBc hA₀ hA₁ hn₀ hn₁ e he hinj
  exact ⟨wholeModel (n := n₁) M, isSmooth_wholeModel, nativeMorphism hg₀.1, nativeMorphism hg₁.1,
    nativeMorphism_isProperBimeromorphic hg₀, nativeMorphism_isProperBimeromorphic hg₁, hsquare, hiso₀, hiso₁, hthin⟩

end SGPT.PSH.PrimeNov16OriginalPairedComponents
