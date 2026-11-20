import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-! Actual uniqueness of the lifted marked component. Full BP first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalMarkedComponentUnique
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

theorem eq_component_of_actual_native_lifts
    {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (G : S ⟶ Y) (hG : IsProperBimeromorphic G)
    (cY : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY cY)
    (c₀ c₁ : ConnectedComponents S.obj.left) {n₀ n₁ : ℕ} (N₀ : CMfd n₀) (N₁ : CMfd n₁)
    (I₀ : wholeModel (n := n₀) N₀ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS c₀)
    (I₁ : wholeModel (n := n₁) N₁ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS c₁)
    (F₀ : wholeModel (n := n₀) N₀ ⟶ wholeModel (n := n) M)
    (F₁ : wholeModel (n := n₁) N₁ ⟶ wholeModel (n := n) M)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁)
    (hsq₀ : F₀ ≫ (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
      I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c₀ ≫ G)
    (hsq₁ : F₁ ≫ (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
      I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c₁ ≫ G) : c₀ = c₁ := by
  obtain ⟨_hp, B, _hBa, hBt, _hpre, hi⟩ := hG
  let H : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY cY).obj.left :=
    (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I)
  let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hY cY).obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected cY)
  let : ConnectedSpace M := H.connectedSpace_iff.mpr inferInstance
  let J := I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let J₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c₀
  let J₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c₁
  have hn : interior (pointMap J ⁻¹' B) = ∅ := native_bad_thin hY (𝟙 Y) B hBt cY M I
  obtain ⟨y, hy⟩ := (interior_eq_empty_iff_dense_compl.mp hn).nonempty
  obtain ⟨x₀, hx₀⟩ := hF₀.surjective ⟨y, mem_univ y⟩
  obtain ⟨x₁, hx₁⟩ := hF₁.surjective ⟨y, mem_univ y⟩
  have he₀ : G.hom.left.base (J₀.hom.left.base x₀) = J.hom.left.base ⟨y, mem_univ y⟩ := by
    have h := congrArg (fun F : wholeModel (n := n₀) N₀ ⟶ Y => F.hom.left.base x₀) hsq₀
    exact h.symm.trans (congrArg J.hom.left.base hx₀)
  have he₁ : G.hom.left.base (J₁.hom.left.base x₁) = J.hom.left.base ⟨y, mem_univ y⟩ := by
    have h := congrArg (fun F : wholeModel (n := n₁) N₁ ⟶ Y => F.hom.left.base x₁) hsq₁
    exact h.symm.trans (congrArg J.hom.left.base hx₁)
  have hg₀ : G.hom.left.base (J₀.hom.left.base x₀) ∈ Bᶜ := he₀.symm ▸ hy
  have hg₁ : G.hom.left.base (J₁.hom.left.base x₁) ∈ Bᶜ := he₁.symm ▸ hy
  have heq := PrimeNov16IsoOverLift.injOn_preimage hi hg₀ hg₁ (he₀.trans he₁.symm)
  have hc₀ : ConnectedComponents.mk (J₀.hom.left.base x₀) = c₀ := (I₀.hom.hom.left.base x₀).property
  have hc₁ : ConnectedComponents.mk (J₁.hom.left.base x₁) = c₁ := (I₁.hom.hom.left.base x₁).property
  exact hc₀.symm.trans ((congrArg ConnectedComponents.mk heq).trans hc₁)

end SGPT.PSH.PrimeNov16OriginalMarkedComponentUnique
