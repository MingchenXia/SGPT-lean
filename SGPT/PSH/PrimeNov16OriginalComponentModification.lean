import SGPT.PSH.PrimeNov16OriginalPairedComponents

/-! Actual native modification on the marked components of original PB maps.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalComponentModification
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaEmbeddedNativeMorphism AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic
open OriginalProperBimeromorphicNative

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

theorem exists_actual_native_component_modification
    {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (G : S ⟶ Y) (hG : IsProperBimeromorphic G)
    (B : Set Y.obj.left) (hBa : Y.IsAnalyticSubset B) (hBt : interior B = ∅)
    (hiG : IsIsoOver G Bᶜ) (hpre : interior (G.hom.left.base ⁻¹' B) = ∅)
    (cS : ConnectedComponents S.obj.left) (cY : ConnectedComponents Y.obj.left)
    (hpair : PrimeNov16OriginalComponentPairing.componentGoodImage G B cS =
      PrimeNov16OriginalComponentPairing.componentGoodImage (𝟙 Y) B cY)
    {n₀ n₁ : ℕ} (M₀ : CMfd n₀) (M₁ : CMfd n₁)
    (I₀ : wholeModel (n := n₀) M₀ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS cS)
    (I₁ : wholeModel (n := n₁) M₁ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY cY) :
    n₀ = n₁ ∧ ∃ F : wholeModel (n := n₀) M₀ ⟶ wholeModel (n := n₁) M₁,
      IsProperBimeromorphic F ∧
      F ≫ (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
        I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G := by
  let j₀ := HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let j₁ := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let P₀ := I₀.hom ≫ j₀ ≫ G
  let P₁ := I₁.hom ≫ j₁
  let H₀ : M₀ ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    (Homeomorph.Set.univ M₀).symm.trans (isoHomeomorph I₀)
  let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected cS)
  let : ConnectedSpace M₀ := H₀.connectedSpace_iff.mpr inferInstance
  let H₁ : M₁ ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY cY).obj.left :=
    (Homeomorph.Set.univ M₁).symm.trans (isoHomeomorph I₁)
  let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hY cY).obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected cY)
  let : ConnectedSpace M₁ := H₁.connectedSpace_iff.mpr inferInstance
  have hn₀ := native_bad_thin hS G B hpre cS M₀ I₀
  have hn₁ : interior (pointMap P₁ ⁻¹' B) = ∅ := by
    exact native_bad_thin hY (𝟙 Y) B hBt cY M₁ I₁
  have hiid : IsIsoOver (𝟙 Y) Bᶜ := IsIsoOver.id_of_isOpen Y hBa.isClosed.isOpen_compl
  obtain ⟨r₀, hr₀⟩ := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction hS G B hBa.isClosed hiG cS M₀ I₀
  have r₁data := PrimeNov16OriginalComponentGoodRestriction.native_component_good_restriction hY (𝟙 Y) B hBa.isClosed hiid cY M₁ I₁
  obtain ⟨r₁, hr₁⟩ := r₁data
  have hrange := hr₁.trans (hpair.symm.trans hr₀.symm)
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hn₁).nonempty
  have hdim := PrimeNov16OriginalGoodDimension.native_dimensions_eq_of_actual_good_restrictions P₀ P₁ B hBa.isClosed r₀ r₁ hrange ⟨x, hx⟩
  refine ⟨hdim, ?_⟩
  subst n₀
  obtain ⟨e, he, hinj⟩ := PrimeNov16OriginalGoodTransition.exists_actual_good_transition P₀ P₁ B hBa.isClosed r₀ r₁ hrange
  have hP₁oi : LocallyRingedSpace.IsOpenImmersion P₁.hom.left := by
    have hI : LocallyRingedSpace.IsOpenImmersion I₁.hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (SourceReducedComplexSpace.isoLeft I₁).hom
      infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ I₁.hom.hom.left hI j₁.hom.left
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY cY)
  have hP₁range : range P₁.hom.left.base = OriginalSmoothComponents.componentSet cY :=
    (range_iso_hom_comp_base (SourceReducedComplexSpace.isoLeft I₁) j₁.hom.left).trans
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hY cY)
  let a : OriginalCommonResolution.goodOpen P₁ B hBa.isClosed := ⟨x, hx⟩
  have hct : ConnectedComponents.mk (pointMap P₁ x) = cY := (H₁ x).property
  have hcc : connectedComponent (pointMap P₁ x) = OriginalSmoothComponents.componentSet cY := by
    rw [← hct]
    exact (OriginalSmoothComponents.componentSet_eq_connectedComponent _).symm
  have hconnrange : range (pointMap P₀) ⊆ OriginalSmoothComponents.componentSet cY := by
    rw [← hcc]
    exact (isConnected_range (continuous_pointMap P₀)).subset_connectedComponent ⟨(e a).val, he a⟩
  have hr : range P₀.hom.left.base ⊆ range P₁.hom.left.base := by
    rw [hP₁range]
    rintro _ ⟨z, rfl⟩
    exact hconnrange ⟨z.val, rfl⟩
  let := hP₁oi
  let L := LocallyRingedSpace.IsOpenImmersion.lift P₁.hom.left P₀.hom.left hr
  have hL : L ≫ P₁.hom.left = P₀.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hLp : L ≫ (wholeModel (n := n₁) M₁).obj.hom = (wholeModel (n := n₁) M₀).obj.hom := by
    calc
      _ = L ≫ (P₁.hom.left ≫ Y.obj.hom) := congrArg (fun f => L ≫ f) (Over.w P₁.hom).symm
      _ = (L ≫ P₁.hom.left) ≫ Y.obj.hom := (Category.assoc _ _ _).symm
      _ = P₀.hom.left ≫ Y.obj.hom := congrArg (fun f => f ≫ Y.obj.hom) hL
      _ = _ := Over.w P₀.hom
  let F : wholeModel (n := n₁) M₀ ⟶ wholeModel (n := n₁) M₁ := ObjectProperty.homMk (Over.homMk L hLp)
  have hfac : F ≫ P₁ = P₀ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hL
  let f := nativePointMap F
  have hf := nativePointMap_contMDiff F
  have hbase (z : M₀) : pointMap P₀ z = pointMap P₁ (f z) :=
    (congrArg (fun H : wholeModel (n := n₁) M₀ ⟶ Y => H.hom.left.base ⟨z, mem_univ z⟩) hfac).symm
  have hJinj : Function.Injective (pointMap P₁) := by
    intro y z heq
    exact congrArg Subtype.val (hP₁oi.base_open.injective heq)
  have hP₀proper : IsProperMap (pointMap P₀) :=
    (hG.1.comp ((component_proper hS cS).comp (isoHomeomorph I₀).isProperMap)).comp
      (Homeomorph.Set.univ M₀).symm.isProperMap
  have hfproper : IsProperMap f := isProperMap_of_comp_of_inj hf.continuous (continuous_pointMap P₁)
    (Eq.mp (congrArg IsProperMap (funext hbase)) hP₀proper) hJinj
  let U := OriginalCommonResolution.goodOpen P₁ B hBa.isClosed
  let σ : U → M₀ := fun y => (e y).val
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel n₁) 𝓘(ℂ, ComplexModel n₁) ∞ σ := contMDiff_subtype_val.comp e.contMDiff
  have hright (y : U) : f (σ y) = y.val := hJinj ((hbase (σ y)).symm.trans (he y))
  have hleft (z : M₀) (hz : f z ∉ pointMap P₁ ⁻¹' B) : σ ⟨f z, hz⟩ = z := by
    let y : U := ⟨f z, hz⟩
    have hzgood : pointMap P₀ z ∉ B := by rw [hbase z]; exact hz
    exact hinj (e y).property hzgood ((he y).trans (hbase z).symm)
  have hDa := isComplexAnalyticSubset_preimage P₁ hBa
  have hmod := PrimeNov16OriginalOpenInverse.isAnalyticModification_of_open_inverse hf hfproper hDa hn₁ σ hσ hright hleft
  have hnative : nativeMorphism hmod.1 = F := nativeMorphism_nativePointMap F
  refine ⟨F, ?_, hfac⟩
  rw [← hnative]
  exact nativeMorphism_isProperBimeromorphic hmod

end SGPT.PSH.PrimeNov16OriginalComponentModification
