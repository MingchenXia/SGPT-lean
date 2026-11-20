import SGPT.Unibranch.OriginalNativeSmoothBarrierThreshold

/-! Actual compact-image calibration of INDEPENDENTLY selected native phase
factory profiles on ONE honest product chart. Full Blueprint FIRST. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalNativeProductFactoryProfile
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG1NativeFiniteProductState
  HironakaG1NativeFiniteProductHSLex OriginalLocalEmbeddingStalkHS
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothSingularLocus OriginalNativeSmoothBarrierThreshold OriginalNativeHSOuterInitialBound
open scoped ProductComplexManifold

variable {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (r : ℕ)
  (O : Opens (productAmbient e r))

private theorem product_smooth : IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

/-- Singular nonemptiness of the ACTUAL image, no target-surjectivity premise. -/
theorem image_singular_nonempty (K : Set (windowSpace e r O).obj.left)
    (hne : (K∩intrinsicSingularLocus (windowSpace e r O).obj).Nonempty) :
    ((windowFirst e r O).hom.left.base '' K∩intrinsicSingularLocus Y.obj).Nonempty := by
  obtain ⟨x,hx,hxs⟩:=hne
  exact ⟨(windowFirst e r O).hom.left.base x,⟨x,hx,rfl⟩,
    (smoothAt_singular_iff (windowFirst e r O) x (product_smooth e r O x)).mp hxs⟩

/-- The target factory's ordinary nonemptiness is internally derived. -/
theorem larger_target_singular_nonempty (K : Set (windowSpace e r O).obj.left)
    (hne : (K∩intrinsicSingularLocus (windowSpace e r O).obj).Nonempty)
    (L : Set Y.obj.left) (hsub : (windowFirst e r O).hom.left.base '' K⊆L) :
    (L∩intrinsicSingularLocus Y.obj).Nonempty :=
  (image_singular_nonempty e r O K hne).mono (inter_subset_inter_left _ hsub)

/-- The actual attained maxima give only the TRUE Lex bound for a larger L. -/
theorem factoryProfile_le_larger_target (K : Set (windowSpace e r O).obj.left) (hK : IsCompact K)
    (hne : (K∩intrinsicSingularLocus (windowSpace e r O).obj).Nonempty)
    (L : Set Y.obj.left) (hL : IsCompact L)
    (hsub : (windowFirst e r O).hom.left.base '' K⊆L) :
    toLex (factoryProfile (windowSpace e r O) K hK hne) ≤
      toLex (finiteProductHS r (factoryProfile Y L hL
        (larger_target_singular_nonempty e r O K hne L hsub))) := by
  let MS := OriginalNativeHSShadowPhaseFactory.maximum (windowSpace e r O) K hK hne
  let MT := OriginalNativeHSShadowPhaseFactory.maximum Y L hL
    (larger_target_singular_nonempty e r O K hne L hsub)
  have hs : (windowFirst e r O).hom.left.base MS.point∈intrinsicSingularLocus Y.obj :=
    (smoothAt_singular_iff (windowFirst e r O) _ (product_smooth e r O _)).mp MS.singular
  have hb := MT.maximal _ (hsub ⟨MS.point,MS.in_compact,rfl⟩) hs
  change toLex (originalStalkHS (windowSpace e r O) MS.point) ≤
    toLex (finiteProductHS r (originalStalkHS Y MT.point))
  rw [window_point_profile e r O MS.point]
  exact (finiteProductHS_lex_le_iff r _ _).mpr hb

/-- The literal independently chosen factory profiles agree on the ACTUAL
compact image; no chosen maximum point or phase record is replaced. -/
theorem factoryProfile_image (K : Set (windowSpace e r O).obj.left) (hK : IsCompact K)
    (hne : (K∩intrinsicSingularLocus (windowSpace e r O).obj).Nonempty) :
    factoryProfile (windowSpace e r O) K hK hne = finiteProductHS r
      (factoryProfile Y ((windowFirst e r O).hom.left.base '' K)
        (hK.image (windowFirst e r O).hom.left.base.hom.continuous)
        (image_singular_nonempty e r O K hne)) := by
  let hImage := hK.image (windowFirst e r O).hom.left.base.hom.continuous
  let MS := OriginalNativeHSShadowPhaseFactory.maximum (windowSpace e r O) K hK hne
  let MT := OriginalNativeHSShadowPhaseFactory.maximum Y ((windowFirst e r O).hom.left.base '' K)
    hImage (image_singular_nonempty e r O K hne)
  have hle := factoryProfile_le_larger_target e r O K hK hne
    ((windowFirst e r O).hom.left.base '' K) hImage Subset.rfl
  obtain ⟨x,hx,hfx⟩ := MT.in_compact
  have hsing : x∈intrinsicSingularLocus (windowSpace e r O).obj :=
    (smoothAt_singular_iff (windowFirst e r O) x (product_smooth e r O x)).mpr (hfx.symm ▸ MT.singular)
  have hxProfile : originalStalkHS (windowSpace e r O) x=
      finiteProductHS r (originalStalkHS Y MT.point) :=
    (window_point_profile e r O x).trans
      (congrArg (fun y=>finiteProductHS r (originalStalkHS Y y)) hfx)
  have hge : toLex (finiteProductHS r (originalStalkHS Y MT.point))≤
      toLex (originalStalkHS (windowSpace e r O) MS.point) := by
    rw [←hxProfile]
    exact MS.maximal x hx hsing
  exact congrArg ofLex (le_antisymm hle hge)

end
end SGPT.Unibranch.OriginalNativeProductFactoryProfile
