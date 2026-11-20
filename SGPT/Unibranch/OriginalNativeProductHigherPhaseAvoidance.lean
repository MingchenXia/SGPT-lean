import SGPT.Unibranch.OriginalNativeProductFactoryProfile
import SGPT.Unibranch.OriginalNativeSmoothProductPhaseSpans
import SGPT.Unibranch.OriginalNativePrecompactNeighbourhood

/-! Actual higher-target compact avoidance and internally constructed smooth
inverse branch on a genuine native source neighbourhood. Full Blueprint FIRST. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalNativeProductHigherPhaseAvoidance
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG1NativeFiniteProductState
  HironakaG1NativeFiniteProductHSLex OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothSingularLocus OriginalNativeSmoothBarrierThreshold OriginalNativeHSOuterInitialBound
  OriginalNativeProductFactoryProfile OriginalNativeSmoothProductPhaseSpans
open scoped ProductComplexManifold

private theorem product_smooth {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y)
    (r : ℕ) (O : Opens (productAmbient e r)) : IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

variable {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (r : ℕ)
  (O : Opens (productAmbient e r)) (K : Set (windowSpace e r O).obj.left) (hK : IsCompact K)
  (hne : (K∩intrinsicSingularLocus (windowSpace e r O).obj).Nonempty)
  (L : Set Y.obj.left) (hL : IsCompact L) (hsub : (windowFirst e r O).hom.left.base '' K⊆L)


variable (hlt : toLex (factoryProfile (windowSpace e r O) K hK hne)<toLex (finiteProductHS r (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub))))

include hK hlt in
/-- Strictness of the ACTUAL independently selected leading profiles makes
the literal target threshold absent on ALL the actual compact K. -/
theorem higher_threshold_avoids_compact :
    K∩(windowFirst e r O).hom.left.base ⁻¹' originalSingularHSThreshold Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub))=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxK,hxT⟩
  have hsing := (smoothAt_singular_iff (windowFirst e r O) x (product_smooth e r O x)).mpr hxT.1
  have hlo : toLex (finiteProductHS r (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub)))≤toLex (originalStalkHS (windowSpace e r O) x) := by
    rw [window_point_profile e r O x]
    exact (finiteProductHS_lex_le_iff r _ _).mpr (Pi.toLex_monotone hxT.2)
  have hmax := (OriginalNativeHSShadowPhaseFactory.maximum (windowSpace e r O) K hK hne).maximal x hxK hsing
  exact (not_le_of_gt hlt) (hlo.trans hmax)

/-- A true original source open, from the ACTUAL closed target threshold. -/
def avoidanceOpen : Opens (windowSpace e r O).obj.left :=
  ⟨(windowFirst e r O).hom.left.base ⁻¹' (originalSingularHSThreshold Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub)))ᶜ,
    ((original_hs_threshold_dictionary Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub))).2.1.isClosed.isOpen_compl).preimage
      (windowFirst e r O).hom.left.base.hom.continuous⟩

/-- Internally constructed literal native precompact neighbourhood of ENTIRE K. -/
def neighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood (windowSpace e r O) K
    (avoidanceOpen e r O K hne L hL hsub) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood (windowSpace e r O) K hK
    (avoidanceOpen e r O K hne L hL hsub) (by
      intro x hxK hxT
      have hbad : x∈K∩(windowFirst e r O).hom.left.base ⁻¹' originalSingularHSThreshold Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub)) := ⟨hxK,hxT⟩
      rw [higher_threshold_avoids_compact e r O K hK hne L hL hsub hlt] at hbad
      exact hbad)

/-- The target-only higher phase is skipped by an INTERNALLY constructed
actual smooth lift on the SAME actual compact-retaining source neighbourhood. -/
theorem exists_target_only_smooth_lift {Z : SourceReducedComplexSpace} (p : Z⟶Y)
    (hp : IsIsoOver p (originalSingularHSThreshold Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub)))ᶜ) :
    ∃ b : (neighbourhood e r O K hK hne L hL hsub hlt).source⟶Z,
      IsSmoothMorphism b ∧ b≫p=(neighbourhood e r O K hK hne L hL hsub hlt).inclusion≫windowFirst e r O := by
  let N := neighbourhood e r O K hK hne L hL hsub hlt
  let F := N.inclusion≫windowFirst e r O
  have hF : range F.hom.left.base⊆(originalSingularHSThreshold Y (factoryProfile Y L hL (larger_target_singular_nonempty e r O K hne L hsub)))ᶜ := by
    rintro _ ⟨z,rfl⟩
    have hz : N.inclusion.hom.left.base z∈N.openSet :=
      (Set.ext_iff.mp N.inclusion_range _).mp ⟨z,rfl⟩
    exact N.closure_subset (subset_closure hz)
  obtain ⟨b,hb,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hp F hF
  have hSmooth : IsSmoothMorphism F := isSmoothMorphism_comp _ _
    (isSmoothMorphism_of_isOpenImmersion _ N.inclusion_isOpenImmersion) (product_smooth e r O)
  exact ⟨b,isSmoothMorphism_lift_of_isIsoOver p hp F hF hSmooth b hb,hb⟩

end
end SGPT.Unibranch.OriginalNativeProductHigherPhaseAvoidance
