import SGPT.PSH.PrimeNov16OriginalSmoothComposition
import SGPT.PSH.PrimeNov16OriginalStrictTransform
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition

/-! Literal ENTIRE original strict-transform composition; actual factors derived.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalStrictComposition
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative
  OriginalSmoothSourceAnalytic
open PrimeNov16OriginalStrictTransform

theorem original_strictTransform_comp_of_subset_component
    {S Y Z : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth) (hZ : Z.IsSmooth)
    (F : S ⟶ Y) (G : Y ⟶ Z) (hF : IsProperBimeromorphic F) (hG : IsProperBimeromorphic G)
    (E : Set Z.obj.left) (c : ConnectedComponents Z.obj.left) (hEc : E ⊆ OriginalSmoothComponents.componentSet c) :
    originalStrictTransform (F ≫ G) E = originalStrictTransform F (originalStrictTransform G E) := by
  obtain ⟨n, M, ⟨I⟩⟩ := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hZ c
  obtain ⟨cY, N, IY, g, hg, hsqg⟩ :=
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hY hZ G hG c M I
  obtain ⟨cS, P, IS, f, hf, hsqf⟩ :=
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hS hY F hF cY N IY
  let J := I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hZ c
  let JY := IY.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let JS := IS.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let D := pointMap J ⁻¹' E
  have hgm := isAnalyticModification_of_isProperBimeromorphic g hg
  have hfm := isAnalyticModification_of_isProperBimeromorphic f hf
  have hgnative : nativeMorphism hgm.1 = g := nativeMorphism_nativePointMap g
  have hfnative : nativeMorphism hfm.1 = f := nativeMorphism_nativePointMap f
  have hgfull : nativeMorphism hgm.1 ≫ J = IY.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY ≫ G := by
    rw [hgnative]
    exact hsqg
  have hffull : nativeMorphism hfm.1 ≫ JY = IS.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ F := by
    rw [hfnative]
    exact hsqf
  have hcompm := AnalyticModificationComposition.isAnalyticModification_comp hgm hfm
  have hcompnative : nativeMorphism hcompm.1 = f ≫ g :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  have hcompfull : nativeMorphism hcompm.1 ≫ J = IS.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ (F ≫ G) := by
    have hgq : g ≫ J = JY ≫ G := hsqg.trans (Category.assoc _ _ _).symm
    have hfq : f ≫ JY = JS ≫ F := hsqf.trans (Category.assoc _ _ _).symm
    have hsq : (f ≫ g) ≫ J = JS ≫ (F ≫ G) := by
      calc
        _ = f ≫ (g ≫ J) := Category.assoc _ _ _
        _ = f ≫ (JY ≫ G) := congrArg (fun q => f ≫ q) hgq
        _ = (f ≫ JY) ≫ G := (Category.assoc _ _ _).symm
        _ = (JS ≫ F) ≫ G := congrArg (fun q => q ≫ G) hfq
        _ = _ := Category.assoc _ _ _
    rw [hcompnative]
    exact hsq.trans (Category.assoc _ _ _)
  have hFG := PrimeNov16OriginalSmoothComposition.isProperBimeromorphic_comp hS hY hZ F G hF hG
  have hGdict := original_strictTransform_eq_native_image hY hZ G hG cY c N M IY I
    (nativePointMap g) hgm hgfull E hEc
  have hE'c : originalStrictTransform G E ⊆ OriginalSmoothComponents.componentSet cY := by
    intro y hy
    have himage := hGdict ▸ hy
    obtain ⟨z, _hz, rfl⟩ := himage
    exact (IY.hom.hom.left.base ⟨z, mem_univ z⟩).property
  have hJYinj := (PrimeNov16OriginalComponentClosure.isClosedEmbedding_native_component hY cY N IY).injective
  have hpre : pointMap JY ⁻¹' originalStrictTransform G E = strictTransform n (nativePointMap g) D :=
    (congrArg (fun A : Set Y.obj.left => pointMap JY ⁻¹' A) hGdict).trans (preimage_image_eq _ hJYinj)
  have hFdict := original_strictTransform_eq_native_image hS hY F hF cS cY P N IS IY
    (nativePointMap f) hfm hffull (originalStrictTransform G E) hE'c
  have hFdict' : originalStrictTransform F (originalStrictTransform G E) =
      pointMap JS '' strictTransform n (nativePointMap f) (strictTransform n (nativePointMap g) D) :=
    hFdict.trans (congrArg (fun A : Set N => pointMap JS '' strictTransform n (nativePointMap f) A) hpre)
  have hcompdict := original_strictTransform_eq_native_image hS hZ (F ≫ G) hFG cS c P M IS I
    (nativePointMap g ∘ nativePointMap f) hcompm hcompfull E hEc
  exact hcompdict.trans ((congrArg (fun A : Set P => pointMap JS '' A)
    (StrictTransformComposition.strictTransform_comp hgm.1 hfm.1 D)).trans hFdict'.symm)

end SGPT.PSH.PrimeNov16OriginalStrictComposition
