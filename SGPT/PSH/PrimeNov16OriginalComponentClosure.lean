import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-! Literal closure in the ENTIRE original space, all other components absent.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalComponentClosure
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

theorem isClosedEmbedding_native_component {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    IsClosedEmbedding (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c)) := by
  let H : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left :=
    (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I)
  exact (OriginalSmoothComponents.component_isClopen hY c).1.isClosedEmbedding_subtypeVal.comp H.isClosedEmbedding

theorem closure_native_component_image {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) (A : Set M) :
    closure (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) '' A) =
      pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) '' closure A :=
  (isClosedEmbedding_native_component hY c M I).closure_image_eq A

theorem closure_image_subset_component {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) (A : Set M) :
    closure (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) '' A) ⊆
      OriginalSmoothComponents.componentSet c := by
  rw [closure_native_component_image hY c M I A]
  rintro _ ⟨z, _hz, rfl⟩
  exact (I.hom.hom.left.base ⟨z, mem_univ z⟩).property

theorem disjoint_closure_image_other_component {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c d : ConnectedComponents Y.obj.left) (hcd : c ≠ d) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) (A : Set M) :
    Disjoint (closure (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) '' A))
      (OriginalSmoothComponents.componentSet d) :=
  (OriginalSmoothComponents.componentSet_pairwise_disjoint hcd).mono_left
    (closure_image_subset_component hY c M I A)

end SGPT.PSH.PrimeNov16OriginalComponentClosure
