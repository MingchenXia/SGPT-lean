import SGPT.PSH.PrimeNov16OriginalStrictTransform

/-! Native strict equality iff literal full ORIGINAL strict equality. Full BP first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalStrictTransformEquality
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic
open PrimeNov16OriginalStrictTransform

theorem native_strict_equality_iff_original
    {S Y₀ Y₁ : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth)
    (G₀ : S ⟶ Y₀) (G₁ : S ⟶ Y₁) (hG₀ : IsProperBimeromorphic G₀) (hG₁ : IsProperBimeromorphic G₁)
    (cS : ConnectedComponents S.obj.left) (c₀ : ConnectedComponents Y₀.obj.left) (c₁ : ConnectedComponents Y₁.obj.left)
    {n : ℕ} (N M₀ M₁ : CMfd n)
    (I : wholeModel (n := n) N ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS cS)
    (I₀ : wholeModel (n := n) M₀ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY₀ c₀)
    (I₁ : wholeModel (n := n) M₁ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY₁ c₁)
    (f₀ : N → M₀) (f₁ : N → M₁)
    (hf₀ : IsAnalyticModification (n := n) f₀) (hf₁ : IsAnalyticModification (n := n) f₁)
    (hsq₀ : nativeMorphism hf₀.1 ≫ (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₀ c₀) =
      I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G₀)
    (hsq₁ : nativeMorphism hf₁.1 ≫ (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ c₁) =
      I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G₁)
    (E₀ : Set Y₀.obj.left) (E₁ : Set Y₁.obj.left)
    (hE₀ : E₀ ⊆ OriginalSmoothComponents.componentSet c₀) (hE₁ : E₁ ⊆ OriginalSmoothComponents.componentSet c₁) :
    strictTransform n f₀ (pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₀ c₀) ⁻¹' E₀) =
      strictTransform n f₁ (pointMap (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ c₁) ⁻¹' E₁) ↔
      originalStrictTransform G₀ E₀ = originalStrictTransform G₁ E₁ := by
  have h₀ := original_strictTransform_eq_native_image hS hY₀ G₀ hG₀ cS c₀ N M₀ I I₀ f₀ hf₀ hsq₀ E₀ hE₀
  have h₁ := original_strictTransform_eq_native_image hS hY₁ G₁ hG₁ cS c₁ N M₁ I I₁ f₁ hf₁ hsq₁ E₁ hE₁
  have hinj := (PrimeNov16OriginalComponentClosure.isClosedEmbedding_native_component hS cS N I).injective
  constructor
  · intro h
    exact h₀.trans ((congrArg (fun A => pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) '' A) h).trans h₁.symm)
  · intro h
    exact hinj.image_injective (h₀.symm.trans (h.trans h₁))

end SGPT.PSH.PrimeNov16OriginalStrictTransformEquality
