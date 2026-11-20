import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift
import SGPT.Unibranch.OriginalBimeromorphicSourceIso

/-! Actual comparison of full native models of the same original component.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalComponentModelIso
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative

theorem exists_actual_native_component_comparison
    {S : SourceReducedComplexSpace} (hS : S.IsSmooth) (c : ConnectedComponents S.obj.left)
    {n : ℕ} (N₀ N₁ : CMfd n)
    (I₀ : wholeModel (n := n) N₀ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS c)
    (I₁ : wholeModel (n := n) N₁ ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS c) :
    ∃ (e : N₀ → N₁) (he : IsAnalyticModification (n := n) e),
      nativeMorphism he.1 ≫ (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c) =
        I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS c := by
  let E := I₀.trans I₁.symm
  have hid : IsProperBimeromorphic (𝟙 (wholeModel (n := n) N₁)) := by
    refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
    exact IsIsoOver.id_of_isOpen _ (by simp)
  have hE : IsProperBimeromorphic E.hom := by
    simpa only [Category.comp_id] using hid.precomp_iso E
  let e := nativePointMap E.hom
  have he : IsAnalyticModification (n := n) e := isAnalyticModification_of_isProperBimeromorphic E.hom hE
  have hnative : nativeMorphism he.1 = E.hom := nativeMorphism_nativePointMap E.hom
  refine ⟨e, he, ?_⟩
  rw [hnative]
  simp only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

end SGPT.PSH.PrimeNov16OriginalComponentModelIso
