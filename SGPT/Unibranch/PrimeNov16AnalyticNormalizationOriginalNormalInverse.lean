import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFaithfulOntoGraph
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphInverse
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalRestrictedInverse

/-! Original-only actual NORMAL original complex space and FULL original proper finite projection.
Blueprint: prime-nov16-analytic-normalization-original-normal-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalInverse
open AnalyticGermDecomposition
open PrimeNov16AnalyticNormalizationOriginalFaithfulOntoGraph
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalGraphInverse
open PrimeNov16AnalyticNormalizationOriginalRestrictedInverse
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationLocalGraph

theorem exists_original_normal_space_with_inverse {n : ℕ}
    {Z N : Set (ComplexModel n)} (hZ : IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (k : ℕ) (r : ℝ) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
      (hH : DifferentiableOn ℂ H (ballDomain (n := n) r))
      (hG : ∀ i,DifferentiableOn ℂ (G i) (ballDomain (n := n) r))
      (hC : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z}),
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ H z) ∧
      (¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → H z=0) ∧
      let X := sourceReducedComplexSpaceModel (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} hC
      let Y := sourceSpace (ballDomain (n := n) r) hC H G hH hG
      let f : Y ⟶ X := projection (ballDomain (n := n) r) hC H G hH hG
      ∃ hp : IsProperMap f.hom.left.base,∃ b0 : X.obj.left,b0.val.val=0 ∧
        ∃ U : Opens X.obj.left,b0 ∈ U ∧ ∃ hPC : ParacompactSpace U,
          let _ : ParacompactSpace U := hPC
          let ν := restrictedMap f hp U
          IsIsoOver ν {b | H b.val.val.val ≠ 0} ∧
          Function.Surjective ν.hom.left.base ∧ IsProperMap ν.hom.left.base ∧
          (∀ b : (restrictedBase U).obj.left,(ν.hom.left.base ⁻¹' {b}).Finite) ∧
          (∀ p : (restrictedSource f hp U).obj.left,
            IsDomain ((restrictedSource f hp U).obj.left.presheaf.stalk p).carrier ∧
            IsIntegrallyClosed ((restrictedSource f hp U).obj.left.presheaf.stalk p).carrier) ∧
          ν ≫ baseInclusion U=sourceInclusion f hp U ≫ f := by
  obtain ⟨k,r,H,G,hH,hG,hC,hr,hrN,hHg,hnonzero,hproper,hfinite,b0,hb0,V,hV,hbV,hsurj,_hpV,_hfV,hNormal⟩ :=
    exists_original_faithful_onto_normal_graph hZ hN
  refine ⟨k,r,H,G,hH,hG,hC,hr,hrN,hHg,hnonzero,hproper,b0,hb0,⟨V,hV⟩,hbV,?_,?_⟩
  · change ParacompactSpace {b : {z : ballDomain (n := n) r | z.val ∈ Z} // b ∈ V}
    infer_instance
  · let U : Opens (sourceReducedComplexSpaceModel (ballDomain (n := n) r)
      {z : ballDomain (n := n) r | z.val ∈ Z} hC).obj.left := ⟨V,hV⟩
    let : ParacompactSpace U := by
      change ParacompactSpace {b : {z : ballDomain (n := n) r | z.val ∈ Z} // b ∈ V}
      infer_instance
    let f := projection (ballDomain (n := n) r) hC H G hH hG
    refine ⟨?_,?_,restrictedMap_proper f hproper U,fun b => restrictedMap_fibres_finite f hproper U hfinite b,
      restrictedSource_normal_stalks f hproper U hNormal,restrictedMap_square f hproper U⟩
    · exact restrictedMap_isIsoOver f hproper U _
        (original_graph_isIsoOver (ballDomain (n := n) r) hC H G hH hG)
    · intro b
      obtain ⟨p,hp⟩ := hsurj b
      refine ⟨p,Subtype.ext ?_⟩
      exact (restrictedMap_point f hproper U (show sourceOpen f U from p)).trans
        (congrArg Subtype.val hp)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalInverse
