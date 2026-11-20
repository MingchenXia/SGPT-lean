import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionZeroAnalytic

/-! Actual whole section density manufactures the original book bimeromorphic predicate.
Blueprint: prime-nov16-analytic-normalization-original-section-bimeromorphic.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionBimeromorphic
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalSectionZeroAnalytic
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open HironakaActualAnalyticSubspace
open SourceReducedComplexSpace

theorem actual_proper_bimeromorphic_of_section_density {n : ℕ}
    (P : Opens (ComplexModel n)) (C : Set P) (hC : IsComplexAnalyticSubset (n := n) C)
    (W : Opens (TopCat.of C)) (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier)
    {Y : SourceReducedComplexSpace} (f : Y ⟶ coordinateSource P C hC W)
    (hp : IsProperMap f.hom.left.base)
    (ht : Dense {x : W | original_value_hom C W x s ≠ 0})
    (hs : Dense (f.hom.left.base ⁻¹' {x | original_value_hom C W x s ≠ 0}))
    (hi : IsIsoOver f {x | original_value_hom C W x s ≠ 0}) : IsProperBimeromorphic f := by
  refine ⟨hp,{x | original_value_hom C W x s=0},actual_section_zero_isAnalytic P C hC W s,?_,?_,hi⟩
  · apply interior_eq_empty_iff_dense_compl.mpr
    exact ht
  · apply interior_eq_empty_iff_dense_compl.mpr
    exact hs

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionBimeromorphic
