import SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSelectorSections

/-! Actual original quotient sections manufacture genuine analytic zero subsets.
Blueprint: prime-nov16-analytic-normalization-original-section-zero-analytic.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionZeroAnalytic
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open HironakaActualAnalyticSubspace
open SourceReducedComplexSpace

theorem actual_section_zero_isAnalytic {n : ℕ} (P : Opens (ComplexModel n))
    (C : Set P) (hC : IsComplexAnalyticSubset (n := n) C) (W : Opens (TopCat.of C))
    (s : ((actualSubspaceSheaf (n := n) C).presheaf.obj (op W)).carrier) :
    (coordinateSource P C hC W).IsAnalyticSubset {x | original_value_hom C W x s=0} := by
  obtain ⟨F,hF,_huniq⟩ := exists_unique_coordinate_morphism (k := 1) P C hC W (fun _ => s)
  let z0 : (domainSpace (⊤ : Opens (ComplexModel 1))).obj.left := ⟨⟨0,by trivial⟩,by trivial⟩
  have hA := (isAnalyticSubset_singleton (domainSpace (⊤ : Opens (ComplexModel 1))) z0).preimage F
  have he : {x : (coordinateSource P C hC W).obj.left | original_value_hom C W x s=0}=
      F.hom.left.base ⁻¹' {z0} := by
    ext x
    constructor
    · intro hx
      change F.hom.left.base x=z0
      apply Subtype.ext
      apply Subtype.ext
      ext i
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact (hF x 0).trans hx
    · intro hx
      change F.hom.left.base x=z0 at hx
      exact (hF x 0).symm.trans (congrArg (fun z => z.val.val 0) hx)
  exact he.symm ▸ hA

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionZeroAnalytic
