import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredChart
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion

/-! Literal selected local-normalizer bases embed openly into the same original space.
Blueprint: prime-nov16-analytic-normalization-original-centered-base-map.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredBaseMap
open PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

variable {n : ℕ} {Z : Set (ComplexModel n)} {P Ω : Opens (ComplexModel n)}
  (hP : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
  (hΩ : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z))
  (hPΩ : P ≤ Ω)
  {X : SourceReducedComplexSpace}
  (j : sourceReducedComplexSpaceModel Ω ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z) hΩ ⟶ X)
  (U : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hP).obj.left)
  [ParacompactSpace U]

def centeredBaseMap : restrictedBase U ⟶ X :=
  baseInclusion U ≫ nativeOpenMap Z P Ω hP hΩ hPΩ ≫ j

instance centeredBaseMap_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion j.hom.left] :
    LocallyRingedSpace.IsOpenImmersion (centeredBaseMap hP hΩ hPΩ j U).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((baseInclusion U).hom.left ≫ (nativeOpenMap Z P Ω hP hΩ hPΩ).hom.left ≫ j.hom.left)
  infer_instance

theorem centeredBaseMap_origin (b : ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
    (hb : b ∈ U) (hb0 : b.val.val = 0)
    (c : ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z)) (hc0 : c.val.val = 0) :
    (centeredBaseMap hP hΩ hPΩ j U).hom.left.base ⟨b,hb⟩ = j.hom.left.base c := by
  change j.hom.left.base ((nativeOpenMap Z P Ω hP hΩ hPΩ).hom.left.base b) = j.hom.left.base c
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change b.val.val = c.val.val
  exact hb0.trans hc0.symm
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredBaseMap
