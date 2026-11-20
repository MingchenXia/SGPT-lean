import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Foundations.Analysis.FirstPass.BlowupSequences

/-! SAME actual original open immersion in SAME native charts: full image,
actual original point lift and existing IsIsomorphismOver predicate.
Blueprint: actual-open-native-isomorphism.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Okounkov
open scoped Topology Manifold ContDiff
variable {X Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (j : X ⟶ Y) [IsOpenImmersion j]
  (n : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (j ≫ f)]
local instance openNativeSourceTopology : TopologicalSpace (SchemeComplexPoint (j ≫ f)) := schemeAnalyticPointTopology (j ≫ f)
local instance openNativeTargetTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance openNativeSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (j ≫ f)) := schemeAnalyticTNChartedSpace (j ≫ f) n
local instance openNativeTargetCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n

omit [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (j ≫ f)] in
/-- Original monomorphism cancellation proves literal actual native point injectivity. -/
theorem actualOpenNative_pointMap_injective : Function.Injective (schemeComplexPointMap (j ≫ f) f j rfl) := by
  intro p q hpq
  apply Subtype.ext
  apply (cancel_mono j).mp
  exact congrArg Subtype.val hpq

omit [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (j ≫ f)] in
/-- ENTIRE original open image, manufactured by the actual original scheme point lifts. -/
theorem actualOpenNative_pointMap_range :
    Set.range (schemeComplexPointMap (j ≫ f) f j rfl) =
      schemeComplexPointImage f ⁻¹' Set.range j := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨schemeComplexPointImage (j ≫ f) q, (Scheme.Hom.comp_apply q.val j default).symm⟩
  · intro hp
    refine ⟨schemeComplexPointLift f j p hp, ?_⟩
    apply Subtype.ext
    exact schemeComplexPointLift_fac f j p hp

/-- Existing EXACT native isomorphism-over predicate on the full genuine original open image. -/
theorem actualOpenNative_isIsomorphismOver :
    IsIsomorphismOver n (schemeComplexPointMap (j ≫ f) f j rfl)
      (schemeComplexPointImage f ⁻¹' Set.range j) := by
  have hmap (p : SchemeComplexPoint (j ≫ f)) :
      schemeComplexPointMap (j ≫ f) f j rfl p ∈ schemeComplexPointImage f ⁻¹' Set.range j :=
    (actualOpenNative_pointMap_range f j).subset ⟨p, rfl⟩
  constructor
  · refine ⟨fun p _ => hmap p, (actualOpenNative_pointMap_injective f j).injOn, ?_⟩
    intro p hp
    obtain ⟨q, hq⟩ := (actualOpenNative_pointMap_range f j).superset hp
    exact ⟨q, hmap q, hq⟩
  · apply Set.disjoint_left.mpr
    intro p _ hp
    apply hp
    have hd := SGPT.NAPotential.NativeSchemeImmersion.openImmersion_mfderiv_injective
      (j ≫ f) f j rfl n p
    let D : ComplexModel n →L[ℂ] ComplexModel n :=
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (schemeComplexPointMap (j ≫ f) f j rfl) p
    have hD : Function.Bijective D := ⟨hd,
      LinearMap.surjective_of_injective (f := D.toLinearMap) hd⟩
    exact hD

end SGPT.Projective.NumEq.AlgebraicCurveDegree
