import SGPT.Unibranch.KahlerResolution
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionLiftProperties

/-! The actual compact native Kahler resolution of the SAME constructed normalization.
Blueprint: native-nov16-normalization-kahler-resolution.tex. -/
set_option autoImplicit false
noncomputable section
open Set CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace

namespace SGPT.Unibranch.NativeNov16NormalizationKahlerResolution
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
open PrimeNov16AnalyticNormalizationOriginalResolutionLiftProperties

/-- Raw embedded analytic data manufacture a compact native Kahler resolution
of the SAME normalization, retaining its full unique triangle and literal form. -/
theorem exists_kahler_resolution_of_normalization
    {n d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W)
    (hpure : AnalyticDimensionBasics.IsPureDim (n := n) W d) (hd : d ≤ n)
    (omega : KahlerBackground n M) :
    ∃ (M' : Type) (_ : TopologicalSpace M') (_ : ChartedSpace (ComplexModel n) M')
      (_ : IsComplexManifold n M') (σ : M' → M) (E : List (Set M'))
      (h : IsStrictTransformResolution n W σ E)
      (hreg : ∀ y ∈ strictTransform n σ W,
        RegularAtDim (n := n) (strictTransform n σ W) y d)
      (omega' : KahlerBackground n M'),
      letI := SubmanifoldChartedSpace.chartedSpace hd hreg
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hreg
      IsComplexManifold d (strictTransform n σ W) ∧
      CompactSpace (strictTransform n σ W) ∧
      ∃ l : ofClosedAnalytic (strictTransform n σ W)
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
            h.isClosedSubmanifold) ⟶
          NativeNov16NormalizationSpace.source (ofClosedAnalytic W hWa),
        IsResolution l ∧ Function.Surjective l.hom.left.base ∧
        l ≫ NativeNov16NormalizationSpace.projection (ofClosedAnalytic W hWa) =
          resolutionMorphism hWa h ∧
        (∀ l', l' ≫ NativeNov16NormalizationSpace.projection (ofClosedAnalytic W hWa) =
          resolutionMorphism hWa h → l' = l) ∧
        ∃ omegaR : KahlerBackground d (strictTransform n σ W),
          omegaR = SubmanifoldKahlerRestriction.kahlerBackground hd hreg omega' := by
  obtain ⟨M', _, _, _, σ, E, h, hreg, omega', hCM, hcpt, hres, _hsurj, omegaR, hform⟩ :=
    exists_kahler_resolution_ofClosedAnalytic hWa hpure hd omega
  let := SubmanifoldChartedSpace.chartedSpace hd hreg
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hreg
  let f := resolutionMorphism hWa h
  let l := resolutionLift f hres
  have hl : IsResolution l := resolutionLift_isResolution f hres
  refine ⟨M', inferInstance, inferInstance, inferInstance, σ, E, h, hreg, omega',
    hCM, hcpt, l, hl, hl.2.surjective, resolutionLift_projection f hres, ?_, omegaR, hform⟩
  intro l' htriangle
  exact resolutionLift_unique f hres l' htriangle

end SGPT.Unibranch.NativeNov16NormalizationKahlerResolution
