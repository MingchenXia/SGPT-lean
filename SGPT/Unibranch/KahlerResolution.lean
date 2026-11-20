import SGPT.Unibranch.Resolution
import SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler

/-!
# Kähler sources for resolutions of pure embedded complex spaces

The actual reduced complex-space resolution of `thm:res` has a compact native
Kähler source when its original pure analytic carrier embeds in a compact
Kähler manifold. The form is the literal restriction of a Kähler background
on the SAME resolving ambient manifold. This supplies the embedded existence
input of `def:unibranch:L212`; descent of potentials and the general singular
modification theorem remain separate obligations.
-/

set_option autoImplicit false

open Set CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace

namespace SGPT.Unibranch

open SourceReducedComplexSpace

/-- The SAME reduced-space resolution has a compact Kähler source on its
canonical native manifold, including an explicit ambient restriction witness. -/
theorem exists_kahler_resolution_ofClosedAnalytic
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
      IsResolution (resolutionMorphism hWa h) ∧
      Function.Surjective (resolutionMorphism hWa h).hom.left.base ∧
      ∃ omegaW : KahlerBackground d (strictTransform n σ W),
        omegaW = SubmanifoldKahlerRestriction.kahlerBackground hd hreg omega' := by
  obtain ⟨M', _, _, _, σ, E, h, hreg, omega', hCM, hcpt, omegaW, hform, _⟩ :=
    HironakaResolutionKahler.exists_kahler_strictTransform_resolution hWa hpure hd omega
  exact ⟨M', inferInstance, inferInstance, inferInstance, σ, E, h, hreg, omega',
    hCM, hcpt, isResolution_resolutionMorphism hWa h,
    HironakaResolutionSpaceComplex.resolutionMap_surjective h, omegaW, hform⟩

end SGPT.Unibranch
