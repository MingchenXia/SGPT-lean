import SGPT.Envelopes.DinewMeasureConvex
import SGPT.Envelopes.RelativeCY

/-!
# The relative Calabi–Yau theorem from Dinew's bounded inequality

Source `thm:Yau_rel` (`author/chapter_envelopes.tex`, lines 1021–1027). S61's
`source_relative_calabiYau` proves existence unconditionally and uniqueness from S61's global
statement `SGPT.Envelopes.RelativeCY.CommonMeasureConvexLowerBound n M` (FPT
`cor:nonpluripolar-common-measure-convex` for two potentials of one class).
`SGPT.Envelopes.DinewMeasure.commonMeasureConvexLowerBound_of_boundedMultifactor` derives that
statement from the bounded coordinate inequality `BoundedMultifactorCommonMeasure n` (FPT
`thm:bounded-multifactor-common-measure`), so:

* `source_relative_calabiYau_of_boundedMultifactor`: `thm:Yau_rel` (existence and uniqueness)
  given only the local, bounded Dinew inequality on open subsets of `ℂⁿ`;
* `source_relative_calabiYau_of_dim_le_one`: `thm:Yau_rel` **unconditionally** in dimension
  `n ≤ 1` (the bounded inequality is trivial for `n = 1`; S61's statement is void for `n = 0`).

The bounded inequality in dimension `n ≥ 2` is not proved in the project; see the module
docstring of `SGPT.Envelopes.DinewMeasureLocal` for the missing analytic input.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA SGPT.Envelopes.RelativeCY SGPT.Envelopes.DinewMeasure

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [BorelSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- **Source `thm:Yau_rel`** (relative Calabi–Yau theorem), conditional only on the bounded
coordinate Dinew inequality (FPT `thm:bounded-multifactor-common-measure`,
`BoundedMultifactorCommonMeasure n`). Let `X` be a connected compact Kähler manifold, `θ`
represent a big class and `φ` be a model potential with positive mass. For every non-pluripolar
measure `μ` with `μ(X) = ∫_X θ_φ^n` there is a unique `u ∈ E(X, θ; φ)` with `θ_u^n = μ` and
`sup_X u = 0`. -/
theorem source_relative_calabiYau_of_boundedMultifactor
    (hB : BoundedMultifactorCommonMeasure n) (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {μ : Measure M} (hμ : SourceNonPluripolarMeasure (n := n) μ)
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 :=
  source_relative_calabiYau ω hbig hφ (commonMeasureConvexLowerBound_of_boundedMultifactor M hB)
    hμ hmass

omit [ConnectedSpace M] in
/-- S61's `CommonMeasureConvexLowerBound` holds unconditionally in dimension `n ≤ 1`. -/
theorem commonMeasureConvexLowerBound_of_le_one (hn : n ≤ 1) :
    CommonMeasureConvexLowerBound n M := by
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact commonMeasureConvexLowerBound_zero M
  · exact commonMeasureConvexLowerBound_one M

/-- **Source `thm:Yau_rel` in dimension `n ≤ 1`, unconditionally** (existence and uniqueness). -/
theorem source_relative_calabiYau_of_dim_le_one (hn : n ≤ 1) (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {μ : Measure M} (hμ : SourceNonPluripolarMeasure (n := n) μ)
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 :=
  source_relative_calabiYau ω hbig hφ (commonMeasureConvexLowerBound_of_le_one hn) hμ hmass

end SGPT.PSH.VariableComplexAtlas
