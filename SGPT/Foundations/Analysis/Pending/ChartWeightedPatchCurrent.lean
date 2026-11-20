import SGPT.Foundations.Analysis.Pending.WholeChartPotentialPatchTransition
import SGPT.Foundations.Analysis.Pending.ChartPartitionRelativeSupports
import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback
import SGPT.Foundations.Analysis.Pending.BidimensionOneFullTestFunctional
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! # Actual weighted patch currents on every original whole chart

All four mathematical statements and complete proofs preceded this source.
The chart transition, restriction, continuity and support are produced here.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ChartWeightedPatchCurrent

open FirstPass FirstPass.GlobalPotentialPatches
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalCurrentPullback ChartPartitionRelativeSupports
  WholeChartPotentialPatchTransition RelativeSupportWeightedCurrentPullback
  BidimensionOneFullTestFunctional

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- The actual positive patch restriction is transported with a genuine global weight. -/
def chartWeightedPullback (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain q} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x) :
    LocalProductCurrent n (chartTarget e) q := by
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
  let hw := chartWeight_relativeSupport e χ hχ P.source hsupp hnonneg
  exact weightedExtendedPullback hg.2.2 (isPositive_restrict hT hg.2.1) hg.1
    (chartWeight e χ) hw.1 hw.2.2.2

/-- The genuine full real two-form functional for the constructed bidimension-one current. -/
def chartWeightedFullTestFunctional (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x) :
    LocalCurrents.TestForm (chartTarget e) 2 →L[ℝ] ℝ :=
  fullTestFunctional (chartWeightedPullback e P hT χ hχ hsupp hnonneg)

/-- Positivity is obtained on all actual finite variable complementary tests. -/
theorem isPositive_chartWeightedPullback (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain q} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x) :
    IsPositive (chartWeightedPullback e P hT χ hχ hsupp hnonneg) := by
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
  let hw := chartWeight_relativeSupport e χ hχ P.source hsupp hnonneg
  exact isPositive_weightedExtendedPullback hg.2.2 (isPositive_restrict hT hg.2.1)
    hg.1 (chartWeight e χ) hw.1 hw.2.2.2 hw.2.1

/-- The actual inverse-map integral and its integrability on the internal restriction. -/
theorem chartWeightedPullback_integral (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain q} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (γ : formSpan n q) (φ : 𝓓(chartTarget e, ℝ)) :
    let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
    let hR := isPositive_restrict hT hg.2.1
    IntegrableOn (fun y => φ (patchToChart e P y) * chartWeight e χ (patchToChart e P y) *
      densityForm hR y (pullSpan q (fderiv ℂ (patchToChart e P) y) γ))
      (patchOverlapDomain e P) hR.traceMeasure ∧
    chartWeightedPullback e P hT χ hχ hsupp hnonneg γ φ =
      ∫ y in patchOverlapDomain e P,
        φ (patchToChart e P y) * chartWeight e χ (patchToChart e P y) *
          densityForm hR y (pullSpan q (fderiv ℂ (patchToChart e P) y) γ)
        ∂hR.traceMeasure := by
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
  let hw := chartWeight_relativeSupport e χ hχ P.source hsupp hnonneg
  exact weightedExtendedPullback_integral hg.2.2 (isPositive_restrict hT hg.2.1)
    hg.1 (chartWeight e χ) hw.1 hw.2.2.2 γ φ

/-- Every actual constant test keeps its pairing under the genuine full-test extension. -/
theorem chartWeightedFullTestFunctional_constant (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (γ : formSpan n 1) (φ : 𝓓(chartTarget e, ℝ)) :
    chartWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg
      (LocalCurrents.constantTestFormCLM (γ : RealForm n 2) φ) =
        chartWeightedPullback e P hT χ hχ hsupp hnonneg γ φ :=
  fullTestFunctional_constant _ γ φ

end SGPT.Foundations.Analysis.Pending.ChartWeightedPatchCurrent
