import SGPT.Foundations.Analysis.Pending.BorelChartZeroExtension
import SGPT.Foundations.Analysis.Pending.BorelFullTestPullbackDensity
import SGPT.Foundations.Analysis.Pending.WholeChartPotentialPatchTransition
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! # Genuine signed Borel patch currents in every original whole chart

The complete mathematical statements and entire proofs precede this file.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.BorelChartWeightedPatchCurrent
open FirstPass FirstPass.GlobalPotentialPatches
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalCurrentPullback ChartPartitionRelativeSupports
  WholeChartPotentialPatchTransition BorelSupportedCurrentPullback
  BorelChartZeroExtension BidimensionOneFullTestFunctional
  WeightedFullTestPullbackDensity BorelFullTestPullbackDensity

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

def chartBorelWeightedPullback (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain q} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    LocalProductCurrent n (chartTarget e) q := by
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
  let hw := chartWeight_relativeSupport e χ hχ P.source hsupp hnonneg
  exact borelWeightedExtendedPullback hg.2.2 (isPositive_restrict hT hg.2.1) hg.1
    (chartWeight e χ) hw.1 hw.2.2.2 (chartBorelWeight e f)
    (measurable_chartBorelWeight e f hf) (chartBorelWeight_bound e f hb)

def chartBorelWeightedFullTestFunctional (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    LocalCurrents.TestForm (chartTarget e) 2 →L[ℝ] ℝ :=
  fullTestFunctional (chartBorelWeightedPullback e P hT χ hχ hsupp hnonneg f hf hb)

theorem chartBorelWeightedFullTestFunctional_constant (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (γ : formSpan n 1) (φ : 𝓓(chartTarget e, ℝ)) :
    chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb
      (LocalCurrents.constantTestFormCLM (γ : RealForm n 2) φ) =
        chartBorelWeightedPullback e P hT χ hχ hsupp hnonneg f hf hb γ φ :=
  fullTestFunctional_constant _ γ φ

theorem chartBorelWeightedFullTestFunctional_density (e : ComplexChart n M) (P : Patch θ u)
    {T : LocalProductCurrent n P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (α : LocalCurrents.TestForm (chartTarget e) 2) :
    IntegrableOn (fun y => (f (P.chart.val.symm y) * χ (P.chart.val.symm y)) *
      densityForm hT y (pullSpan 1 (fderiv ℂ (patchToChart e P) y)
        (oneOneProjection (α (patchToChart e P y)))))
      (patchOverlapDomain e P) hT.traceMeasure ∧
    chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb α =
      ∫ y in patchOverlapDomain e P,
        (f (P.chart.val.symm y) * χ (P.chart.val.symm y)) * densityForm hT y
          (pullSpan 1 (fderiv ℂ (patchToChart e P) y)
            (oneOneProjection (α (patchToChart e P y)))) ∂hT.traceMeasure := by
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e P
  let hw := chartWeight_relativeSupport e χ hχ P.source hsupp hnonneg
  have hk := fullTestFunctional_borelWeighted_restriction_density hg.2.2 hT hg.2.1 hg.1
    (chartWeight e χ) hw.1 hw.2.2.2 (chartBorelWeight e f)
    (measurable_chartBorelWeight e f hf) (chartBorelWeight_bound e f hb) α
  have heq (y : ComplexModel n) (hy : y ∈ patchOverlapDomain e P) :
      chartBorelWeight e f (patchToChart e P y) = f (P.chart.val.symm y) ∧
      chartWeight e χ (patchToChart e P y) = χ (P.chart.val.symm y) := by
    have hys : P.chart.val.symm y ∈ e.val.source := hy.2
    have hyt : patchToChart e P y ∈ e.val.target := e.val.map_source hys
    constructor
    · rw [chartBorelWeight, indicator_of_mem hyt]
      change f (e.val.symm (e.val (P.chart.val.symm y))) = f (P.chart.val.symm y)
      rw [e.val.left_inv hys]
    · rw [chartWeight, indicator_of_mem hyt]
      change χ (e.val.symm (e.val (P.chart.val.symm y))) = χ (P.chart.val.symm y)
      rw [e.val.left_inv hys]
  refine ⟨hk.1.congr_fun (fun y hy => ?_)
    (patchOverlapDomain e P).isOpen.measurableSet, ?_⟩
  · dsimp only
    rw [(heq y hy).1, (heq y hy).2]
  · change fullTestFunctional
      (borelWeightedExtendedPullback hg.2.2 (isPositive_restrict hT hg.2.1) hg.1
        (chartWeight e χ) hw.1 hw.2.2.2 (chartBorelWeight e f)
        (measurable_chartBorelWeight e f hf) (chartBorelWeight_bound e f hb)) α = _
    rw [hk.2]
    apply setIntegral_congr_fun (patchOverlapDomain e P).isOpen.measurableSet
    intro y hy
    dsimp only
    rw [(heq y hy).1, (heq y hy).2]

end SGPT.Foundations.Analysis.Pending.BorelChartWeightedPatchCurrent
