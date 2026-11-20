import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartCoefficientTransport
import SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Actual continuous supported full alternating-tensor pullback

The coefficient operator field is internally smooth in its true operator norm.
The actual chart derivative supplies that field to the whole supported transport
construction; no smoothness or continuity of a transported tensor is assumed.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalSupportedChartTensorPullback

open FirstPass NaturalSmoothTensorPullback NaturalSupportedChartCoefficientTransport

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual full tensor pullback operator field is internally smooth. -/
theorem contDiffOn_tensor_field (e f : ComplexChart n M) :
    ContDiffOn ℝ ∞
      (fun z => (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (chartTransitionDerivative e f z) :
        ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
          (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
      (chartTransition e f).source := by
  let : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let : FiniteDimensional ℝ ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
    Module.Finite.of_injective
      (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ))
      ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply contDiffOn_clm_apply.mpr
  intro A
  have hF : ContDiffOn ℝ ∞ (chartTransition e f) (chartTransition e f).source :=
    fun z hz => (HolomorphicMaps.chartTransition_contDiffAt_real e f hz).contDiffWithinAt
  exact contDiffOn_compContinuousLinearMap contDiffOn_const
    ((contDiffOn_infty_iff_fderiv_of_isOpen (chartTransition e f).open_source).mp hF).2

/-- Genuine chart pullback on whole supported alternating-tensor smooth spaces. -/
def chartPullCLM (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target) :
    𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      𝓓_{reverseCompact e f K hK}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  weightedPullCLM e f K hK
    (fun z => ContinuousAlternatingMap.compContinuousLinearMapCLM
      (chartTransitionDerivative e f z)) (contDiffOn_tensor_field e f)

/-- Exact full tensor formula, including the original outside-overlap zero values. -/
theorem chartPullCLM_apply (e f : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ (chartTransition e f).target)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ))
    (z : ComplexModel n) :
    chartPullCLM e f K hK A z = (chartTransition e f).source.indicator
      (fun y => (A (chartTransition e f y)).compContinuousLinearMap
        (chartTransitionDerivative e f y)) z := rfl

end SGPT.Foundations.Analysis.Pending.NaturalSupportedChartTensorPullback
