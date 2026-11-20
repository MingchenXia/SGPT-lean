import SGPT.Foundations.Analysis.Pending.CompactScalarAdjointOverlap
import SGPT.Foundations.Analysis.Pending.XiaoChartLocalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularTopFormChartTransport

open FirstPass SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  TopDegreeDensity ThetaPshChartLimitGluing GlobalCurrentPotentials

/-- Canonical complex-oriented density of an arbitrary genuine compact top-form test. -/
def topDensityTest {n : ℕ} {U : Opens (ComplexModel n)}
    (α : TestForm U (2 * n)) : 𝓓(U, ℝ) :=
  TestFunction.postcompCLM
    (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ (topBasis n)) α

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Whole natural top-form transport produces the actual absolute-Jacobian identity. -/
theorem topDensityTest_overlap_actual_jacobian
    (e f : ComplexChart n M)
    (α : TestForm (overlapSource e f) (2 * n))
    (β : TestForm (overlapTarget e f) (2 * n))
    (h : OverlapTestRelated e f α β) {x : ComplexModel n}
    (hx : x ∈ (chartTransition e f).source) :
    topDensityTest α x = transitionJac e f x *
      topDensityTest β (chartTransition e f x) := by
  have heq : α x = (β (chartTransition e f x)).compContinuousLinearMap
      (chartTransitionDerivative e f x) := by
    ext v
    exact h x hx v
  change topDensity (α x) = transitionJac e f x * topDensity (β (chartTransition e f x))
  rw [heq, topDensity_compContinuousLinearMap]
  rw [transitionJac, abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hx)]

/-- Bundled source support internally gives the entire zero-extended scalar pullback. -/
theorem topDensityTest_eq_actual_pullFun
    (e f : ComplexChart n M)
    (α : TestForm (overlapSource e f) (2 * n))
    (β : TestForm (overlapTarget e f) (2 * n))
    (h : OverlapTestRelated e f α β) :
    (topDensityTest α : ComplexModel n → ℝ) = pullFun e f (topDensityTest β) := by
  funext x
  by_cases hx : x ∈ (chartTransition e f).source
  · rw [pullFun_of_mem e f _ hx]
    exact topDensityTest_overlap_actual_jacobian e f α β h hx
  · rw [pullFun_of_notMem e f _ hx]
    exact image_eq_zero_of_notMem_tsupport
      (fun ht => hx ((topDensityTest α).tsupport_subset ht))

/-- Original genuine chart L1 supplies both integrabilities and singular top-form transport. -/
theorem genuine_theta_potential_top_form_overlap_integral
    (hn : 0 < n) (θ : SmoothRealForm n M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) (e f : ComplexChart n M)
    (α : TestForm (overlapSource e f) (2 * n))
    (β : TestForm (overlapTarget e f) (2 * n))
    (h : OverlapTestRelated e f α β) :
    Integrable (fun x => topDensityTest α x * (chartFunction u e x).toReal) volume ∧
      Integrable (fun y => topDensityTest β y * (chartFunction u f y).toReal) volume ∧
      (∫ x, topDensityTest α x * (chartFunction u e x).toReal) =
        ∫ y, topDensityTest β y * (chartFunction u f y).toReal := by
  let b := (stdOrthonormalBasis ℝ (ComplexModel n)).toBasis
  have hvol : b.addHaar = volume :=
    (stdOrthonormalBasis ℝ (ComplexModel n)).addHaar_eq_volume
  have hLe := quasiPsh_chart_locallyIntegrable b hn u hu.quasiPshPotential e
  have hLf := quasiPsh_chart_locallyIntegrable b hn u hu.quasiPshPotential f
  rw [hvol] at hLe hLf
  have hiα : Integrable (fun x => topDensityTest α x * (chartFunction u e x).toReal)
      volume := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hLe.mono_set (overlapSource_le e f)) (topDensityTest α)
  have hiβ : Integrable (fun y => topDensityTest β y * (chartFunction u f y).toReal)
      volume := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hLf.mono_set (overlapTarget_le e f)) (topDensityTest β)
  refine ⟨hiα, hiβ, ?_⟩
  rw [integral_mul_eq_integral_pullFun volume e f (topDensityTest β).tsupport_subset
    (fun y => (chartFunction u f y).toReal),
    ← topDensityTest_eq_actual_pullFun e f α β h]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ (chartTransition e f).source
  · have hx' : x ∈ e.val.target ∧ e.val.symm x ∈ f.val.source := by
      simpa [chartTransition] using hx
    have hue : (chartFunction u e x).toReal =
        (chartFunction u f (chartTransition e f x)).toReal := by
      simp [chartFunction, chartTransition, f.val.left_inv hx'.2]
    rw [hue]
  · have hzero : topDensityTest α x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun ht => hx ((topDensityTest α).tsupport_subset ht))
    rw [hzero, zero_mul, zero_mul]

end SGPT.Foundations.Analysis.Pending.SingularTopFormChartTransport
