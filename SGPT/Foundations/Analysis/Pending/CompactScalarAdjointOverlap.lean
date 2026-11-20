import SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap
import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCoordinateDistributions

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactScalarAdjointOverlap

open FirstPass SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms LocalProductCurrents
  CompactDifferentialTests CompactDifferentialOverlap CompactDdcCoordinateExpansion
  ScalarFullTestTranspose TopDegreeDensity ConstantFormProducts ThetaPshChartLimitGluing
  GlobalCurrentPotentials

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Genuine whole tensor overlap data internally produce the scalar adjoint Jacobian law. -/
theorem scalarAdjointTest_overlap_actual_jacobian
    (e f : ComplexChart (m + 1) M)
    (α : TestForm (overlapSource e f) (2 * m))
    (β : TestForm (overlapTarget e f) (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m)
    (hβ : ∀ x, β x ∈ formSpan (m + 1) m)
    (h : OverlapTestRelated e f α β) {x : ComplexModel (m + 1)}
    (hx : x ∈ (chartTransition e f).source) :
    scalarAdjointTest α x = transitionJac e f x *
      scalarAdjointTest β (chartTransition e f x) := by
  have hd := overlapTestRelated_localDdcTestCLM e f α β h
  have heq : localDdcTestCLM α x =
      (localDdcTestCLM β (chartTransition e f x)).compContinuousLinearMap
        (chartTransitionDerivative e f x) := by
    ext v
    exact hd x hx v
  rw [scalarAdjointTest_apply_eq_actual_density α hα,
    scalarAdjointTest_apply_eq_actual_density β hβ, heq,
    ← castForm_compContinuousLinearMap, topDensity_compContinuousLinearMap]
  rw [transitionJac, abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hx)]

/-- Natural source support supplies the entire zero-extended scalar pullback relation. -/
theorem scalarAdjointTest_eq_actual_pullFun
    (e f : ComplexChart (m + 1) M)
    (α : TestForm (overlapSource e f) (2 * m))
    (β : TestForm (overlapTarget e f) (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m)
    (hβ : ∀ x, β x ∈ formSpan (m + 1) m)
    (h : OverlapTestRelated e f α β) :
    (scalarAdjointTest α : ComplexModel (m + 1) → ℝ) =
      pullFun e f (scalarAdjointTest β) := by
  funext x
  by_cases hx : x ∈ (chartTransition e f).source
  · rw [pullFun_of_mem e f _ hx]
    exact scalarAdjointTest_overlap_actual_jacobian e f α β hα hβ h hx
  · rw [pullFun_of_notMem e f _ hx]
    exact image_eq_zero_of_notMem_tsupport
      (fun ht => hx ((scalarAdjointTest α).tsupport_subset ht))

/-- The genuine singular potential supplies integrability and full overlap pairing equality. -/
theorem genuine_theta_potential_full_test_overlap_integral
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e f : ComplexChart (m + 1) M)
    (α : TestForm (overlapSource e f) (2 * m))
    (β : TestForm (overlapTarget e f) (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m)
    (hβ : ∀ x, β x ∈ formSpan (m + 1) m)
    (h : OverlapTestRelated e f α β) :
    Integrable (fun x => scalarAdjointTest α x * (chartFunction u e x).toReal) volume ∧
      Integrable (fun y => scalarAdjointTest β y * (chartFunction u f y).toReal) volume ∧
      (∫ x, scalarAdjointTest α x * (chartFunction u e x).toReal) =
        ∫ y, scalarAdjointTest β y * (chartFunction u f y).toReal := by
  let b := (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).toBasis
  have hvol : b.addHaar = volume :=
    (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).addHaar_eq_volume
  have hLe := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
  have hLf := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential f
  rw [hvol] at hLe hLf
  have hiα : Integrable (fun x => scalarAdjointTest α x * (chartFunction u e x).toReal)
      volume := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hLe.mono_set (overlapSource_le e f)) (scalarAdjointTest α)
  have hiβ : Integrable (fun y => scalarAdjointTest β y * (chartFunction u f y).toReal)
      volume := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hLf.mono_set (overlapTarget_le e f)) (scalarAdjointTest β)
  refine ⟨hiα, hiβ, ?_⟩
  rw [integral_mul_eq_integral_pullFun volume e f (scalarAdjointTest β).tsupport_subset
    (fun y => (chartFunction u f y).toReal),
    ← scalarAdjointTest_eq_actual_pullFun e f α β hα hβ h]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ (chartTransition e f).source
  · have hx' : x ∈ e.val.target ∧ e.val.symm x ∈ f.val.source := by
      simpa [chartTransition] using hx
    have hue : (chartFunction u e x).toReal =
        (chartFunction u f (chartTransition e f x)).toReal := by
      simp [chartFunction, chartTransition, f.val.left_inv hx'.2]
    rw [hue]
  · have hzero : scalarAdjointTest α x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun ht => hx ((scalarAdjointTest α).tsupport_subset ht))
    rw [hzero, zero_mul, zero_mul]

end SGPT.Foundations.Analysis.Pending.CompactScalarAdjointOverlap
