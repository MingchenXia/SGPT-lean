import SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import SGPT.Foundations.Analysis.FirstPass.ExteriorDerivative

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap

open FirstPass SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms CompactDifferentialTests

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Natural related overlap tests internally produce the differentiated relation. -/
theorem overlapTestRelated_exteriorTestCLM
    (e f : ComplexChart n M) (α : TestForm (overlapSource e f) k)
    (β : TestForm (overlapTarget e f) k) (h : OverlapTestRelated e f α β) :
    OverlapTestRelated e f (exteriorTestCLM α) (exteriorTestCLM β) := by
  intro z hz v
  have heq : (α : ComplexModel n → RealForm n k) =ᶠ[𝓝 z]
      fun w => (β (chartTransition e f w)).compContinuousLinearMap
        (fderiv ℝ (chartTransition e f) w) := by
    filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with w hw
    ext u
    exact h w hw u
  have hdiff : DifferentiableAt ℝ (β : ComplexModel n → RealForm n k)
      (chartTransition e f z) :=
    (ContDiff.differentiable β.contDiff (by simp)).differentiableAt
  have hnatural := extDeriv_pullback hdiff
    (HolomorphicMaps.chartTransition_contDiffAt_real e f hz)
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [exteriorTestCLM_apply, exteriorTestCLM_apply, heq.extDeriv_eq, hnatural]
  rfl

/-- The actual holomorphic derivative commutes with the model complex twist. -/
theorem overlapTestRelated_postcomp_complexStructure
    (e f : ComplexChart n M) (α : TestForm (overlapSource e f) k)
    (β : TestForm (overlapTarget e f) k) (h : OverlapTestRelated e f α β) :
    OverlapTestRelated e f
      (TestFunction.postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) α)
      (TestFunction.postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) β) := by
  intro z hz v
  change α z (fun i => Complex.I • v i) =
    β (chartTransition e f z)
      (fun i => Complex.I • chartTransitionDerivative e f z (v i))
  rw [h z hz]
  congr 1
  funext i
  exact chartTransitionDerivative_complex_smul e f z hz Complex.I (v i)

/-- The literal two-twist normalization is natural for arbitrary actual test degree. -/
theorem overlapTestRelated_localDcTestCLM
    (e f : ComplexChart n M) (α : TestForm (overlapSource e f) k)
    (β : TestForm (overlapTarget e f) k) (h : OverlapTestRelated e f α β) :
    OverlapTestRelated e f (localDcTestCLM α) (localDcTestCLM β) := by
  have hj := overlapTestRelated_postcomp_complexStructure e f α β h
  have hd := overlapTestRelated_exteriorTestCLM e f _ _ hj
  have hjd := overlapTestRelated_postcomp_complexStructure e f _ _ hd
  intro z hz v
  change (((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
      ((exteriorTestCLM
        (TestFunction.postcompCLM
          (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) α))
          z).compContinuousLinearMap (modelComplexStructure n)) v =
    (((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
      ((exteriorTestCLM
        (TestFunction.postcompCLM
          (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) β))
          (chartTransition e f z)).compContinuousLinearMap (modelComplexStructure n))
            (fun i => chartTransitionDerivative e f z (v i))
  change (((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) * _) =
    (((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) * _)
  exact congrArg (fun t : ℝ => ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) * t) (hjd z hz v)

/-- Second differentiation internally preserves the full overlap tensor equation. -/
theorem overlapTestRelated_localDdcTestCLM
    (e f : ComplexChart n M) (α : TestForm (overlapSource e f) k)
    (β : TestForm (overlapTarget e f) k) (h : OverlapTestRelated e f α β) :
    OverlapTestRelated e f (localDdcTestCLM α) (localDdcTestCLM β) :=
  overlapTestRelated_exteriorTestCLM e f _ _ (overlapTestRelated_localDcTestCLM e f α β h)

end SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap
