import SGPT.Foundations.Analysis.Pending.DistributionChartPullback

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionDdcChartCovariance
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DDCOverlap DistributionChartPullback ThetaPshChartLimitGluing

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The full adjoint chart identity is a literal original test-space equality. -/
theorem weighted_adjoint_eq
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
    (θ : TestForm (overlapTarget e f) q) (hrel : OverlapTestRelated e f η θ) :
    weightedTestCLM e f (ddcAdjoint B θ) = ddcAdjoint B η := by
  let a : 𝓓(overlapSource e f, ℝ) := weightedTestCLM e f (ddcAdjoint B θ)
  let b : 𝓓(overlapSource e f, ℝ) := ddcAdjoint B η
  have ha : ∀ x, a x = pullFun e f (ddcAdjoint B θ) x := fun _ => rfl
  have heq : (a : ComplexModel n → ℝ) =ᵐ[volume] b := by
    have h := ddcAdjoint_overlap_ae B volume e f η θ hrel
    filter_upwards [h] with x hx
    rw [ha x]
    by_cases hxs : x ∈ (chartTransition e f).source
    · rw [pullFun_of_mem e f _ hxs]
      exact (sub_eq_zero.mp (hx hxs)).symm
    · rw [pullFun_of_notMem e f _ hxs]
      exact (image_eq_zero_of_notMem_tsupport
        (fun ht => hxs (b.tsupport_subset ht))).symm
  apply TestFunction.ext
  exact congrFun (Measure.eq_of_ae_eq heq a.continuous b.continuous)

/-- ANY signed original scalar distribution satisfies the actual full-test
holomorphic ddC covariance, by the internally continuous transpose. -/
theorem wedgePairing_ddC_transpose
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (e f : ComplexChart n M) (S : 𝓓'(overlapSource e f, ℝ))
    (η : TestForm (overlapSource e f) q)
    (θ : TestForm (overlapTarget e f) q) (hrel : OverlapTestRelated e f η θ) :
    wedgePairing B (ddC S) η =
      wedgePairing B (ddC (S.comp (weightedTestCLM e f))) θ := by
  have hS := wedgePairing_ddC B S η
  have hR := wedgePairing_ddC B
    (show 𝓓'(overlapTarget e f, ℝ) from S.comp (weightedTestCLM e f)) θ
  exact hS.trans ((congrArg S (weighted_adjoint_eq B e f η θ hrel)).symm.trans hR.symm)

end SGPT.Foundations.Analysis.Pending.DistributionDdcChartCovariance
