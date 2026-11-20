import SGPT.Foundations.Analysis.Pending.SingularTopFormLocalization
import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalizedFullDdcBridge

open FirstPass ProductTestForms StronglyPositiveForms SingularTopFormLocalization
  XiaoChartLocalization XiaoComplexDifferential XiaoLocalComplexStokes
  CompactDifferentialTests CompactDdcCoordinateExpansion ScalarFullTestTranspose
  TopDegreeDensity ConstantFormProducts LocalProductCurrents

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual compact second differential equals the original global coefficient on targets. -/
theorem localDdc_localizedTensorTest_eq_global_coeff
    (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (Φ : SmoothRealForm n M k) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    localDdcTestCLM (localizedTensorTest e χ hχ Φ hc hs) z =
      (XiaoComplexDifferential.ddc (smulFun χ hχ Φ)).coeff e z := by
  rw [localDdcTestCLM_apply]
  change extDeriv (fun y => localDc (localizedTensorTest e χ hχ Φ hc hs) y) z =
    extDeriv ((dc (smulFun χ hχ Φ)).coeff e) z
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [e.val.open_target.mem_nhds hz] with y hy
  exact localDc_localizedCoeff_eq e χ hχ Φ hy

/-- The full scalar transpose has the literal density of global dd-c of the localized form. -/
theorem scalarAdjoint_localizedTensorTest_eq_global_density
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    (e : ComplexChart (m + 1) X) (χ : X → ℝ)
    (hχ : ChartSmooth (n := m + 1) χ) (Φ : SmoothRealForm (m + 1) X (2 * m))
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source)
    (hΦ : ∀ z ∈ e.val.target, Φ.coeff e z ∈ formSpan (m + 1) m)
    {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) :
    scalarAdjointTest (localizedTensorTest e χ hχ Φ hc hs) z =
      topDensity (castForm (by omega : 2 * m + 1 + 1 = 2 * (m + 1))
        ((XiaoComplexDifferential.ddc (smulFun χ hχ Φ)).coeff e z)) := by
  have hα : ∀ y, localizedTensorTest e χ hχ Φ hc hs y ∈ formSpan (m + 1) m := by
    intro y
    change localizedCoeff e χ Φ y ∈ formSpan (m + 1) m
    by_cases hy : y ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem hy]
      exact (formSpan (m + 1) m).smul_mem _ (hΦ y hy)
    · rw [localizedCoeff, indicator_of_notMem hy]
      exact (formSpan (m + 1) m).zero_mem
  rw [scalarAdjointTest_apply_eq_actual_density _ hα,
    localDdc_localizedTensorTest_eq_global_coeff e χ hχ Φ hc hs hz]

private theorem extDeriv_zero_field (n k : ℕ) (z : ComplexModel n) :
    extDeriv (0 : ComplexModel n → RealForm n k) z = 0 := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
    (fderiv ℝ (fun _ : ComplexModel n => (0 : RealForm n k)) z) = 0
  rw [fderiv_const_apply, map_zero]

/-- Both genuine differentiations preserve local zero off the original scalar support. -/
theorem ddc_coeff_eq_zero_of_notMem_cutoff_support
    (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (Φ : SmoothRealForm n M k) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hs : e.val.symm z ∉ tsupport χ) :
    (XiaoComplexDifferential.ddc (smulFun χ hχ Φ)).coeff e z = 0 := by
  have hscalar : (fun y => χ (e.val.symm y)) =ᶠ[𝓝 z] 0 :=
    (e.val.continuousAt_symm hz).eventually (notMem_tsupport_iff_eventuallyEq.mp hs)
  have htw : (fun y => ((smulFun χ hχ Φ).coeff e y).compContinuousLinearMap
      (modelComplexStructure n)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hscalar] with y hy
    simp only [smulFun_coeff, hy, Pi.zero_apply, zero_smul]
    ext v
    rfl
  have hder := htw.extDeriv
  have hdc : (dc (smulFun χ hχ Φ)).coeff e =ᶠ[𝓝 z] 0 := by
    filter_upwards [hder] with y hy
    change _ • (extDeriv (fun w => ((smulFun χ hχ Φ).coeff e w).compContinuousLinearMap
      (modelComplexStructure n)) y).compContinuousLinearMap (modelComplexStructure n) = 0
    rw [hy, extDeriv_zero_field]
    have hzero : (0 : RealForm n (k + 1)).compContinuousLinearMap (modelComplexStructure n) = 0 := by
      ext v
      rfl
    rw [hzero, smul_zero]
  change extDeriv ((dc (smulFun χ hχ Φ)).coeff e) z = 0
  rw [hdc.extDeriv_eq, extDeriv_zero_field]

end SGPT.Foundations.Analysis.Pending.LocalizedFullDdcBridge
