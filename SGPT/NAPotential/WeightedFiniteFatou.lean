import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# Constant-preserving Fatou for a finite family

An independent measure-theoretic lemma for the two Skoda limit stages.  It
does not assert that solutions or bounds exist: the later division proof must
produce its actual family and its single uniform bound from smooth division.
The conclusion retains that single bound for the sum, without multiplying by
the number of components.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Fatou followed by monotone convergence for a finite family.  The input
bound is a bound on the entire sum, so the output keeps the same constant. -/
theorem lintegral_finite_sum_iSup_le_of_tendsto
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    {w : ℕ → ComplexModel n → ℝ≥0∞}
    (hwmono : ∀ z ∈ U, Monotone fun j => w j z)
    (hwmeas : ∀ j, AEMeasurable (w j) (volume.restrict U))
    {F : ℕ → ι → ComplexModel n → ℂ} {H : ι → ComplexModel n → ℂ}
    (hF : ∀ j i, ContinuousOn (F j i) U) (hH : ∀ i, ContinuousOn (H i) U)
    (hconv : ∀ i z, z ∈ U → Tendsto (fun j => F j i z) atTop (𝓝 (H i z)))
    {A : ℝ≥0∞}
    (hbound : ∀ j, (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2) * w j z) ≤ A) :
    (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * ⨆ j, w j z) ≤ A := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hFc : ∀ j, ContinuousOn (fun z => ∑ i, ‖F j i z‖ ^ 2) U := fun j =>
    continuousOn_finsetSum _ fun i _ => (hF j i).norm.pow 2
  have hHc : ContinuousOn (fun z => ∑ i, ‖H i z‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => (hH i).norm.pow 2
  have hfixed : ∀ m, (∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * w m z) ≤ A := by
    intro m
    have hmeas : ∀ j, AEMeasurable
        (fun z => ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2) * w m z) (volume.restrict U) :=
      fun j => ((ENNReal.continuous_ofReal.comp_continuousOn (hFc j)).aemeasurable hUm).mul
        (hwmeas m)
    calc
      _ ≤ ∫⁻ z in U, liminf
          (fun j => ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2) * w m z) atTop := by
        refine setLIntegral_mono' hUm fun z hz => ?_
        have ht : Tendsto (fun j => ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2))) := by
          apply ENNReal.tendsto_ofReal
          exact tendsto_finsetSum _ fun i _ => ((hconv i z hz).norm).pow 2
        by_cases hzero : ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) = 0
        · rw [hzero, zero_mul]
          exact zero_le
        · exact ((ENNReal.Tendsto.mul_const ht (Or.inl hzero)).liminf_eq).ge
      _ ≤ liminf (fun j => ∫⁻ z in U,
          ENNReal.ofReal (∑ i, ‖F j i z‖ ^ 2) * w m z) atTop := lintegral_liminf_le' hmeas
      _ ≤ A := by
        refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
        filter_upwards [eventually_ge_atTop m] with j hj
        refine (setLIntegral_mono' hUm fun z hz => ?_).trans (hbound j)
        exact mul_le_mul_of_nonneg_left (hwmono z hz hj) zero_le
  calc
    _ = ∫⁻ z in U, ⨆ j, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * w j z := by
      refine lintegral_congr fun z => ?_
      rw [ENNReal.mul_iSup]
    _ = ⨆ j, ∫⁻ z in U, ENNReal.ofReal (∑ i, ‖H i z‖ ^ 2) * w j z := by
      refine lintegral_iSup' (fun j =>
        ((ENNReal.continuous_ofReal.comp_continuousOn hHc).aemeasurable hUm).mul (hwmeas j)) ?_
      refine (ae_restrict_iff' hUm).mpr (Eventually.of_forall fun z hz i j hij => ?_)
      exact mul_le_mul_of_nonneg_left (hwmono z hz hij) zero_le
    _ ≤ A := iSup_le hfixed

end SGPT.NAPotential.GAGAMult
