import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.FullLocalSmoothCurrentDensity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorSmooth LocalCurrentPullbackDdc CompactVariableCurrentTests
  LocalCurrentLebesgue LocalCurrentDensityMatrix TopDegreeDensity XiaoChartLocalization
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalCurrentDeterminant BedfordTaylor

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem integrable_smooth_density_test
    {f : ComplexModel (m + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x * formDensity (smoothDDC f x) γ) := by
  have hpt : ∀ x, φ x * formDensity (smoothDDC f x) γ = ∑ a, ∑ b,
      (-(1 / (4 * Real.pi))) *
        (topDensity (n := m + 1)
          (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (coeffForm a b)) *
            (φ x * hessFun a b f x)) := by
    intro x
    by_cases hx : x ∈ U
    · rw [formDensity_apply, ← wedgeDensity_apply, smoothDDC_eq_sum_hessFun hf hx,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, smul_eq_mul, wedgeDensity_apply]
      ring
    · simp [testFunction_eq_zero_of_notMem φ hx]
  simp_rw [hpt]
  have hint : ∀ a b, Integrable (fun x => φ x * hessFun a b f x) := fun a b =>
    (mulSmoothOnCLM (contDiffOn_hessFun hf a b) φ).continuous.integrable_of_hasCompactSupport
      (mulSmoothOnCLM (contDiffOn_hessFun hf a b) φ).hasCompactSupport
  exact integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => ((hint a b).const_mul _).const_mul _

/-- The genuine finite smooth-current correction reassembles to its full wedge density. -/
theorem ddcWedge_oneCurrent_full_test_integral
    {f : ComplexModel (m + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (α : 𝓓(U, RealForm (m + 1) (2 * m)))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    (∑ i, ddcWedge (oneCurrent U) hf (formBasis (m + 1) m i) (coeffTest α i)) =
      ∫ z, topDensity (coordinateWedge (α z) (smoothDDC f z)) := by
  have hcur : ddcMul (oneCurrent U) f = ddcWedge (oneCurrent U) hf :=
    ddcMul_eq_ddcWedge isPositive_oneCurrent
      (show IsClosedCurrent (oneCurrent U) from isClosedAny_oneCurrent (U := U)) hf
  simp_rw [← hcur, ddcMul_oneCurrent_apply hf]
  rw [← integral_finsetSum _ (fun i _ =>
    integrable_smooth_density_test hf (formBasis (m + 1) m i) (coeffTest α i))]
  apply integral_congr_ae
  filter_upwards [] with z
  have he : (⟨α z, hα z⟩ : formSpan (m + 1) m) =
      ∑ i, coeffTest α i z • formBasis (m + 1) m i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using eq_sum_coeffTest α hα z
  change ∑ i, coeffTest α i z * formDensity (smoothDDC f z) (formBasis (m + 1) m i) =
    formDensity (smoothDDC f z) ⟨α z, hα z⟩
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]

/-- A natural compact chart test reads the literal smooth form from its genuine local potential. -/
theorem localPotential_full_chart_wedge_correction
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    (θ : SmoothRealForm (m + 1) X 2) (e : ComplexChart (m + 1) X)
    (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e U ρ)
    (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (G : SmoothRealForm (m + 1) X (2 * m)) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (hU : e.val '' tsupport χ ⊆ U)
    (hG : ∀ z ∈ e.val.target, G.coeff e z ∈ formSpan (m + 1) m) :
    (∑ i, ddcWedge (oneCurrent U) hpot.2.2.1 (formBasis (m + 1) m i)
      (coeffTest (chartTest e χ hχ G hc hs hU) i)) =
      ∫ z, topDensity (coordinateWedge (localizedCoeff e χ G z) (θ.coeff e z)) := by
  let α := chartTest e χ hχ G hc hs hU
  have hα : ∀ z, α z ∈ formSpan (m + 1) m := by
    intro z
    change localizedCoeff e χ G z ∈ formSpan (m + 1) m
    by_cases hz : z ∈ e.val.target
    · rw [localizedCoeff, indicator_of_mem hz]
      exact (formSpan (m + 1) m).smul_mem _ (hG z hz)
    · rw [localizedCoeff, indicator_of_notMem hz]
      exact (formSpan (m + 1) m).zero_mem
  rw [ddcWedge_oneCurrent_full_test_integral hpot.2.2.1 α hα]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ U
  · rw [hpot.2.2.2 hz]
    rfl
  · have ha : α z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (α.tsupport_subset h))
    change topDensity (coordinateWedge (α z) (smoothDDC ρ z)) =
      topDensity (coordinateWedge (α z) (θ.coeff e z))
    have hzero (A : RealForm (m + 1) 2) :
        coordinateWedge (0 : RealForm (m + 1) (2 * m)) A = 0 := by
      simpa only [zero_smul] using coordinateWedge_smul_left
        (0 : ℝ) (0 : RealForm (m + 1) (2 * m)) A
    rw [ha, hzero, hzero]

end SGPT.Foundations.Analysis.Pending.FullLocalSmoothCurrentDensity
