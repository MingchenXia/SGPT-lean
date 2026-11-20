import SGPT.Foundations.Analysis.Pending.ActualPrecompactSlotChartPartition
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

/-! # Actual mixed mass lower semicontinuity in capacity

An internally produced finite precompact chart partition and the actual
same-test singular chart inequalities assemble by finite-counting Fatou.
No boundedness, mass limit, or topological intersection bound is input.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedCapacityMassLiminf

open FirstPass FirstPass.PositiveClasses GlobalSlotStokes GlobalNonPluripolar
  ThetaCapacity ChartPartition FiniteGeodesicStripCharts

noncomputable section

private theorem finite_sum_liminf_le {m : ℕ} (f : ℕ → Fin m → ℝ≥0∞) :
    (∑ a, liminf (fun j => f j a) atTop) ≤
      liminf (fun j => ∑ a, f j a) atTop := by
  have h := lintegral_liminf_le (μ := Measure.count) (u := atTop)
    (fun j => measurable_of_finite (f j))
  simpa only [lintegral_fintype, Measure.count_singleton, mul_one] using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

private theorem chartExtend_read_eq (e : ComplexChart n M) (f : M → ℝ)
    (hfs : tsupport f ⊆ e.val.source) : chartExtend e (chartRead e f) = f := by
  funext x
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx, chartRead_of_mem (e.val.map_source hx), e.val.left_inv hx]
  · rw [chartExtend_of_notMem hx,
      image_eq_zero_of_notMem_tsupport (fun hs => hx (hfs hs))]

variable [MeasurableSpace M] [BorelSpace M] [IsComplexManifold n M]

private theorem sum_partition_integrals {m : ℕ} (χ : Fin m → M → ℝ)
    (hsm : ∀ a, ChartSmooth (n := n) (χ a)) (h0 : ∀ a x, 0 ≤ χ a x)
    (h1 : ∀ x, ∑ a, χ a x = 1) (μ : Measure M) :
    (∑ a, ∫⁻ x, ENNReal.ofReal (χ a x) ∂μ) = μ univ := by
  have hadd := lintegral_finsetSum (μ := μ) Finset.univ
    (fun a _ => (GlobalSlotStokes.ChartSmooth.continuous (hsm a)).measurable.ennreal_ofReal)
  calc
    _ = ∫⁻ x, ∑ a, ENNReal.ofReal (χ a x) ∂μ := hadd.symm
    _ = ∫⁻ _, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => h0 a x), h1 x, ENNReal.ofReal_one]
    _ = μ univ := lintegral_one

variable [CompactSpace M]

/-- Weight-one capacity lower semicontinuity of the actual global mixed
mass, with its finite precompact chart partition produced internally. -/
theorem globalMixedMass_le_liminf (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0)) :
    globalMixedMeasure θ v (fun i => (hv i).1) univ ≤
      liminf (fun j => globalMixedMeasure θ (u j) (fun i => (hu j i).1) univ) atTop := by
  classical
  obtain ⟨m, χ, J, D, hsm, h0, hcompact, hclosure, hsupp, hcpt, h1⟩ :=
    ActualPrecompactSlotChartPartition.exists_precompact_chart_partition θ omega.form
  have hlocal (a : Fin m) :
      (∫⁻ x, ENNReal.ofReal (χ a x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
    have hsource : tsupport (χ a) ⊆ (J a).chart.val.source := fun x hx => (hsupp a hx).1
    let K : Set (ComplexModel n) := (J a).chart.val '' tsupport (χ a)
    have hK : IsCompact K := isCompact_image_tsupport (hcpt a) hsource
    have hKD : K ⊆ D a := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsupp a hx).2
    have hn : ∀ z, 0 ≤ chartRead (J a).chart (χ a) z := by
      intro z
      by_cases hz : z ∈ (J a).chart.val.target
      · rw [chartRead_of_mem hz]; exact h0 a _
      · rw [chartRead_of_notMem hz]
    have h := ActualSingularChartMassLiminf.chart_test_liminf omega hu hv hcap (J a)
      (hcompact a) (hclosure a) hK hKD
      (continuous_chartRead (hsm a) (hcpt a) hsource) hn
      (tsupport_chartRead_subset (hcpt a) hsource)
    rwa [chartExtend_read_eq (J a).chart (χ a) hsource] at h
  calc
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (χ a x)
        ∂globalMixedMeasure θ v (fun i => (hv i).1) :=
      (sum_partition_integrals χ hsm h0 h1 _).symm
    _ ≤ ∑ a, liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop :=
      Finset.sum_le_sum (fun a _ => hlocal a)
    _ ≤ liminf (fun j => ∑ a, ∫⁻ x, ENNReal.ofReal (χ a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := finite_sum_liminf_le _
    _ = _ := congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop) (funext fun j =>
      sum_partition_integrals χ hsm h0 h1 _)

end
end SGPT.Foundations.Analysis.Pending.ActualMixedCapacityMassLiminf
