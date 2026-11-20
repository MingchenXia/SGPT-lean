import SGPT.Foundations.Analysis.Pending.ActualPrecompactSlotChartPartition
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

/-! # Actual continuous-test lower semicontinuity in capacity

Genuine continuous tests are localized using an internally produced
finite precompact chart partition. No smoothness of the global test
or target mass/weak-limit certificate is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedCapacityContinuousTestLiminf

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

private theorem continuous_chartRead_of_continuous {e : ComplexChart n M} {f : M → ℝ}
    (hf : Continuous f) (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : Continuous (chartRead e f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ e.val.target
  · have hc : ContinuousOn (fun y => f (e.val.symm y)) e.val.target :=
      hf.continuousOn.comp e.val.symm.continuousOn (fun _ _ => mem_univ _)
    have hread : ContinuousOn (chartRead e f) e.val.target :=
      hc.congr (fun y hy => chartRead_of_mem hy)
    exact hread.continuousAt (e.val.open_target.mem_nhds hz)
  · have hzK : z ∉ e.val '' tsupport f := fun h => hz (image_tsupport_subset_target hfs h)
    have hev : chartRead e f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isCompact_image_tsupport hfc hfs).isClosed.isOpen_compl.mem_nhds hzK]
        with y hy
      by_contra h
      exact hy (support_chartRead_subset e f h)
    exact continuousAt_const.congr_of_eventuallyEq hev

private theorem chartExtend_read_eq (e : ComplexChart n M) (f : M → ℝ)
    (hfs : tsupport f ⊆ e.val.source) : chartExtend e (chartRead e f) = f := by
  funext x
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx, chartRead_of_mem (e.val.map_source hx), e.val.left_inv hx]
  · rw [chartExtend_of_notMem hx,
      image_eq_zero_of_notMem_tsupport (fun hs => hx (hfs hs))]

variable [MeasurableSpace M] [BorelSpace M]

private theorem sum_integrals {m : ℕ} (f : Fin m → M → ℝ)
    (hc : ∀ a, Continuous (f a)) (h0 : ∀ a x, 0 ≤ f a x) (μ : Measure M) :
    (∑ a, ∫⁻ x, ENNReal.ofReal (f a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (∑ a, f a x) ∂μ := by
  have hadd := lintegral_finsetSum (μ := μ) Finset.univ
    (fun a _ => (hc a).measurable.ennreal_ofReal)
  refine hadd.symm.trans (lintegral_congr ?_)
  intro x
  exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => h0 a x)).symm

variable [IsComplexManifold n M] [CompactSpace M]

/-- Actual nonnegative continuous global tests satisfy the singular mixed
capacity liminf inequality; no global smoothness of the test is required. -/
theorem lintegral_le_liminf (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    {f : M → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (f x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  classical
  obtain ⟨m, χ, J, D, hsm, h0, hcompact, hclosure, hsupp, hcpt, h1⟩ :=
    ActualPrecompactSlotChartPartition.exists_precompact_chart_partition θ omega.form
  let g : Fin m → M → ℝ := fun a x => f x * χ a x
  have hgc (a : Fin m) : Continuous (g a) :=
    hf.mul (GlobalSlotStokes.ChartSmooth.continuous (hsm a))
  have hg0 (a : Fin m) (x : M) : 0 ≤ g a x := mul_nonneg (hn x) (h0 a x)
  have hgs (a : Fin m) : tsupport (g a) ⊆ tsupport (χ a) := tsupport_mul_subset_right
  have hsum : (fun x => ∑ a, g a x) = f := by
    funext x
    simp only [g, ← Finset.mul_sum, h1 x, mul_one]
  have htotal (μ : Measure M) : (∑ a, ∫⁻ x, ENNReal.ofReal (g a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    have h := sum_integrals g hgc hg0 μ
    exact h.trans (lintegral_congr (fun x => congrArg ENNReal.ofReal (congrFun hsum x)))
  have hlocal (a : Fin m) :
      (∫⁻ x, ENNReal.ofReal (g a x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
    have hsource : tsupport (g a) ⊆ (J a).chart.val.source :=
      fun x hx => (hsupp a (hgs a hx)).1
    have hgcpt : IsCompact (tsupport (g a)) :=
      (hcpt a).of_isClosed_subset (isClosed_tsupport _) (hgs a)
    let K : Set (ComplexModel n) := (J a).chart.val '' tsupport (g a)
    have hK : IsCompact K := isCompact_image_tsupport hgcpt hsource
    have hKD : K ⊆ D a := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsupp a (hgs a hx)).2
    have hread0 : ∀ z, 0 ≤ chartRead (J a).chart (g a) z := by
      intro z
      by_cases hz : z ∈ (J a).chart.val.target
      · rw [chartRead_of_mem hz]; exact hg0 a _
      · rw [chartRead_of_notMem hz]
    have h := ActualSingularChartMassLiminf.chart_test_liminf omega hu hv hcap (J a)
      (hcompact a) (hclosure a) hK hKD
      (continuous_chartRead_of_continuous (hgc a) hgcpt hsource) hread0
      (tsupport_chartRead_subset hgcpt hsource)
    rwa [chartExtend_read_eq (J a).chart (g a) hsource] at h
  calc
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (g a x)
        ∂globalMixedMeasure θ v (fun i => (hv i).1) := (htotal _).symm
    _ ≤ ∑ a, liminf (fun j => ∫⁻ x, ENNReal.ofReal (g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop :=
      Finset.sum_le_sum (fun a _ => hlocal a)
    _ ≤ liminf (fun j => ∑ a, ∫⁻ x, ENNReal.ofReal (g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := finite_sum_liminf_le _
    _ = _ := congrArg (fun q : ℕ → ℝ≥0∞ => liminf q atTop) (funext fun j => htotal _)

end
end SGPT.Foundations.Analysis.Pending.ActualMixedCapacityContinuousTestLiminf
