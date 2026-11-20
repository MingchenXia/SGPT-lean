import SGPT.Foundations.Analysis.Pending.ActualPrecompactSlotChartPartition
import SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousLiminf
import SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousBorelRepresentative
import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityZeroNull
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false

/-! # Actual original bounded quasicontinuous mixed-capacity liminf

Genuine continuous tests are localized using an internally produced
finite precompact chart partition. No smoothness of the global test
or target mass/weak-limit certificate is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedCapacityQuasiContinuousLiminf

open FirstPass FirstPass.PositiveClasses GlobalSlotStokes GlobalNonPluripolar
  ThetaCapacity ChartPartition FiniteGeodesicStripCharts
  CapacityWeightedConvergence PluripolarCapacityZero

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

omit [TopologicalSpace M] [BorelSpace M] in
private theorem sum_integrals {m : ℕ} (f : Fin m → M → ℝ)
    (hm : ∀ a, Measurable (f a)) (h0 : ∀ a x, 0 ≤ f a x) (μ : Measure M) :
    (∑ a, ∫⁻ x, ENNReal.ofReal (f a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (∑ a, f a x) ∂μ := by
  have hadd := lintegral_finsetSum (μ := μ) Finset.univ
    (fun a _ => (hm a).ennreal_ofReal)
  refine hadd.symm.trans (lintegral_congr ?_)
  intro x
  exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => h0 a x)).symm

variable [IsComplexManifold n M] [CompactSpace M]

/-- Actual nonnegative continuous global tests satisfy the singular mixed
capacity liminf inequality; no global smoothness of the test is required. -/
private theorem borel_lintegral_le_liminf (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, 0 ≤ χ x ∧ |χ x| ≤ C)
    (hχm : Measurable χ)
    (hχ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ)
    {f : M → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (χ x * f x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ x * f x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  classical
  obtain ⟨m, part, J, D, hsm, h0, hcompact, hclosure, hsupp, hcpt, h1⟩ :=
    ActualPrecompactSlotChartPartition.exists_precompact_chart_partition θ omega.form
  let g : Fin m → M → ℝ := fun a x => f x * part a x
  have hgc (a : Fin m) : Continuous (g a) :=
    hf.mul (GlobalSlotStokes.ChartSmooth.continuous (hsm a))
  have hg0 (a : Fin m) (x : M) : 0 ≤ g a x := mul_nonneg (hn x) (h0 a x)
  have hgs (a : Fin m) : tsupport (g a) ⊆ tsupport (part a) := tsupport_mul_subset_right
  have hsum : (fun x => ∑ a, g a x) = f := by
    funext x
    simp only [g, ← Finset.mul_sum, h1 x, mul_one]
  have htotal (μ : Measure M) : (∑ a, ∫⁻ x, ENNReal.ofReal (χ x * g a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (χ x * f x) ∂μ := by
    have h := sum_integrals (fun a x => χ x * g a x)
      (fun a => hχm.mul (hgc a).measurable) (fun a x => mul_nonneg (hχC x).1 (hg0 a x)) μ
    exact h.trans (lintegral_congr (fun x => congrArg ENNReal.ofReal
      (by rw [← Finset.mul_sum, congrFun hsum x])))
  have hlocal (a : Fin m) :
      (∫⁻ x, ENNReal.ofReal (χ x * g a x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ x * g a x)
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
    have h := ActualSingularChartQuasiContinuousLiminf.chart_quasiContinuous_test_liminf omega hu hv hcap (J a)
      (hcompact a) (hclosure a) hK hKD hC hχC hχm hχ
      (continuous_chartRead_of_continuous (hgc a) hgcpt hsource) hread0
      (tsupport_chartRead_subset hgcpt hsource)
    rwa [chartExtend_read_eq (J a).chart (g a) hsource] at h
  calc
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (χ x * g a x)
        ∂globalMixedMeasure θ v (fun i => (hv i).1) := (htotal _).symm
    _ ≤ ∑ a, liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ x * g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop :=
      Finset.sum_le_sum (fun a _ => hlocal a)
    _ ≤ liminf (fun j => ∑ a, ∫⁻ x, ENNReal.ofReal (χ x * g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := finite_sum_liminf_le _
    _ = _ := congrArg (fun q : ℕ → ℝ≥0∞ => liminf q atTop) (funext fun j => htotal _)

/-- Original bounded nonnegative quasicontinuous weights satisfy the actual
unbounded mixed-capacity liminf, with no original measurability hypothesis. -/
theorem lintegral_le_liminf (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, 0 ≤ χ x ∧ |χ x| ≤ C)
    (hχ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ)
    {f : M → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (χ x * f x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ x * f x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  obtain ⟨g, hgm, hgB, hgQC, E, _hEm, hEo, heq⟩ :=
    ActualQuasiContinuousBorelRepresentative.exists_borel_representative omega hC
      (fun x => (hχC x).2) hχ
  let gp : M → ℝ := fun x => max (g x) 0
  have hgpm : Measurable gp := hgm.max measurable_const
  have hgpB : ∀ x, 0 ≤ gp x ∧ |gp x| ≤ C := by
    intro x
    have hp : 0 ≤ gp x := le_max_right _ _
    refine ⟨hp, ?_⟩
    rw [abs_of_nonneg hp]
    exact max_le ((le_abs_self _).trans (hgB x)) hC
  have hgpQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) gp := by
    intro eta heta
    obtain ⟨G, hGo, hGc, hgG⟩ := hgQC eta heta
    exact ⟨G, hGo, hGc, fun x hx => (hgG x hx).max continuousWithinAt_const⟩
  have hcapE : thetaCapacity omega.form (fun _ => 0) E = 0 := by
    refine le_antisymm (le_of_forall_gt fun eta heta => ?_) zero_le
    obtain ⟨G, _hGo, hEG, hGc⟩ := hEo eta heta
    exact (thetaCapacity_mono hEG).trans_lt hGc
  have hIntegral (a : Fin n → M → EReal)
      (ha : ∀ i, IsThetaPshPotential (θ i).val (a i)) :
      (∫⁻ x, ENNReal.ofReal (χ x * f x) ∂globalMixedMeasure θ a (fun i => (ha i).1)) =
      ∫⁻ x, ENNReal.ofReal (gp x * f x) ∂globalMixedMeasure θ a (fun i => (ha i).1) := by
    have hnull := ActualMixedCapacityZeroNull.globalMixedMeasure_eq_zero_of_capacity_eq_zero
      omega ha hcapE
    have hae : ∀ᵐ x ∂globalMixedMeasure θ a (fun i => (ha i).1), x ∉ E :=
      by apply ae_iff.mpr; simpa only [not_not, Set.ofPred_mem_eq] using hnull
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    have he : χ x = gp x := by
      dsimp only [gp]
      rw [← heq hx, max_eq_left (hχC x).1]
    rw [he]
  rw [hIntegral v hv]
  have h := borel_lintegral_le_liminf omega hu hv hcap hC hgpB hgpm hgpQC hf hn
  exact h.trans_eq (congrArg (fun a : ℕ → ℝ≥0∞ => liminf a atTop)
    (funext fun j => (hIntegral (u j) (hu j)).symm))

end
end SGPT.Foundations.Analysis.Pending.ActualMixedCapacityQuasiContinuousLiminf
