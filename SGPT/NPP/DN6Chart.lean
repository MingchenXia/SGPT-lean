import SGPT.NPP.DN6Pairing
import SGPT.Envelopes.LapClassSmoothing
import SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration
import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace

/-!
# Reading the Kähler volume and test functions in a chart

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 7: "We work in a fixed coordinate
chart …").  Helpers transporting the pairing `∫_Y F θ ω^N` to a chart `e`:

* `chartVol`: the density `V_e` of `ω^N` in the chart (positive and smooth on the target);
* `chartTransfer θ = V_e · (θ ∘ e⁻¹)`, extended by zero: smooth with support in `e(tsupport θ)`
  (`contDiff_chartTransfer`, `support_chartTransfer_subset`);
* `integral_mul_eq_chart`: `∫_Y F θ ω^N = ∫ F(e⁻¹ z) (chartTransfer θ)(z) dz` for every `F`;
* `chartRep g = 1_{target} · (g ∘ e⁻¹)`: strongly measurable for strongly measurable `g`
  (`stronglyMeasurable_chartRep`) and integrable on compact subsets of the target for
  `ω^N`-integrable `g` (`integrableOn_chartRep`);
* `continuous_chartExtend_of_vanish`, `integral_mul_chartExtend`: the inverse transport of
  continuous densities vanishing off a compact subset of the target.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending KahlerLaplacianChart IntegrationCurrent ChartPartition
open SmoothMixedMeasureDensity ProductTestForms StronglyPositiveForms TopDegreeDensity

/-- `χ ρ` is smooth when `χ` is smooth with support in an open set on which `ρ` is smooth. -/
theorem contDiff_mul_of_tsupport_subset' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} (hD : IsOpen D) {χ ρ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχD : tsupport χ ⊆ D)
    (hρ : ContDiffOn ℝ ∞ ρ D) : ContDiff ℝ ∞ (fun z => ρ z * χ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ D
  · exact (hρ.contDiffAt (hD.mem_nhds hz)).mul hχ.contDiffAt
  · have hnot : z ∉ tsupport χ := fun h => hz (hχD h)
    have hev : (fun z => ρ z * χ z) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hnot] with w hw
      simp [hw]
    exact contDiffAt_const.congr_of_eventuallyEq hev

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The density of `ω^N` in the chart `e`. -/
def chartVol (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z : ComplexModel N) : ℝ :=
  topDensity ((formPow wY.form.val N).coeff e z)

theorem chartVol_pos (wY : KahlerBackground N Y) (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) : 0 < chartVol wY e z :=
  topDensity_formPow_pos wY.isKahler.1 hz

theorem contDiffOn_chartVol (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (chartVol wY e) e.val.target :=
  (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ (topBasis N)).contDiff.comp_contDiffOn
    ((formPow wY.form.val N).smooth e)

/-- The chart representative `1_{target} · (g ∘ e⁻¹)` of a function on `Y`. -/
def chartRep (e : ComplexChart N Y) (g : Y → ℝ) : ComplexModel N → ℝ :=
  e.val.target.indicator (g ∘ e.val.symm)

theorem chartRep_of_mem (e : ComplexChart N Y) (g : Y → ℝ) {z : ComplexModel N}
    (hz : z ∈ e.val.target) : chartRep e g z = g (e.val.symm z) := by
  rw [chartRep, indicator_of_mem hz]; rfl

/-- The chart transfer `V_e · (θ ∘ e⁻¹)` of a test function, extended by zero. -/
def chartTransfer (wY : KahlerBackground N Y) (e : ComplexChart N Y) (θ : Y → ℝ) :
    ComplexModel N → ℝ :=
  fun z => chartVol wY e z * chartRep e θ z

theorem chartTransfer_of_notMem (wY : KahlerBackground N Y) (e : ComplexChart N Y) (θ : Y → ℝ)
    {z : ComplexModel N} (hz : z ∉ e.val.target) : chartTransfer wY e θ z = 0 := by
  simp [chartTransfer, chartRep, indicator_of_notMem hz]

theorem support_chartTransfer_subset (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    (θ : Y → ℝ) : Function.support (chartTransfer wY e θ) ⊆ e.val '' tsupport θ := by
  intro z hz
  by_cases hzt : z ∈ e.val.target
  · have h : θ (e.val.symm z) ≠ 0 := by
      intro h0
      apply hz
      simp [chartTransfer, chartRep_of_mem e θ hzt, h0]
    exact ⟨e.val.symm z, subset_tsupport θ h, e.val.right_inv hzt⟩
  · exact absurd (chartTransfer_of_notMem wY e θ hzt) hz

theorem tsupport_chartTransfer_subset [CompactSpace Y] (wY : KahlerBackground N Y)
    (e : ComplexChart N Y) {θ : Y → ℝ} (hθs : tsupport θ ⊆ e.val.source) :
    tsupport (chartTransfer wY e θ) ⊆ e.val '' tsupport θ := by
  have hc : IsCompact (e.val '' tsupport θ) :=
    (isClosed_tsupport θ).isCompact.image_of_continuousOn (e.val.continuousOn.mono hθs)
  exact closure_minimal (support_chartTransfer_subset wY e θ) hc.isClosed

theorem contDiff_chartTransfer [CompactSpace Y] (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {θ : Y → ℝ} (hθ : ChartSmooth (n := N) θ) (hθs : tsupport θ ⊆ e.val.source) :
    ContDiff ℝ ∞ (chartTransfer wY e θ) := by
  obtain ⟨h1, -, h3⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e hθ
    (isClosed_tsupport θ).isCompact hθs
  exact contDiff_mul_of_tsupport_subset' e.val.open_target h1 h3 (contDiffOn_chartVol wY e)

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem chartDensity_eq_chartVol (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    chartDensity (fun _ => wY.form) e = fun z => ENNReal.ofReal (chartVol wY e z) := by
  funext z
  simp only [chartDensity, chartVol, formPow_coeff, formPower_eq_wedgeProd, topDensity_wedgeProd]

/-- The Kähler volume on a chart source, as a measure on the target. -/
def chartMeasure (wY : KahlerBackground N Y) (e : ComplexChart N Y) : Measure (ComplexModel N) :=
  (volume.restrict e.val.target).withDensity fun z => ENNReal.ofReal (chartVol wY e z)

theorem restrict_kahlerVolume_eq_map (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    (kahlerVolume wY).restrict e.val.source = Measure.map e.val.symm (chartMeasure wY e) := by
  have h := NaturalHermitianKahlerVolumeCalibration.kahlerVolume_restrict_chart wY e
  rw [chartDensity_eq_chartVol] at h
  exact h

theorem aemeasurable_symm_chartMeasure (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    AEMeasurable e.val.symm (chartMeasure wY e) :=
  (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac
    (withDensity_absolutelyContinuous _ _)

theorem aemeasurable_chartVol (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    AEMeasurable (fun z => ENNReal.ofReal (chartVol wY e z)) (volume.restrict e.val.target) :=
  (ENNReal.continuous_ofReal.comp_continuousOn (contDiffOn_chartVol wY e).continuousOn).aemeasurable
    e.val.open_target.measurableSet

theorem toReal_chartVol_ae (wY : KahlerBackground N Y) (e : ComplexChart N Y) :
    (fun z => (ENNReal.ofReal (chartVol wY e z)).toReal) =ᵐ[volume.restrict e.val.target]
      chartVol wY e := by
  filter_upwards [ae_restrict_mem e.val.open_target.measurableSet] with z hz
  exact ENNReal.toReal_ofReal (chartVol_pos wY e hz).le

/-- `∫_Y F ω^N` read in a chart, for measurable `F` vanishing off the chart source. -/
theorem integral_eq_chart (wY : KahlerBackground N Y) (e : ComplexChart N Y) {F : Y → ℝ}
    (hFm : StronglyMeasurable F) (hF : ∀ x ∉ e.val.source, F x = 0) :
    ∫ x, F x ∂kahlerVolume wY = ∫ z in e.val.target, chartVol wY e z * F (e.val.symm z) := by
  calc ∫ x, F x ∂kahlerVolume wY = ∫ x in e.val.source, F x ∂kahlerVolume wY :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm
    _ = ∫ x, F x ∂(Measure.map e.val.symm (chartMeasure wY e)) := by
        rw [restrict_kahlerVolume_eq_map]
    _ = ∫ z, F (e.val.symm z) ∂chartMeasure wY e :=
        integral_map (aemeasurable_symm_chartMeasure wY e) hFm.aestronglyMeasurable
    _ = ∫ z in e.val.target, (ENNReal.ofReal (chartVol wY e z)).toReal • F (e.val.symm z) :=
        integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_chartVol wY e)
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫ z in e.val.target, chartVol wY e z * F (e.val.symm z) := by
        refine integral_congr_ae ?_
        filter_upwards [toReal_chartVol_ae wY e] with z hz
        rw [hz, smul_eq_mul]

/-- Integrability read in a chart. -/
theorem integrableOn_chart_of_integrable (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {F : Y → ℝ} (hFm : StronglyMeasurable F) (hF : Integrable F (kahlerVolume wY)) :
    IntegrableOn (fun z => chartVol wY e z * F (e.val.symm z)) e.val.target volume := by
  have h1 : Integrable F (Measure.map e.val.symm (chartMeasure wY e)) := by
    rw [← restrict_kahlerVolume_eq_map]; exact hF.restrict
  have h2 := (integrable_map_measure hFm.aestronglyMeasurable
    (aemeasurable_symm_chartMeasure wY e)).mp h1
  have h3 := (integrable_withDensity_iff_integrable_smul₀' (aemeasurable_chartVol wY e)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp h2
  refine Integrable.congr h3 ?_
  filter_upwards [toReal_chartVol_ae wY e] with z hz
  simp only [Function.comp_apply, smul_eq_mul]
  rw [hz]

/-- **The pairing with a test function supported in a chart, read in the chart.** -/
theorem integral_mul_eq_chart (wY : KahlerBackground N Y) (e : ComplexChart N Y) {F : Y → ℝ}
    (hFm : StronglyMeasurable F) {θ : Y → ℝ} (hθ : Continuous θ)
    (hθs : tsupport θ ⊆ e.val.source) :
    ∫ y, F y * θ y ∂kahlerVolume wY =
      ∫ z, F (e.val.symm z) * chartTransfer wY e θ z := by
  have hm : StronglyMeasurable fun y => F y * θ y := hFm.mul hθ.stronglyMeasurable
  rw [integral_eq_chart wY e hm fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hθs h), mul_zero]]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.val.target)
    (f := fun z => F (e.val.symm z) * chartTransfer wY e θ z)
    fun z hz => by rw [chartTransfer_of_notMem wY e θ hz, mul_zero]]
  refine setIntegral_congr_fun e.val.open_target.measurableSet fun z hz => ?_
  simp only [chartTransfer, chartRep_of_mem e θ hz]
  ring

theorem stronglyMeasurable_chartRep (e : ComplexChart N Y) {g : Y → ℝ}
    (hg : StronglyMeasurable g) : StronglyMeasurable (chartRep e g) := by
  classical
  by_cases hne : e.val.target.Nonempty
  swap
  · have h0 : chartRep e g = fun _ => 0 := by
      funext z
      exact indicator_of_notMem (fun hz => hne ⟨z, hz⟩) _
    rw [h0]; exact stronglyMeasurable_const
  obtain ⟨z₁, -⟩ := hne
  set y₀ := e.val.symm z₁
  have hm : Measurable (e.val.target.piecewise e.val.symm fun _ => y₀) :=
    ContinuousOn.measurable_piecewise e.val.continuousOn_symm continuousOn_const
      e.val.open_target.measurableSet
  have h1 : StronglyMeasurable (g ∘ e.val.target.piecewise e.val.symm fun _ => y₀) :=
    hg.comp_measurable hm
  have h2 := h1.indicator e.val.open_target.measurableSet
  have heq : chartRep e g = e.val.target.indicator
      (g ∘ e.val.target.piecewise e.val.symm fun _ => y₀) := by
    funext z
    by_cases hz : z ∈ e.val.target
    · simp [chartRep, indicator_of_mem hz, piecewise_eq_of_mem _ _ _ hz]
    · simp [chartRep, indicator_of_notMem hz]
  rw [heq]
  exact h2

/-- The chart representative of an `ω^N`-integrable function is integrable on compact subsets of
the target. -/
theorem integrableOn_chartRep (wY : KahlerBackground N Y) (e : ComplexChart N Y) {g : Y → ℝ}
    (hgm : StronglyMeasurable g) (hg : Integrable g (kahlerVolume wY)) {K : Set (ComplexModel N)} (hK : IsCompact K)
    (hKt : K ⊆ e.val.target) : IntegrableOn (chartRep e g) K volume := by
  have hF : Integrable (e.val.source.indicator g) (kahlerVolume wY) :=
    hg.indicator e.val.open_source.measurableSet
  have h1 := integrableOn_chart_of_integrable wY e (hgm.indicator e.val.open_source.measurableSet) hF
  have h2 : IntegrableOn (fun z => chartVol wY e z *
      e.val.source.indicator g (e.val.symm z)) K volume := h1.mono_set hKt
  have hinv : ContinuousOn (fun z => (chartVol wY e z)⁻¹) K :=
    ((contDiffOn_chartVol wY e).continuousOn.mono hKt).inv₀ fun z hz =>
      (chartVol_pos wY e (hKt hz)).ne'
  have h3 := h2.continuousOn_mul hinv hK
  refine h3.congr_fun (fun z hz => ?_) hK.measurableSet
  have hzt := hKt hz
  simp only
  rw [indicator_of_mem (e.val.map_target hzt), chartRep_of_mem e g hzt, ← mul_assoc,
    inv_mul_cancel₀ (chartVol_pos wY e hzt).ne', one_mul]

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- The extension by zero of a function continuous on the target and vanishing off a compact
subset of it is continuous. -/
theorem continuous_chartExtend_of_vanish (e : ComplexChart N Y) {β : ComplexModel N → ℝ}
    (hβ : ContinuousOn β e.val.target) {K : Set (ComplexModel N)} (hK : IsCompact K)
    (hKt : K ⊆ e.val.target) (hβv : ∀ z ∉ K, β z = 0) : Continuous (chartExtend e β) := by
  set L : Set Y := e.val.symm '' K with hL
  have hLc : IsCompact L := hK.image_of_continuousOn (e.val.continuousOn_symm.mono hKt)
  have hzero : ∀ y ∉ L, chartExtend e β y = 0 := by
    intro y hy
    by_cases hys : y ∈ e.val.source
    · rw [chartExtend_of_mem hys]
      exact hβv _ fun h => hy ⟨_, h, e.val.left_inv hys⟩
    · exact chartExtend_of_notMem hys
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hys : y ∈ e.val.source
  · have hev : chartExtend e β =ᶠ[𝓝 y] fun y => β (e.val y) := by
      filter_upwards [e.val.open_source.mem_nhds hys] with y' hy' using chartExtend_of_mem hy'
    refine ContinuousAt.congr ?_ hev.symm
    exact (hβ.continuousAt (e.val.open_target.mem_nhds (e.val.map_source hys))).comp
      (e.val.continuousAt hys)
  · have hyL : y ∉ L := by
      rintro ⟨z, hz, rfl⟩
      exact hys (e.val.map_target (hKt hz))
    have hev : chartExtend e β =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hLc.isClosed.isOpen_compl.mem_nhds hyL] with y' hy' using hzero y' hy'
    exact continuousAt_const.congr hev.symm

/-- `∫_Y g · ext(φ / V_e) ω^N = ∫ chartRep g · φ` for `φ` vanishing off the target. -/
theorem integral_mul_chartExtend (wY : KahlerBackground N Y) (e : ComplexChart N Y) {g : Y → ℝ}
    (hgm : StronglyMeasurable g) {φ : ComplexModel N → ℝ}
    (hc : Continuous (chartExtend e (fun z => φ z / chartVol wY e z)))
    (hφv : ∀ z ∉ e.val.target, φ z = 0) :
    ∫ y, g y * chartExtend e (fun z => φ z / chartVol wY e z) y ∂kahlerVolume wY =
      ∫ z, chartRep e g z * φ z := by
  have hm : StronglyMeasurable fun y => g y * chartExtend e (fun z => φ z / chartVol wY e z) y :=
    hgm.mul hc.stronglyMeasurable
  rw [integral_eq_chart wY e hm fun x hx => by
    rw [chartExtend_of_notMem hx, mul_zero]]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.val.target)
    (f := fun z => chartRep e g z * φ z) fun z hz => by rw [hφv z hz, mul_zero]]
  refine setIntegral_congr_fun e.val.open_target.measurableSet fun z hz => ?_
  show chartVol wY e z * (g (e.val.symm z) *
    chartExtend e (fun z => φ z / chartVol wY e z) (e.val.symm z)) = chartRep e g z * φ z
  rw [chartExtend_of_mem (e.val.map_target hz), e.val.right_inv hz, chartRep_of_mem e g hz]
  field_simp [(chartVol_pos wY e hz).ne']

end SGPT.NPP.DN6
