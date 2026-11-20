import SGPT.Foundations.Analysis.Pending.BoundedPshRadialACApproximation
import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.Pending.BTTruncations
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotMonotoneMeasure
import Mathlib.MeasureTheory.Measure.Regular

set_option autoImplicit false

/-! The actual AC exterior-top measure of the SAME original bounded PSH
current is dominated by its genuine canonical Bedford--Taylor measure.
The full mathematical statement and ENTIRE proof precede this source.
Fatou is used in the correct direction before proving AC compact finiteness.
No desired limit, integrability, finite mass or comparison is an input. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BoundedPshACBedfordTaylorDomination
open FirstPass FirstPass.MongeAmpere LocalProductCurrents LocalCurrentDensityMatrix LocalCurrentDeterminant
  LocalBedfordTaylorProducts
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing HolomorphicPullback
  BoundedPshRadialACApproximation PositiveCurrentACTopMeasure

variable {m : ℕ} {U : Opens (ComplexModel (m+1))}

private theorem weighted_fatou
    {p : ComplexModel (m+1) → ℝ} (hp : IsLocallyBoundedPshOn U p)
    (hT : IsPositive (ddc (scalarTopCurrent (regularDistribution volume p
      (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)))))
    {φ : ComplexModel (m+1) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφ0 : ∀ z, 0 ≤ φ z) :
    ∫⁻ z, ENNReal.ofReal (φ z) ∂acTopMeasure hT ≤
      ENNReal.ofReal (∫ z, φ z ∂MongeAmpere.canonicalBedfordTaylorMeasure U p hp) := by
  classical
  obtain ⟨A₀,hAo,hKA,hclAU,hAc⟩ :=
    exists_open_between_and_isCompact_closure hφc U.isOpen hφU
  let A : Opens (ComplexModel (m+1)) := ⟨A₀,hAo⟩
  have hA : RelativelyCompactIn A U := ⟨hAc,hclAU⟩
  have hAU : (A : Set (ComplexModel (m+1))) ⊆ U := subset_closure.trans hclAU
  obtain ⟨hT',R,hR,K,hK,hKU,hf,hac⟩ :=
    exists_decreasing_radial_ac_approximation hp hA
  let f : ℕ → ComplexModel (m+1) → ℝ :=
    fun j => translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)
  let μA := volume.restrict (A : Set (ComplexModel (m+1)))
  let d := fun z => actualTopPowerDensity (acForm hT z)
  let G := fun j z => ENNReal.ofReal (φ z * smoothDensity (f j) z)
  have htest (j : ℕ) := smoothMeasure_test_integral (hf.1 j) φ hφ hφc hKA
  have hGmeas (j : ℕ) : AEMeasurable (G j) μA :=
    (htest j).2.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hGnn (j : ℕ) : 0 ≤ᵐ[μA] (fun z => φ z * smoothDensity (f j) z) := by
    filter_upwards [ae_restrict_mem A.isOpen.measurableSet] with z hz
    exact mul_nonneg (hφ0 z) (smoothDensity_nonneg ((hf.1 j).2.2 z hz))
  have hGintegral (j : ℕ) :
      ∫⁻ z, G j z ∂μA = ENNReal.ofReal (∫ z, φ z ∂smoothMeasure A (f j) (hf.1 j)) := by
    exact (ofReal_integral_eq_lintegral_ofReal (htest j).2.1 (hGnn j)).symm.trans
      (congrArg ENNReal.ofReal (htest j).2.2.symm)
  have hw := ((MongeAmpere.canonicalBedfordTaylorMeasure_spec U p hp).2.2.2 A hA).2
    f hf φ hφ hφc hKA
  have hGi : Tendsto (fun j => ∫⁻ z, G j z ∂μA) atTop
      (𝓝 (ENNReal.ofReal (∫ z, φ z ∂MongeAmpere.canonicalBedfordTaylorMeasure U p hp))) :=
    (ENNReal.tendsto_ofReal hw).congr fun j => (hGintegral j).symm
  have hGlimit : ∀ᵐ z ∂μA,
      Tendsto (fun j => G j z) atTop (𝓝 (ENNReal.ofReal (φ z * d z))) := by
    filter_upwards [(ae_restrict_iff' A.isOpen.measurableSet).2 hac,
      ae_restrict_mem A.isOpen.measurableSet] with z hz hzA
    have hgeo (j : ℕ) : actualTopPowerDensity (smoothDDC (f j) z) = smoothDensity (f j) z :=
      actualTopPowerDensity_smoothDDC
        (((hf.1 j).1.contDiffAt (A.isOpen.mem_nhds hzA)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    have hd : Tendsto (fun j => smoothDensity (f j) z) atTop (𝓝 (d z)) :=
      hz.2.2.congr hgeo
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hd)
  have hFatou : ∫⁻ z, ENNReal.ofReal (φ z * d z) ∂μA ≤
      ENNReal.ofReal (∫ z, φ z ∂MongeAmpere.canonicalBedfordTaylorMeasure U p hp) := by
    calc
      _ = ∫⁻ z, liminf (fun j => G j z) atTop ∂μA :=
        lintegral_congr_ae (hGlimit.mono fun z hz => hz.liminf_eq.symm)
      _ ≤ liminf (fun j => ∫⁻ z, G j z ∂μA) atTop := lintegral_liminf_le' hGmeas
      _ = _ := hGi.liminf_eq
  have hsupp : Function.support (fun z => ENNReal.ofReal (φ z * d z)) ⊆ A := by
    intro z hz
    by_contra hzA
    have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hzφ => hzA (hKA hzφ)
    simp [hφz] at hz
  have hleft : (∫⁻ z, ENNReal.ofReal (φ z) ∂acTopMeasure hT) =
      ∫⁻ z, ENNReal.ofReal (φ z * d z) ∂μA := by
    unfold acTopMeasure
    rw [restrict_withDensity U.isOpen.measurableSet,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_acTopDensity hT).ennreal_ofReal
        hφ.measurable.ennreal_ofReal]
    calc
      _ = ∫⁻ z in U, ENNReal.ofReal (φ z * d z) ∂volume := by
        apply setLIntegral_congr_fun U.isOpen.measurableSet
        intro z _
        change ENNReal.ofReal (d z) * ENNReal.ofReal (φ z) = _
        rw [mul_comm, ← ENNReal.ofReal_mul (hφ0 z)]
      _ = _ := (setLIntegral_eq_of_support_subset (hsupp.trans hAU)).trans
        (setLIntegral_eq_of_support_subset hsupp).symm
  exact hleft.le.trans hFatou

private theorem finite_on_compacts_of_weighted
    (μ ν : Measure (ComplexModel (m+1)))
    (hw : ∀ {φ : ComplexModel (m+1) → ℝ}, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) →
      ∫⁻ z, ENNReal.ofReal (φ z) ∂μ ≤ ENNReal.ofReal (∫ z, φ z ∂ν))
    {K : Set (ComplexModel (m+1))} (hK : IsCompact K) (hKU : K ⊆ U) : μ K < ⊤ := by
  obtain ⟨χ,hχ0,hχK⟩ := exists_nonneg_testFunction_one_le_on_compact hK hKU
  have hind : K.indicator (1 : ComplexModel (m+1) → ℝ≥0∞) ≤
      fun z => ENNReal.ofReal (χ z) := by
    intro z
    by_cases hz : z ∈ K
    · simpa only [Set.indicator_of_mem hz, Pi.one_apply, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (hχK z hz)
    · simp only [Set.indicator_of_notMem hz]; exact bot_le
  calc
    μ K = ∫⁻ z, K.indicator (1 : ComplexModel (m+1) → ℝ≥0∞) z ∂μ :=
      (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (χ z) ∂μ := lintegral_mono hind
    _ ≤ ENNReal.ofReal (∫ z, χ z ∂ν) :=
      hw χ.continuous χ.hasCompactSupport χ.tsupport_subset hχ0
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- From the original real locally bounded PSH potential alone, internally
produce positivity and domination of its entire actual AC top measure by
its canonical bounded Bedford--Taylor measure on ANY measurable set. -/
theorem acTopMeasure_le_canonicalBedfordTaylorMeasure
    {p : ComplexModel (m+1) → ℝ} (hp : IsLocallyBoundedPshOn U p) :
    let D := regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)
    ∃ hT : IsPositive (ddc (scalarTopCurrent D)),
      acTopMeasure hT ≤ MongeAmpere.canonicalBedfordTaylorMeasure U p hp := by
  classical
  let D := regularDistribution volume p (locallyIntegrableOn_of_plurisubharmonicOn_real hp.1)
  have hT : IsPositive (ddc (scalarTopCurrent D)) :=
    isPositive_ddc_scalarTopCurrent (hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1)
  refine ⟨hT, ?_⟩
  let μ := acTopMeasure hT
  let ν := MongeAmpere.canonicalBedfordTaylorMeasure U p hp
  have hw : ∀ {φ : ComplexModel (m+1) → ℝ}, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) →
      ∫⁻ z, ENNReal.ofReal (φ z) ∂μ ≤ ENNReal.ofReal (∫ z, φ z ∂ν) :=
    fun hφ hφc hφU hφ0 => weighted_fatou hp hT hφ hφc hφU hφ0
  have hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤ :=
    fun _ hK hKU => finite_on_compacts_of_weighted μ ν hw hK hKU
  have hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤ :=
    fun _ hK hKU => MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts hp hK hKU
  have hreal : ∀ φ : ComplexModel (m+1) → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) → ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν := by
    intro φ hφ hφc hφU hφ0
    have hbound := hw hφ hφc hφU hφ0
    have hint : Integrable φ μ :=
      (lintegral_ofReal_ne_top_iff_integrable hφ.aestronglyMeasurable
        (ae_of_all μ hφ0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all μ hφ0)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hφ0)).mp hbound
  have hcompact : ∀ {K : Set (ComplexModel (m+1))}, IsCompact K → K ⊆ U → μ K ≤ ν K :=
    fun hK hKU => BedfordTaylor.measure_le_of_testFunction_integral_le hμf hνf hreal hK hKU
  have : SigmaFinite μ := by
    change SigmaFinite (((volume.withDensity fun z =>
      ENNReal.ofReal (actualTopPowerDensity (acForm hT z)))).restrict U)
    infer_instance
  have : μ.InnerRegular := inferInstance
  apply Measure.le_iff.mpr
  intro B hB
  have hμB : μ B = μ (B ∩ (U : Set (ComplexModel (m+1)))) := by
    change (volume.withDensity _).restrict U B =
      (volume.withDensity _).restrict U (B ∩ (U : Set (ComplexModel (m+1))))
    rw [Measure.restrict_apply hB, Measure.restrict_apply (hB.inter U.isOpen.measurableSet)]
    simp only [inter_assoc, inter_self]
  rw [hμB, (hB.inter U.isOpen.measurableSet).measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_
  exact (hcompact hK (hKB.trans inter_subset_right)).trans
    (measure_mono (hKB.trans inter_subset_left))

end SGPT.Foundations.Analysis.Pending.BoundedPshACBedfordTaylorDomination
