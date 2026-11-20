import SGPT.Foundations.Analysis.Pending.RawPshRadialConvexACApproximation
import SGPT.Foundations.Analysis.Pending.SmoothConvexCutoffDensityLowerBound
import SGPT.Foundations.Analysis.Pending.BoundedPshACBedfordTaylorDomination

set_option autoImplicit false

/-! Weighted actual AC measures of the SAME original raw PSH current are
internally dominated by the canonical BT measures of ALL convex cutoffs.
Full mathematics and ENTIRE proof precede this source. Fatou precedes
compact finiteness. No approximation, limit, finite-mass or class cert.
Complex(m+1) includes one; genuine dimension zero has separate counting. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawPshWeightedACBTDomination
open MongeAmpere FirstPass FirstPass.MongeAmpere LocalProductCurrents LocalCurrentDensityMatrix LocalCurrentDeterminant
  LocalBedfordTaylorProducts ScalarLeviPositiveCurrent LocalPositiveCurrentGluing HolomorphicPullback
  RawPshRadialConvexACApproximation RawPshConvexCutoff SmoothConvexCutoffDensityLowerBound
  PositiveCurrentACTopMeasure

variable {m : ℕ} {U : Opens (ComplexModel (m+1))}

private theorem weighted_fatou
    {u : ComplexModel (m+1) → EReal} (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥)
    (hL : LocallyIntegrableOn (fun z => (u z).toReal) U volume)
    (hT : IsPositive (ddc (scalarTopCurrent (regularDistribution volume (fun z => (u z).toReal) hL))))
    (b : ℝ) {φ : ComplexModel (m+1) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφ0 : ∀ z, 0 ≤ φ z) :
    (∫⁻ z, ENNReal.ofReal (φ z) ∂(volume.withDensity (fun z =>
      ENNReal.ofReal (SmoothMax.trans ((u z).toReal-b)^(m+1) * actualTopPowerDensity (acForm hT z)))).restrict U) ≤
    ENNReal.ofReal (∫ z, φ z ∂canonicalBedfordTaylorMeasure U
      (fun z => b+SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal-b))
      (isLocallyBoundedPshOn_convexCutoff U hu b)) := by
  classical
  obtain ⟨A₀,hAo,hKA,hclAU,hAc⟩ := exists_open_between_and_isCompact_closure hφc U.isOpen hφU
  let A : Opens (ComplexModel (m+1)) := ⟨A₀,hAo⟩
  have hA : RelativelyCompactIn A U := ⟨hAc,hclAU⟩
  have hAU : (A : Set (ComplexModel (m+1))) ⊆ U := subset_closure.trans hclAU
  obtain ⟨hT',R,hR,K,hK,hKU,hf,hanti,hpoint,hcut,hac⟩ :=
    exists_raw_radial_convex_ac_approximation hu hfin hL hA
  let f : ℕ → ComplexModel (m+1) → ℝ := fun j =>
    translationPairing volume (K.indicator (fun y => (u y).toReal)) (explicitRadialKernel R hR j)
  let q : ComplexModel (m+1) → ℝ := fun z =>
    b+SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal-b)
  let g : ℕ → ComplexModel (m+1) → ℝ := fun j z => b+SmoothMax.posPart (f j z-b)
  let hq := isLocallyBoundedPshOn_convexCutoff U hu b
  let μA := volume.restrict (A : Set (ComplexModel (m+1)))
  let d := fun z => actualTopPowerDensity (acForm hT z)
  let w := fun z => SmoothMax.trans ((u z).toReal-b)^(m+1)
  let F := fun j z => ENNReal.ofReal (φ z * (SmoothMax.trans (f j z-b)^(m+1) * smoothDensity (f j) z))
  let G := fun j z => ENNReal.ofReal (φ z * smoothDensity (g j) z)
  have hc : IsDecreasingApproximation A q g := hcut b
  have htest (j : ℕ) := FirstPass.MongeAmpere.smoothMeasure_test_integral (hc.1 j) φ hφ hφc hKA
  have htestRaw (j : ℕ) := FirstPass.MongeAmpere.smoothMeasure_test_integral (hf j) φ hφ hφc hKA
  have hgL := (integrable_indicator_of_locallyIntegrableOn_isCompact hL hK hKU).locallyIntegrable
  have hfGlob (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f j) :=
    contDiff_translationPairing hgL (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff R hR j)
  have hFmeas (j : ℕ) : AEMeasurable (F j) μA := by
    have hwj : Continuous (fun z => SmoothMax.trans (f j z-b)^(m+1)) :=
      (SmoothMax.continuous_trans.comp ((hfGlob j).continuous.sub continuous_const)).pow _
    have hm := ((htestRaw j).2.1.aestronglyMeasurable.aemeasurable.mul
      hwj.measurable.aemeasurable).ennreal_ofReal
    convert hm using 1
    funext z
    dsimp only [F, Pi.mul_apply]
    congr 1
    ring
  have hGnn (j : ℕ) : 0 ≤ᵐ[μA] (fun z => φ z * smoothDensity (g j) z) := by
    filter_upwards [ae_restrict_mem A.isOpen.measurableSet] with z hz
    exact mul_nonneg (hφ0 z) (smoothDensity_nonneg ((hc.1 j).2.2 z hz))
  have hGintegral (j : ℕ) :
      (∫⁻ z, G j z ∂μA) = ENNReal.ofReal (∫ z, φ z ∂smoothMeasure A (g j) (hc.1 j)) :=
    (ofReal_integral_eq_lintegral_ofReal (htest j).2.1 (hGnn j)).symm.trans
      (congrArg ENNReal.ofReal (htest j).2.2.symm)
  have hw := ((canonicalBedfordTaylorMeasure_spec U q hq).2.2.2 A hA).2
    g hc φ hφ hφc hKA
  have hGi : Tendsto (fun j => ∫⁻ z, G j z ∂μA) atTop
      (𝓝 (ENNReal.ofReal (∫ z, φ z ∂canonicalBedfordTaylorMeasure U q hq))) :=
    (ENNReal.tendsto_ofReal hw).congr fun j => (hGintegral j).symm
  have hcompare (j : ℕ) : (∫⁻ z, F j z ∂μA) ≤ ∫⁻ z, G j z ∂μA := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem A.isOpen.measurableSet] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (weighted_smoothDensity_le_cutoff
        (((hf j).1.contDiffAt (A.isOpen.mem_nhds hz)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((hf j).2.2 z hz) b) (hφ0 z))
  have hFlimit : ∀ᵐ z ∂μA,
      Tendsto (fun j => F j z) atTop (𝓝 (ENNReal.ofReal (φ z * (w z * d z)))) := by
    filter_upwards [(ae_restrict_iff' A.isOpen.measurableSet).2 hac,
      ae_restrict_mem A.isOpen.measurableSet] with z hz hzA
    have hgeo (j : ℕ) : actualTopPowerDensity (smoothDDC (f j) z) = smoothDensity (f j) z :=
      actualTopPowerDensity_smoothDDC
        (((hf j).1.contDiffAt (A.isOpen.mem_nhds hzA)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    have hd : Tendsto (fun j => smoothDensity (f j) z) atTop (𝓝 (d z)) :=
      hz.2.2.2.congr hgeo
    have ht : Tendsto (fun j => SmoothMax.trans (f j z-b)^(m+1)) atTop (𝓝 (w z)) :=
      ((SmoothMax.continuous_trans.tendsto _).comp
        (hz.1.sub tendsto_const_nhds)).pow _
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (ht.mul hd))
  have hFatou : (∫⁻ z, ENNReal.ofReal (φ z * (w z*d z)) ∂μA) ≤
      ENNReal.ofReal (∫ z, φ z ∂canonicalBedfordTaylorMeasure U q hq) := by
    calc
      _ = ∫⁻ z, liminf (fun j => F j z) atTop ∂μA :=
        lintegral_congr_ae (hFlimit.mono fun z hz => hz.liminf_eq.symm)
      _ ≤ liminf (fun j => ∫⁻ z, F j z ∂μA) atTop := lintegral_liminf_le' hFmeas
      _ ≤ liminf (fun j => ∫⁻ z, G j z ∂μA) atTop :=
        liminf_le_liminf (Eventually.of_forall hcompare)
      _ = _ := hGi.liminf_eq
  have hsupp : Function.support (fun z => ENNReal.ofReal (φ z*(w z*d z))) ⊆ A := by
    intro z hz
    by_contra hzA
    have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hzφ => hzA (hKA hzφ)
    simp [hφz] at hz
  have hm : AEMeasurable (fun z => ENNReal.ofReal (w z*d z)) (volume.restrict U) :=
    ((SmoothMax.continuous_trans.measurable.comp_aemeasurable
      (hL.aestronglyMeasurable.aemeasurable.sub_const b)).pow_const (m+1)).mul
      (measurable_acTopDensity hT).aemeasurable |>.ennreal_ofReal
  have hleft : (∫⁻ z, ENNReal.ofReal (φ z) ∂(volume.withDensity
      (fun z => ENNReal.ofReal (w z*d z))).restrict U) =
      ∫⁻ z, ENNReal.ofReal (φ z*(w z*d z)) ∂μA := by
    rw [restrict_withDensity U.isOpen.measurableSet,
      lintegral_withDensity_eq_lintegral_mul₀ hm hφ.measurable.ennreal_ofReal.aemeasurable]
    calc
      _ = ∫⁻ z in U, ENNReal.ofReal (φ z*(w z*d z)) ∂volume := by
        apply setLIntegral_congr_fun U.isOpen.measurableSet
        intro z _
        change ENNReal.ofReal (w z*d z) * ENNReal.ofReal (φ z) =
          ENNReal.ofReal (φ z*(w z*d z))
        rw [mul_comm, ← ENNReal.ofReal_mul (hφ0 z)]
      _ = _ := (setLIntegral_eq_of_support_subset (hsupp.trans hAU)).trans
        (setLIntegral_eq_of_support_subset hsupp).symm
  exact hleft.le.trans hFatou

private theorem finite_on_compacts_of_weighted
    (μ ν : Measure (ComplexModel (m+1)))
    (hw : ∀ {φ : ComplexModel (m+1) → ℝ}, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) →
      (∫⁻ z, ENNReal.ofReal (φ z) ∂μ) ≤ ENNReal.ofReal (∫ z, φ z ∂ν))
    {K : Set (ComplexModel (m+1))} (hK : IsCompact K) (hKU : K ⊆ U) : μ K < ⊤ := by
  obtain ⟨χ,hχ0,hχK⟩ := exists_nonneg_testFunction_one_le_on_compact hK hKU
  have hind : K.indicator (1 : ComplexModel (m+1) → ℝ≥0∞) ≤ fun z => ENNReal.ofReal (χ z) := by
    intro z
    by_cases hz : z ∈ K
    · simpa only [indicator_of_mem hz,Pi.one_apply,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (hχK z hz)
    · simp only [indicator_of_notMem hz]; exact bot_le
  calc
    μ K = ∫⁻ z, K.indicator (1 : ComplexModel (m+1) → ℝ≥0∞) z ∂μ :=
      (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (χ z) ∂μ := lintegral_mono hind
    _ ≤ ENNReal.ofReal (∫ z, χ z ∂ν) := hw χ.continuous χ.hasCompactSupport χ.tsupport_subset hχ0
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The SAME original raw current is positive internally, and ALL weighted
AC measures are dominated on ANY measurable set by genuine convex-cutoff BT. -/
theorem weighted_ac_measure_le_canonicalBedfordTaylorMeasure
    {u : ComplexModel (m+1) → EReal} (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥)
    (hL : LocallyIntegrableOn (fun z => (u z).toReal) U volume) :
    let D := regularDistribution volume (fun z => (u z).toReal) hL
    ∃ hT : IsPositive (ddc (scalarTopCurrent D)), ∀ b : ℝ,
      (volume.withDensity (fun z => ENNReal.ofReal (SmoothMax.trans ((u z).toReal-b)^(m+1) *
        actualTopPowerDensity (acForm hT z)))).restrict U ≤ canonicalBedfordTaylorMeasure U
        (fun z => b+SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal-b))
        (isLocallyBoundedPshOn_convexCutoff U hu b) := by
  classical
  have hT : IsPositive (ddc (scalarTopCurrent (regularDistribution volume (fun z => (u z).toReal) hL))) :=
    isPositive_ddc_scalarTopCurrent (hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable hL hfin)
  refine ⟨hT,fun b => ?_⟩
  let μ := (volume.withDensity (fun z => ENNReal.ofReal (SmoothMax.trans ((u z).toReal-b)^(m+1) *
    actualTopPowerDensity (acForm hT z)))).restrict U
  let q := fun z => b+SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal-b)
  let hq := isLocallyBoundedPshOn_convexCutoff U hu b
  let ν := canonicalBedfordTaylorMeasure U q hq
  have hw : ∀ {φ : ComplexModel (m+1) → ℝ}, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) →
      (∫⁻ z, ENNReal.ofReal (φ z) ∂μ) ≤ ENNReal.ofReal (∫ z, φ z ∂ν) :=
    fun hφ hφc hφU hφ0 => weighted_fatou hu hfin hL hT b hφ hφc hφU hφ0
  have hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤ :=
    fun _ hK hKU => finite_on_compacts_of_weighted μ ν hw hK hKU
  have hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤ :=
    fun _ hK hKU => canonicalBedfordTaylorMeasure_finiteOnCompacts hq hK hKU
  have hreal : ∀ φ : ComplexModel (m+1) → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ z, 0 ≤ φ z) → ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν := by
    intro φ hφ hφc hφU hφ0
    have hbound := hw hφ hφc hφU hφ0
    have hint : Integrable φ μ := (lintegral_ofReal_ne_top_iff_integrable hφ.aestronglyMeasurable
      (ae_of_all μ hφ0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all μ hφ0)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hφ0)).mp hbound
  have hcompact : ∀ {K : Set (ComplexModel (m+1))}, IsCompact K → K ⊆ U → μ K ≤ ν K :=
    fun hK hKU => BedfordTaylor.measure_le_of_testFunction_integral_le hμf hνf hreal hK hKU
  have : SigmaFinite μ := by dsimp only [μ]; infer_instance
  have : μ.InnerRegular := inferInstance
  apply Measure.le_iff.mpr
  intro B hB
  have hμB : μ B = μ (B ∩ (U : Set (ComplexModel (m+1)))) := by
    change (volume.withDensity _).restrict U B =
      (volume.withDensity _).restrict U (B ∩ (U : Set (ComplexModel (m+1))))
    rw [Measure.restrict_apply hB,Measure.restrict_apply (hB.inter U.isOpen.measurableSet)]
    simp only [inter_assoc,inter_self]
  rw [hμB,(hB.inter U.isOpen.measurableSet).measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_
  exact (hcompact hK (hKB.trans inter_subset_right)).trans (measure_mono (hKB.trans inter_subset_left))

end SGPT.Foundations.Analysis.Pending.RawPshWeightedACBTDomination
