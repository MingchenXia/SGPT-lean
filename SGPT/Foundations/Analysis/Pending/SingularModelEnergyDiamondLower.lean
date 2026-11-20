import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondUpper

set_option autoImplicit false

/-!
# Actual lower rooftop-path estimate for singular same-type potentials

Xia SGPT PDF0137, Corollary 3.1.7. Actual genuine rooftop contact support,
actual contact measure comparison, and genuinely integrable canonical
differences control the lower path's energy increment. Common poles are
handled pointwise; no bounded endpoint or target diamond premise is used.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondLower

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeEnergyIntegrability
  SingularModelEnergyDiamondPaths SingularModelEnergyDiamondUpper
  SingularModelEnergyCocycle GlobalNonPluripolar ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Real values of the genuine extended affine path have the affine formula,
including the shared pole where all real values vanish. -/
theorem toReal_path {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
    (path u v t x).toReal = (1 - t) * (u x).toReal + t * (v x).toReal := by
  have hf := relativeEInfinity_path hu hv ht
  by_cases hub : u x = ⊥
  · have hφb := (sameSingularityTypeOn_eq_bot_iff hu.2 (mem_univ x)).mp hub
    have hvb := (sameSingularityTypeOn_eq_bot_iff hv.2 (mem_univ x)).mpr hφb
    have hfb := (sameSingularityTypeOn_eq_bot_iff hf.2 (mem_univ x)).mpr hφb
    simp [hub, hvb, hfb]
  · have hvb : v x ≠ ⊥ := fun h =>
      hub ((sameSingularityTypeOn_eq_bot_iff (hu.2.trans hv.2.symm) (mem_univ x)).mpr h)
    simp only [path, convexComb]
    rw [← EReal.coe_toReal (hu.1.1.quasiPlurisubharmonic.ne_top x) hub,
      ← EReal.coe_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x) hvb,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp only [EReal.toReal_coe]
    ring

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- The actual lower path's energy increment is bounded by the actual
positive canonical gap on the affine path, for singular same-type endpoints. -/
theorem energyOf_lowerPath_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : RelativeEInfinity θ φ u)
    (hv : RelativeEInfinity θ φ v) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    RelativeEnergyDiamond.energyOf θ φ hφ (lowerPath θ u v t) -
      RelativeEnergyDiamond.energyOf θ φ hφ (lowerPath θ u v s) ≤
        (t - s) * gap θ u v s := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hst, ht1⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.trans ht1⟩
  have hBt := relativeEInfinity_lowerPath hφ hu hv htI
  have hBs := relativeEInfinity_lowerPath hφ hu hv hsI
  have hft := relativeEInfinity_path hu hv htI
  have hfs := relativeEInfinity_path hu hv hsI
  rw [RelativeEnergyDiamond.energyOf_eq hBt.1, RelativeEnergyDiamond.energyOf_eq hBs.1]
  refine (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ
    hBt.1 hBs.1 hBt.2 hBs.2).2.trans ?_
  let h := fun x => max (canonicalERealDiffToReal (v x) (u x)) 0
  let C1 := {x | lowerPath θ u v s x = path u v s x}
  have hC1m : MeasurableSet C1 :=
    measurableSet_eq_fun (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hBs.1.1)
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hfs.1.1)
  let μB := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => lowerPath θ u v s)
    (fun _ => hBs.1.1)
  let μf := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => path u v s)
    (fun _ => hfs.1.1)
  let : IsFiniteMeasure μB := globalMixedMeasure_isFiniteMeasure omega (fun _ => hBs.1.1)
  let : IsFiniteMeasure μf := globalMixedMeasure_isFiniteMeasure omega (fun _ => hfs.1.1)
  have hN : μB {x | lowerPath θ u v s x ≠ path u v s x ∧ lowerPath θ u v s x ≠ v x} = 0 :=
    RooftopContactGeneral.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general
      omega θ hfs.1 hv.1 hBs.1
  have hobs := RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hft.1 hv.1
  have hobs' := RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hfs.1 hv.1
  have hcontact : ∀ᵐ x ∂μB, lowerPath θ u v s x ≠ path u v s x →
      lowerPath θ u v s x = v x := by
    rw [ae_iff]
    convert hN using 2
    ext x
    simp only [mem_ofPred_eq, Classical.not_imp]
  have hae : ∀ᵐ x ∂μB,
      canonicalERealDiffToReal (lowerPath θ u v t x) (lowerPath θ u v s x) ≤
        (t - s) * C1.indicator h x := by
    filter_upwards [hcontact] with x hx
    by_cases hub : u x = ⊥
    · have hφb := (sameSingularityTypeOn_eq_bot_iff hu.2 (mem_univ x)).mp hub
      have hvb := (sameSingularityTypeOn_eq_bot_iff hv.2 (mem_univ x)).mpr hφb
      have hBtb := (sameSingularityTypeOn_eq_bot_iff hBt.2 (mem_univ x)).mpr hφb
      have hBsb := (sameSingularityTypeOn_eq_bot_iff hBs.2 (mem_univ x)).mpr hφb
      have hz : h x = 0 := by simp [h, hvb, hub]
      rw [hBtb, hBsb, canonicalERealDiffToReal_bot_bot]
      by_cases hc : x ∈ C1
      · simp [hc, hz]
      · simp [hc]
    · have hvb : v x ≠ ⊥ := fun h =>
        hub ((sameSingularityTypeOn_eq_bot_iff (hu.2.trans hv.2.symm) (mem_univ x)).mpr h)
      have hBtb : lowerPath θ u v t x ≠ ⊥ := fun h =>
        hub ((sameSingularityTypeOn_eq_bot_iff (hBt.2.trans hu.2.symm) (mem_univ x)).mp h)
      have h1 : (lowerPath θ u v t x).toReal ≤ (path u v t x).toReal :=
        EReal.toReal_le_toReal (hobs.1 x) hBtb (hft.1.1.quasiPlurisubharmonic.ne_top x)
      have h2 : (lowerPath θ u v t x).toReal ≤ (v x).toReal :=
        EReal.toReal_le_toReal (hobs.2 x) hBtb (hv.1.1.quasiPlurisubharmonic.ne_top x)
      rw [canonicalDiff_eq_sub_toReal (hBt.1.1.quasiPlurisubharmonic.ne_top x)
        (hBs.1.1.quasiPlurisubharmonic.ne_top x)
        (sameSingularityTypeOn_eq_bot_iff (hBt.2.trans hBs.2.symm) (mem_univ x))]
      rw [toReal_path hu hv htI] at h1
      by_cases hc : lowerPath θ u v s x = path u v s x
      · rw [indicator_of_mem (show x ∈ C1 from hc)]
        have h3 : (lowerPath θ u v s x).toReal =
            (1 - s) * (u x).toReal + s * (v x).toReal := by
          rw [hc, toReal_path hu hv hsI]
        dsimp only [h]
        rw [canonicalDiff_eq_sub_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x)
          (hu.1.1.quasiPlurisubharmonic.ne_top x)
          (sameSingularityTypeOn_eq_bot_iff (hv.2.trans hu.2.symm) (mem_univ x))]
        rcases le_total (u x).toReal (v x).toReal with huv | huv
        · rw [max_eq_left (sub_nonneg.mpr huv)]
          nlinarith
        · rw [max_eq_right (sub_nonpos.mpr huv)]
          nlinarith
      · rw [indicator_of_notMem (show x ∉ C1 from hc), mul_zero]
        have h3 : (lowerPath θ u v s x).toReal = (v x).toReal := by rw [hx hc]
        linarith
  have hBint := integrable_canonicalDiff_globalMixedMeasure omega hBt.1.1 hBs.1.1
    (hBt.2.trans hBs.2.symm) (fun _ => hBs.1.1)
  have hIint : Integrable (fun x => (t - s) * C1.indicator h x) μB :=
    ((integrable_positivePart_canonicalDiff omega hu hv
      (fun _ => hBs.1.1)).indicator hC1m).const_mul (t - s)
  refine (integral_mono_ae hBint hIint hae).trans ?_
  rw [integral_const_mul, integral_indicator hC1m]
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hst)
  have hle : μB.restrict C1 ≤ μf.restrict C1 := by
    refine Measure.le_iff.2 fun E hE => ?_
    rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
    exact MaxMassDecomposition.contact_measure_le omega hBs.1 hfs.1 hobs'.1 hE
  have hnn : ∀ μ : Measure M, 0 ≤ᵐ[μ] h := fun _ => Eventually.of_forall fun x => le_max_right _ _
  have hintf : Integrable h μf := integrable_positivePart_canonicalDiff omega hu hv (fun _ => hfs.1.1)
  calc
    ∫ x in C1, h x ∂μB ≤ ∫ x in C1, h x ∂μf :=
      integral_mono_measure hle (hnn _) hintf.integrableOn
    _ ≤ ∫ x, h x ∂μf := setIntegral_le_integral hintf (hnn _)
    _ = gap θ u v s := by rw [gap, RelativeEnergyDiamond.measureOf_eq hfs.1.1]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondLower
