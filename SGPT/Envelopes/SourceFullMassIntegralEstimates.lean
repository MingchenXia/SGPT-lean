import SGPT.Envelopes.SourceMixedComparison
import Mathlib.MeasureTheory.Integral.Layercake

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling

/-- Finite positive scaling for an extended nonnegative integral needs no integrability. -/
theorem sourceLIntegral_two_mul_half {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = 2 * ∫⁻ x, ENNReal.ofReal (f x / 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  apply lintegral_congr
  intro x
  calc ENNReal.ofReal (f x) = ENNReal.ofReal (2 * (f x / 2)) := congrArg ENNReal.ofReal (by ring)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- Actual layer-cake transfer of a two-term distribution bound, allowing infinite integrals. -/
theorem sourceLIntegral_le_two_add_of_tail {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f g : X → ℝ} {h : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ y, 0 ≤ h y)
    (htail : ∀ t : ℝ, 0 < t → μ {x | 2 * t < f x} ≤ μ {x | t < g x} + ν {y | t < h y}) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      2 * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) + 2 * ∫⁻ y, ENNReal.ofReal (h y) ∂ν := by
  have hgm : Measurable (fun t : ℝ => μ {x | t < g x}) :=
    Antitone.measurable (fun a b hab => measure_mono fun _ hx => lt_of_le_of_lt hab hx)
  have hhalf : (∫⁻ x, ENNReal.ofReal (f x / 2) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ) + ∫⁻ y, ENNReal.ofReal (h y) ∂ν := by
    rw [lintegral_eq_lintegral_meas_lt μ
      (Eventually.of_forall fun x => div_nonneg (hfn x) (by norm_num)) (hf.div_const 2).aemeasurable]
    calc
      (∫⁻ t in Ioi 0, μ {x | t < f x / 2}) ≤
          (∫⁻ t in Ioi 0, μ {x | t < g x} + ν {y | t < h y}) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        simpa only [lt_div_iff₀ (show (0 : ℝ) < 2 by norm_num), mul_comm t 2] using htail t ht
      _ = (∫⁻ t in Ioi 0, μ {x | t < g x}) + ∫⁻ t in Ioi 0, ν {y | t < h y} :=
        lintegral_add_left hgm _
      _ = _ := by
        rw [← lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hgn) hg.aemeasurable,
          ← lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hhn) hh.aemeasurable]
  calc (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = 2 * ∫⁻ x, ENNReal.ofReal (f x / 2) ∂μ :=
      sourceLIntegral_two_mul_half μ f
    _ ≤ 2 * ((∫⁻ x, ENNReal.ofReal (g x) ∂μ) + ∫⁻ y, ENNReal.ofReal (h y) ∂ν) :=
      mul_le_mul_right hhalf 2
    _ = _ := mul_add _ _ _

/-- The one-term extended distribution transfer with an actual nonnegative measure coefficient. -/
theorem sourceLIntegral_le_two_mul_of_tail {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → ℝ} {h : Y → ℝ} (C : ℝ≥0∞)
    (hf : Measurable f) (hh : Measurable h) (hfn : ∀ x, 0 ≤ f x) (hhn : ∀ y, 0 ≤ h y)
    (htail : ∀ t : ℝ, 0 < t → μ {x | 2 * t < f x} ≤ C * ν {y | t < h y}) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ (2 * C) * ∫⁻ y, ENNReal.ofReal (h y) ∂ν := by
  have h := sourceLIntegral_le_two_add_of_tail μ (C • ν) hf measurable_const hh
    hfn (fun _ => le_rfl) hhn (fun t ht => by
      have hz : {x : X | t < (0 : ℝ)} = ∅ := by ext x; simp [not_lt.mpr ht.le]
      simpa only [hz,
        measure_empty, zero_add, Measure.smul_apply, smul_eq_mul] using htail t ht)
  simpa only [ENNReal.ofReal_zero, lintegral_zero, mul_zero, zero_add,
    lintegral_smul_measure, smul_eq_mul, mul_assoc] using h

/-- The real nonnegative canonical gap gauge; its integral interpretation is proved below. -/
def sourceRealGap {X : Type*} (a b : X → EReal) (x : X) : ℝ :=
  (canonicalERealAbsDiff (a x) (b x)).toReal

/-- This real gauge is nonnegative at every point, including canonical pole values. -/
theorem sourceRealGap_nonneg {X : Type*} (a b : X → EReal) (x : X) :
    0 ≤ sourceRealGap a b x := ENNReal.toReal_nonneg

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- An arbitrary genuine original potential is finite almost everywhere for every actual diagonal. -/
theorem sourcePotentialNonPluripolarMeasure_ae_ne_bot {w a : M → EReal}
    (hw : (ofFixedModel n M).IsThetaPSH θ w)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (ha : (ofFixedModel n M).IsThetaPSH σ a) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ w hw, a x ≠ ⊥ := by
  apply ae_iff.mpr
  simpa only [not_not, ← sourceMixedNonPluripolarMeasure_diagonal] using
    sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hw) ha

/-- The canonical ENNReal gap is actually finite almost everywhere before its real readback. -/
theorem sourceCanonicalGap_finite_ae {a b w : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (hw : (ofFixedModel n M).IsThetaPSH θ w) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ w hw,
      canonicalERealAbsDiff (a x) (b x) ≠ ⊤ := by
  filter_upwards [sourcePotentialNonPluripolarMeasure_ae_ne_bot hw ha,
    sourcePotentialNonPluripolarMeasure_ae_ne_bot hw hb] with x hab hbb
  rw [← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ a).mp ha).1.quasiPlurisubharmonic.ne_top x) hab,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ b).mp hb).1.quasiPlurisubharmonic.ne_top x) hbb,
    canonicalERealAbsDiff_coe_coe]
  exact ENNReal.ofReal_ne_top

omit [CompactSpace M] in
/-- Genuine original theta-PSH functions give a measurable actual canonical real gap. -/
theorem sourceRealGap_measurable {a b : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b) :
    Measurable (sourceRealGap a b) := by
  have ham := ((isThetaPSH_iff_nativeThetaPotential θ a).mp
    ha).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hbm := ((isThetaPSH_iff_nativeThetaPotential θ b).mp
    hb).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  exact (ham.canonicalERealAbsDiff hbm).ennreal_toReal

/-- The actual original nonnegative gap integral on the unchanged genuine diagonal domain. -/
def sourceDiagonalGapIntegral (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (a b w : M → EReal) (hw : (ofFixedModel n M).IsThetaPSH θ w) : ℝ≥0∞ :=
  ∫⁻ x, canonicalERealAbsDiff (a x) (b x) ∂sourcePotentialNonPluripolarMeasure θ w hw

/-- Actual pole-null finite readback identifies the entire nonnegative integral, even when it is infinite. -/
theorem sourceDiagonalGapIntegral_eq_realGap {a b w : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (hw : (ofFixedModel n M).IsThetaPSH θ w) :
    sourceDiagonalGapIntegral θ a b w hw =
      ∫⁻ x, ENNReal.ofReal (sourceRealGap a b x) ∂sourcePotentialNonPluripolarMeasure θ w hw := by
  apply lintegral_congr_ae
  filter_upwards [sourceCanonicalGap_finite_ae ha hb hw] with x hx
  exact (ENNReal.ofReal_toReal hx).symm

/-- The ordered actual gap's real superlevels are exactly the original strict comparison domain modulo poles. -/
theorem sourceRealGap_tail_measure {a b w : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (hw : (ofFixedModel n M).IsThetaPSH θ w) (hba : b ≤ a) (t : ℝ) :
    sourcePotentialNonPluripolarMeasure θ w hw {x | t < sourceRealGap a b x} =
      sourcePotentialNonPluripolarMeasure θ w hw {x | b x + (t : EReal) < a x} := by
  apply measure_congr
  filter_upwards [sourcePotentialNonPluripolarMeasure_ae_ne_bot hw ha,
    sourcePotentialNonPluripolarMeasure_ae_ne_bot hw hb] with x hab hbb
  have hat := ((isThetaPSH_iff_nativeThetaPotential θ a).mp ha).1.quasiPlurisubharmonic.ne_top x
  have hbt := ((isThetaPSH_iff_nativeThetaPotential θ b).mp hb).1.quasiPlurisubharmonic.ne_top x
  have horder := EReal.toReal_le_toReal (hba x) hbb hat
  apply propext
  change (t < sourceRealGap a b x) ↔ b x + (t : EReal) < a x
  unfold sourceRealGap
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hbt hbb]
  simp only [canonicalERealAbsDiff_coe_coe, abs_of_nonneg (sub_nonneg.mpr horder),
    ENNReal.toReal_ofReal (sub_nonneg.mpr horder), ← EReal.coe_add, EReal.coe_lt_coe_iff]
  constructor <;> intro h <;> linarith

omit [BorelSpace M] in
/-- The original j=0 auxiliary tuple is exactly the unchanged diagonal product. -/
theorem sourceMixedComparisonMeasure_zero
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceMixedComparisonMeasure θ ⟨0, Nat.zero_lt_succ n⟩ Fin.elim0 Fin.elim0
      (fun a => a.elim0) u hu = sourcePotentialNonPluripolarMeasure θ u hu := by
  have hforms : (fun i : Fin n => atlasClosedFormToNative
      (sourceComparisonFormTuple θ ⟨0, Nat.zero_lt_succ n⟩ Fin.elim0 i)) =
      fun _ => atlasClosedFormToNative θ := by
    funext i
    simp [sourceComparisonFormTuple, i.isLt]
  have hpots : sourceComparisonPotentialTuple ⟨0, Nat.zero_lt_succ n⟩ Fin.elim0 u =
      fun _ : Fin n => u := by
    funext i
    simp [sourceComparisonPotentialTuple, i.isLt]
  exact globalMixedMeasure_congr hforms hpots
    (fun i => ((isThetaPSH_iff_nativeThetaPotential _ _).mp
      (sourceComparisonTuple_thetaPSH (fun a => a.elim0) hu i)).1)
    (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1)

/-- Actual finite translation leaves the same original whole diagonal measure unchanged. -/
theorem sourcePotentialNonPluripolarMeasure_add_const {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ)
    (huc : (ofFixedModel n M).IsThetaPSH θ (fun x => u x + (c : EReal))) :
    sourcePotentialNonPluripolarMeasure θ (fun x => u x + (c : EReal)) huc =
      sourcePotentialNonPluripolarMeasure θ u hu :=
  DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const _
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) c
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp huc)

variable [ConnectedSpace M] {φ u v γ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- Both original full-mass diagonal comparisons are obtained from the whole actual mixed theorem. -/
theorem sourceDiagonalFullMassComparison (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    (sourcePotentialNonPluripolarMeasure θ v hv.choose {x | u x < v x} ≤
      sourcePotentialNonPluripolarMeasure θ u hu.choose {x | u x < v x}) ∧
    (sourcePotentialNonPluripolarMeasure θ v hv.choose {x | u x ≤ v x} ≤
      sourcePotentialNonPluripolarMeasure θ u hu.choose {x | u x ≤ v x}) := by
  have h := sourceMixedComparisonPrinciple ω (j := ⟨0, Nat.zero_lt_succ n⟩)
    (η := Fin.elim0) (q := Fin.elim0) (fun a => a.elim0) hu hv
  simpa only [sourceMixedComparisonMeasure_zero] using h

/-- Original full-mass comparison on the actual finite-translated strict integration domain. -/
theorem sourceDiagonalFullMass_shifted_comparison (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) (t : ℝ) :
    sourcePotentialNonPluripolarMeasure θ v hv.choose {x | u x + (t : EReal) < v x} ≤
      sourcePotentialNonPluripolarMeasure θ u hu.choose {x | u x + (t : EReal) < v x} := by
  have h := (sourceDiagonalFullMassComparison ω (sourceRelativeFullMass_add_const hu t) hv).1
  rwa [sourcePotentialNonPluripolarMeasure_add_const hu.choose t] at h

/-- The whole original independent upper-potential integral estimate on the full-mass domain. -/
theorem sourceFullMass_upper_integral_comparison (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ)
    (hγ : SourceRelativeFullMass θ φ γ hφ) (huγ : u ≤ γ) (hvγ : v ≤ γ) :
    sourceDiagonalGapIntegral θ γ u v hv.choose ≤
      2 * sourceDiagonalGapIntegral θ γ u u hu.choose +
        2 * sourceDiagonalGapIntegral θ γ v v hv.choose := by
  let μu := sourcePotentialNonPluripolarMeasure θ u hu.choose
  let μv := sourcePotentialNonPluripolarMeasure θ v hv.choose
  have htail (t : ℝ) (_ht : 0 < t) :
      μv {x | 2 * t < sourceRealGap γ u x} ≤
        μv {x | t < sourceRealGap γ v x} + μu {x | t < sourceRealGap γ u x} := by
    rw [sourceRealGap_tail_measure hγ.choose hu.choose hv.choose huγ,
      sourceRealGap_tail_measure hγ.choose hv.choose hv.choose hvγ,
      sourceRealGap_tail_measure hγ.choose hu.choose hu.choose huγ]
    have hsub : {x | u x + ((2 * t : ℝ) : EReal) < γ x} ⊆
        {x | v x + (t : EReal) < γ x} ∪ {x | u x + (t : EReal) < v x} := by
      intro x hx
      change u x + ((2 * t : ℝ) : EReal) < γ x at hx
      by_cases h1 : v x + (t : EReal) < γ x
      · exact Or.inl h1
      · apply Or.inr
        by_contra h2
        apply hx.not_ge
        calc γ x ≤ v x + (t : EReal) := not_lt.mp h1
          _ ≤ (u x + (t : EReal)) + (t : EReal) := add_le_add (not_lt.mp h2) le_rfl
          _ = u x + ((2 * t : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            have ht2 : t + t = 2 * t := by ring
            rw [ht2]
    calc μv {x | u x + ((2 * t : ℝ) : EReal) < γ x} ≤
          μv ({x | v x + (t : EReal) < γ x} ∪ {x | u x + (t : EReal) < v x}) := measure_mono hsub
      _ ≤ μv {x | v x + (t : EReal) < γ x} + μv {x | u x + (t : EReal) < v x} :=
        measure_union_le _ _
      _ ≤ μv {x | v x + (t : EReal) < γ x} + μu {x | u x + (t : EReal) < v x} :=
        add_le_add le_rfl (sourceDiagonalFullMass_shifted_comparison ω hu hv t)
      _ ≤ μv {x | v x + (t : EReal) < γ x} + μu {x | u x + (t : EReal) < γ x} :=
        add_le_add le_rfl (measure_mono fun x (hx : u x + (t : EReal) < v x) =>
          hx.trans_le (hvγ x))
  have h := sourceLIntegral_le_two_add_of_tail μv μu
    (sourceRealGap_measurable hγ.choose hu.choose)
    (sourceRealGap_measurable hγ.choose hv.choose)
    (sourceRealGap_measurable hγ.choose hu.choose)
    (sourceRealGap_nonneg γ u) (sourceRealGap_nonneg γ v) (sourceRealGap_nonneg γ u) htail
  rw [sourceDiagonalGapIntegral_eq_realGap hγ.choose hu.choose hv.choose,
    sourceDiagonalGapIntegral_eq_realGap hγ.choose hu.choose hu.choose,
    sourceDiagonalGapIntegral_eq_realGap hγ.choose hv.choose hv.choose]
  simpa only [add_comm] using h

/-- The actual unchanged midpoint of two original potentials. -/
def sourceFullMassMidpoint (v γ : M → EReal) : M → EReal :=
  ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) v γ

/-- Actual closed source convexity produces full mass of the genuine midpoint without E1. -/
theorem sourceFullMass_midpoint (ω : KahlerBackground n M)
    (hv : SourceRelativeFullMass θ φ v hφ) (hγ : SourceRelativeFullMass θ φ γ hφ) :
    SourceRelativeFullMass θ φ (sourceFullMassMidpoint v γ) hφ :=
  sourceRelativeFullMass_convexComb ω hv hγ (by norm_num) (by norm_num)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Positive midpoint order is the actual original sandwich, including poles. -/
theorem sourceFullMassMidpoint_sandwich {v γ : M → EReal} (hvγ : v ≤ γ) :
    v ≤ sourceFullMassMidpoint v γ ∧ sourceFullMassMidpoint v γ ≤ γ := by
  have hlo := ThetaPshConvexCombination.convexComb_mono
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (le_refl v) hvγ
  have hhi := ThetaPshConvexCombination.convexComb_mono
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hvγ (le_refl γ)
  rw [ThetaCapacity.convexComb_self (by norm_num) (by norm_num)] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Native actual binary expansion gives the whole midpoint domination on full mass, with no E1 premise. -/
theorem sourceFullMass_midpoint_measure_domination (ω : KahlerBackground n M)
    (hv : SourceRelativeFullMass θ φ v hφ) (hγ : SourceRelativeFullMass θ φ γ hφ) :
    sourcePotentialNonPluripolarMeasure θ v hv.choose ≤ (2 : ℝ≥0∞) ^ n •
      sourcePotentialNonPluripolarMeasure θ (sourceFullMassMidpoint v γ)
        (sourceFullMass_midpoint ω hv hγ).choose := by
  have h := SingularModelFiniteEnergyMixedGap.binaryMixedMeasure_le_pow_smul_midpoint ω
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.choose)
    ((isThetaPSH_iff_nativeThetaPotential θ γ).mp hγ.choose) (fun _ => true)
  simpa only [SingularModelFiniteEnergyMixedGap.binaryMixedMeasure, Bool.true_eq, ↓reduceIte,
    ENNReal.ofReal_pow (p := (2 : ℝ)) (by norm_num) n, ENNReal.ofReal_ofNat,
    sourcePotentialNonPluripolarMeasure, diagonalPotentialMeasure, sourceFullMassMidpoint] using h

/-- The whole original arbitrary-upper full-mass fundamental estimate, including infinite integrals. -/
theorem sourceFullMass_fundamental_integral_estimate (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ)
    (hγ : SourceRelativeFullMass θ φ γ hφ) (huv : u ≤ v) (hvγ : v ≤ γ) :
    sourceDiagonalGapIntegral θ γ v v hv.choose ≤
      (2 : ℝ≥0∞) ^ (n + 1) * sourceDiagonalGapIntegral θ γ u u hu.choose := by
  let w := sourceFullMassMidpoint v γ
  have hw := sourceFullMass_midpoint ω hv hγ
  have hwγ : w ≤ γ := (sourceFullMassMidpoint_sandwich hvγ).2
  let μu := sourcePotentialNonPluripolarMeasure θ u hu.choose
  let μv := sourcePotentialNonPluripolarMeasure θ v hv.choose
  let μw := sourcePotentialNonPluripolarMeasure θ w hw.choose
  have htail (t : ℝ) (_ht : 0 < t) : μv {x | 2 * t < sourceRealGap γ v x} ≤
      (2 : ℝ≥0∞) ^ n * μu {x | t < sourceRealGap γ u x} := by
    rw [sourceRealGap_tail_measure hγ.choose hv.choose hv.choose hvγ,
      sourceRealGap_tail_measure hγ.choose hu.choose hu.choose (huv.trans hvγ)]
    let S : Set M := {x | u x + (t : EReal) < w x}
    have hSm : MeasurableSet S := measurableSet_lt
      (((isThetaPSH_iff_nativeThetaPotential θ u).mp
        hu.choose).add_const t).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      (((isThetaPSH_iff_nativeThetaPotential θ w).mp
        hw.choose).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
    have hsub : {x | v x + ((2 * t : ℝ) : EReal) < γ x} ≤ᵐ[μv] S := by
      filter_upwards [sourcePotentialNonPluripolarMeasure_ae_ne_bot hv.choose hv.choose] with x hvb
      intro hx
      have hγb : γ x ≠ ⊥ := ne_bot_of_le_ne_bot hvb (hvγ x)
      have hvt := ((isThetaPSH_iff_nativeThetaPotential θ v).mp
        hv.choose).1.quasiPlurisubharmonic.ne_top x
      have hγt := ((isThetaPSH_iff_nativeThetaPotential θ γ).mp
        hγ.choose).1.quasiPlurisubharmonic.ne_top x
      have hmid : v x + (t : EReal) < w x := by
        change v x + (t : EReal) <
          ((1 / 2 : ℝ) : EReal) * v x + ((1 - 1 / 2 : ℝ) : EReal) * γ x
        change v x + ((2 * t : ℝ) : EReal) < γ x at hx
        rw [← EReal.coe_toReal hvt hvb, ← EReal.coe_toReal hγt hγb,
          ← EReal.coe_add, EReal.coe_lt_coe_iff] at hx
        rw [← EReal.coe_toReal hvt hvb, ← EReal.coe_toReal hγt hγb,
          ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
          ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith
      exact (add_le_add (huv x) le_rfl).trans_lt hmid
    have hdom : μv S ≤ (2 : ℝ≥0∞) ^ n * μw S := by
      have h := Measure.le_iff.mp (sourceFullMass_midpoint_measure_domination ω hv hγ) S hSm
      simpa only [Measure.smul_apply, smul_eq_mul] using h
    calc μv {x | v x + ((2 * t : ℝ) : EReal) < γ x} ≤ μv S := measure_mono_ae hsub
      _ ≤ (2 : ℝ≥0∞) ^ n * μw S := hdom
      _ ≤ (2 : ℝ≥0∞) ^ n * μu S :=
        mul_le_mul_right (sourceDiagonalFullMass_shifted_comparison ω hu hw t) _
      _ ≤ (2 : ℝ≥0∞) ^ n * μu {x | u x + (t : EReal) < γ x} :=
        mul_le_mul_right (measure_mono fun x (hx : u x + (t : EReal) < w x) =>
          hx.trans_le (hwγ x)) _
  have h := sourceLIntegral_le_two_mul_of_tail μv μu ((2 : ℝ≥0∞) ^ n)
    (sourceRealGap_measurable hγ.choose hv.choose)
    (sourceRealGap_measurable hγ.choose hu.choose)
    (sourceRealGap_nonneg γ v) (sourceRealGap_nonneg γ u) htail
  rw [sourceDiagonalGapIntegral_eq_realGap hγ.choose hv.choose hv.choose,
    sourceDiagonalGapIntegral_eq_realGap hγ.choose hu.choose hu.choose]
  simpa only [pow_succ, mul_comm (2 : ℝ≥0∞) ((2 : ℝ≥0∞) ^ n)] using h

end SGPT.PSH.VariableComplexAtlas
