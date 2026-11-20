import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceTestCurvePositiveMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Lattice

/-! # Actual test-curve mass continuity

The original spatial mass is continuous at each interior parameter and
at negative infinity. Interior continuity uses genuine positive mixed
products and the original concavity directly; general mass log-concavity
remains a separate nonsmooth mixed-mass inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

private theorem mass_local_bounds {k : ℕ} {m : ℝ → ℝ} {a : ℝ}
    (hm : Antitone m)
    (hchord : ∀ {p q t : ℝ}, p < a → q < a → 0 < t → t < 1 →
      t ^ k * m p ≤ m (t * p + (1 - t) * q))
    {r b s : ℝ} (hrb : r < b) (hba : b < a) (hsb : s < b) :
    min (m r) (((b - s) / (b - r)) ^ k * m r) ≤ m s ∧
      m s ≤ max (m r) (((b - s) / (b - r)) ^ k * m r) := by
  rcases lt_trichotomy s r with hsr | hsr | hrs
  · let t : ℝ := (b - r) / (b - s)
    have ht0 : 0 < t := div_pos (sub_pos.mpr hrb) (sub_pos.mpr hsb)
    have ht1 : t < 1 := (div_lt_one (sub_pos.mpr hsb)).mpr (by linarith)
    have hpar : t * s + (1 - t) * b = r := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hsb), ne_of_gt (sub_pos.mpr hrb)]
      ring
    have hc := hchord (hsb.trans hba) hba ht0 ht1
    rw [hpar] at hc
    have hprod : (b - s) / (b - r) * t = 1 := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hsb), ne_of_gt (sub_pos.mpr hrb)]
    have hpow : ((b - s) / (b - r)) ^ k * t ^ k = 1 := by
      rw [← mul_pow, hprod, one_pow]
    have hupper := mul_le_mul_of_nonneg_left hc
      (pow_nonneg (div_nonneg (sub_nonneg.mpr hsb.le) (sub_nonneg.mpr hrb.le)) k)
    simp only [← mul_assoc, hpow, one_mul] at hupper
    exact ⟨(min_le_left _ _).trans (hm hsr.le), hupper.trans (le_max_right _ _)⟩
  · subst s
    simp only [div_self (sub_ne_zero.mpr hrb.ne'), one_pow, one_mul, min_self, max_self,
      le_refl, and_self]
  · let t : ℝ := (b - s) / (b - r)
    have ht0 : 0 < t := div_pos (sub_pos.mpr hsb) (sub_pos.mpr hrb)
    have ht1 : t < 1 := (div_lt_one (sub_pos.mpr hrb)).mpr (by linarith)
    have hpar : t * r + (1 - t) * b = s := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hsb), ne_of_gt (sub_pos.mpr hrb)]
      ring
    have hc := hchord (hrb.trans hba) hba ht0 ht1
    rw [hpar] at hc
    exact ⟨(min_le_right _ _).trans hc, (hm hrs.le).trans (le_max_left _ _)⟩

private theorem mass_continuousAt {k : ℕ} {m : ℝ → ℝ} {a r : ℝ}
    (hm : Antitone m)
    (hchord : ∀ {p q t : ℝ}, p < a → q < a → 0 < t → t < 1 →
      t ^ k * m p ≤ m (t * p + (1 - t) * q)) (hr : r < a) :
    ContinuousAt m r := by
  let b := (r + a) / 2
  have hrb : r < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hK : ContinuousAt (fun s : ℝ ↦ ((b - s) / (b - r)) ^ k * m r) r := by
    fun_prop
  have hKeq : ((b - r) / (b - r)) ^ k * m r = m r := by
    rw [div_self (sub_ne_zero.mpr hrb.ne'), one_pow, one_mul]
  have hlo : Tendsto (fun s : ℝ ↦ min (m r) (((b - s) / (b - r)) ^ k * m r))
      (𝓝 r) (𝓝 (m r)) := by
    simpa only [hKeq, min_self] using ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ m r) r).inf hK).tendsto
  have hhi : Tendsto (fun s : ℝ ↦ max (m r) (((b - s) / (b - r)) ^ k * m r))
      (𝓝 r) (𝓝 (m r)) := by
    simpa only [hKeq, max_self] using ((continuousAt_const : ContinuousAt (fun _ : ℝ ↦ m r) r).sup hK).tendsto
  have he := (eventually_lt_nhds hrb).mono fun s hsb ↦ mass_local_bounds hm hchord hrb hba hsb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (he.mono fun _ h ↦ h.1) (he.mono fun _ h ↦ h.2)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A quantitative lower bound for the actual original real masses,
produced from genuine positive mixed products and source concavity. -/
theorem sourceTestCurveRealMassAt_chord_lower_bound (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {a b t : ℝ} (ha : a < Γ.max) (hb : b < Γ.max)
    (ht0 : 0 < t) (ht1 : t < 1) :
    t ^ n * sourceTestCurveRealMassAt omega Γ a ≤
      sourceTestCurveRealMassAt omega Γ (t * a + (1 - t) * b) := by
  have hs : t * a + (1 - t) * b < Γ.max := by
    nlinarith [mul_pos ht0 (sub_pos.mpr ha),
      mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hb)]
  let w := convexComb t (Γ.potential ⟨a, ha⟩) (Γ.potential ⟨b, hb⟩)
  have hw := (isThetaPSH_iff_nativeThetaPotential θ w).mpr
    (isThetaPshPotential_convexComb (Γ.native_thetaPSH ⟨a, ha⟩)
      (Γ.native_thetaPSH ⟨b, hb⟩) ht0 ht1)
  have hmono := sourcePotentialNonPluripolarMass_mono omega hw (Γ.thetaPSH ⟨_, hs⟩)
    (MoreSingularOn.of_le fun x _ ↦
      Γ.toSourceTestCurvePredata.convexComb_le ⟨a, ha⟩ ⟨b, hb⟩ ht0 ht1 x)
  have hscale := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
    (θ := atlasClosedFormToNative θ)
    (Γ.native_thetaPSH ⟨a, ha⟩) (Γ.native_thetaPSH ⟨b, hb⟩) ht0 ht1 univ
  change ENNReal.ofReal (t ^ n) *
      sourcePotentialNonPluripolarMeasure θ (Γ.potential ⟨a, ha⟩) (Γ.thetaPSH ⟨a, ha⟩) univ ≤
    sourcePotentialNonPluripolarMeasure θ w hw univ at hscale
  have hreal := ENNReal.toReal_mono (Γ.mass_lt_top omega ⟨_, hs⟩).ne (hscale.trans hmono)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht0.le n)] at hreal
  simpa only [sourceTestCurveRealMassAt_of_lt omega Γ ha,
    sourceTestCurveRealMassAt_of_lt omega Γ hs] using hreal

/-- The actual real mass function is continuous at every original interior
parameter, with no nonsmooth mixed-mass inequality assumed. -/
theorem sourceTestCurveRealMassAt_continuousAt (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {r : ℝ} (hr : r < Γ.max) :
    ContinuousAt (sourceTestCurveRealMassAt omega Γ) r :=
  mass_continuousAt (sourceTestCurveRealMassAt_antitone omega Γ)
    (sourceTestCurveRealMassAt_chord_lower_bound omega Γ) hr

/-- Whole original directed mass continuity at negative infinity. -/
theorem SourceTestCurvePredata.mass_tendsto_atBot (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) :
    Tendsto (fun r : Iio Γ.max ↦
      sourcePotentialNonPluripolarMeasure θ (Γ.potential r) (Γ.thetaPSH r) univ)
      atBot (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ)
        Γ.limit_thetaPSH univ)) := by
  change Tendsto (fun r : OrderDual (Iio Γ.max) ↦
    sourcePotentialNonPluripolarMeasure θ (Γ.potential r) (Γ.thetaPSH r) univ)
    atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ)
      Γ.limit_thetaPSH univ))
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hm (_j : Fin n) : Monotone
      (fun r : OrderDual (Iio Γ.max) ↦ Γ.potential r) := by
    intro a b hab x
    exact Γ.antitone x hab
  have hlim := sourceIncreasingMixed_mass_tendsto omega
    (I := OrderDual (Iio Γ.max))
    (θ := fun _ : Fin n ↦ θ)
    (u := fun r : OrderDual (Iio Γ.max) ↦ fun _ : Fin n ↦ Γ.potential r)
    (fun r _ ↦ Γ.thetaPSH r) hm (C := fun _ ↦ 0)
    (fun _ r x ↦ by simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero r x)
  have hU : uscRegularization (⨆ r : OrderDual (Iio Γ.max), Γ.potential r) =
      sourceTestCurveLimit Γ := by
    apply congrArg uscRegularization
    funext x
    exact iSup_apply
  simpa only [hU, sourceMixedNonPluripolarMass, sourceMixedNonPluripolarMeasure,
    sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMeasure] using hlim

private theorem testCurveLimit_mass_ne_top (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) :
    sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ)
      Γ.limit_thetaPSH univ ≠ ⊤ := by
  have hfin := sourceMixedNonPluripolarMass_lt_top omega (fun _ : Fin n ↦ θ)
    (fun _ ↦ sourceTestCurveLimit Γ) (fun _ ↦ Γ.limit_thetaPSH)
  simpa only [sourceMixedNonPluripolarMass_diagonal] using hfin.ne

/-- Actual finiteness permits real readback of the whole original directed
mass limit; it is established before the logarithm is applied. -/
theorem sourceTestCurveRealMassAt_tendsto_atBot (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    Tendsto (fun r : Iio Γ.max ↦ sourceTestCurveRealMassAt omega Γ r.val) atBot
      (𝓝 (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) Γ.limit_thetaPSH univ).toReal) := by
  have hreal := (ENNReal.continuousAt_toReal
    (testCurveLimit_mass_ne_top omega Γ.toSourceTestCurvePredata)).tendsto.comp
      (Γ.toSourceTestCurvePredata.mass_tendsto_atBot omega)
  have hfun : (fun r : Iio Γ.max ↦ sourceTestCurveRealMassAt omega Γ r.val) =
      fun r : Iio Γ.max ↦
        (sourcePotentialNonPluripolarMeasure θ (Γ.potential r) (Γ.thetaPSH r) univ).toReal := by
    funext r
    exact sourceTestCurveRealMassAt_of_lt omega Γ r.property
  rw [hfun]
  exact hreal

/-- The original positive interior mass makes its actual real logarithm
continuous; no positive-mass premise is added to the original curve. -/
theorem sourceTestCurveLogMassAt_continuousAt (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {r : ℝ} (hr : r < Γ.max) :
    ContinuousAt (fun s ↦ Real.log (sourceTestCurveRealMassAt omega Γ s)) r := by
  have hp : 0 < sourceTestCurveRealMassAt omega Γ r := by
    rw [sourceTestCurveRealMassAt_of_lt omega Γ hr]
    exact ENNReal.toReal_pos (Γ.mass_positive omega ⟨r, hr⟩).ne'
      (Γ.mass_lt_top omega ⟨r, hr⟩).ne
  exact (Real.continuousAt_log hp.ne').comp
    (sourceTestCurveRealMassAt_continuousAt omega Γ hr)

/-- Continuity of the original logarithmic mass at negative infinity,
through the entire original open parameter interval. -/
theorem sourceTestCurveLogMassAt_tendsto_atBot (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    Tendsto (fun r : Iio Γ.max ↦ Real.log (sourceTestCurveRealMassAt omega Γ r.val)) atBot
      (𝓝 (Real.log (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) Γ.limit_thetaPSH univ).toReal)) := by
  have hp : 0 < (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveLimit Γ.toSourceTestCurvePredata) Γ.limit_thetaPSH univ).toReal :=
    ENNReal.toReal_pos Γ.positiveLimitMass.ne'
      (testCurveLimit_mass_ne_top omega Γ.toSourceTestCurvePredata)
  exact (Real.continuousAt_log hp.ne').tendsto.comp
    (sourceTestCurveRealMassAt_tendsto_atBot omega Γ)

end SGPT.PSH.VariableComplexAtlas
