import SGPT.Trace.OptimalNativeNormalBackground
import SGPT.Trace.OTResFlat
import SGPT.Trace.TwistedL2SingularRemoval

/-!
# Finite actual singular background energy

The SAME vanishing physical datum radius cancels the genuine logarithmic
pole. No local energy integrability result is an input.
Blueprint: work/sgpt-resume-20261114/bert-e2-native-energy/blueprint/bert-e2-native-energy.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNativeNormalEnergy
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Trace.OptimalNativeNormalBackground

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The literal finite energy after canceling the SAME original radius. -/
def regularBackgroundEnergy (f : X → ℂ) (k : X → ℝ) (ε ρ : ℝ)
    (F : (x : X) → L.Fiber x) (x : X) : ℝ :=
  ε ^ 2 / (ρ ^ 2 * (ε + nativeRadius f x) ^ 4) * ‖F x‖ ^ 2 * Real.exp (-k x)

theorem regularBackgroundEnergy_nonneg (f : X → ℂ) (k : X → ℝ) (ε ρ : ℝ)
    (F : (x : X) → L.Fiber x) (x : X) :
    0 ≤ regularBackgroundEnergy L f k ε ρ F x := by
  unfold regularBackgroundEnergy
  positivity

/-- Actual continuity is produced from the original metric/section/weight. -/
theorem continuous_regularBackgroundEnergy {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    {k : X → ℝ} (hk : ChartSmooth (n := n) k) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    Continuous (regularBackgroundEnergy L f k ε ρ F) := by
  have hR : Continuous (nativeRadius f) := continuous_of_chartSmooth' (chartSmooth_nativeRadius hf)
  have hN : Continuous (fun x => ‖F x‖ ^ 2) := continuous_of_chartSmooth'
    (SGPT.Trace.OTRes.chartSmooth_normSq L hL (SGPT.Trace.OTExt5.isSmoothSectionOn_of_holomorphic L hF))
  have hK : Continuous k := continuous_of_chartSmooth' hk
  have hden : ∀ x, ρ ^ 2 * (ε + nativeRadius f x) ^ 4 ≠ 0 := fun x =>
    mul_ne_zero (pow_ne_zero 2 hρ.ne')
      (pow_ne_zero 4 (add_pos_of_pos_of_nonneg hε (sq_nonneg _)).ne')
  exact ((continuous_const.div (continuous_const.mul ((continuous_const.add hR).pow 4)) hden).mul hN).mul
    (Real.continuous_exp.comp hK.neg)

/-- Exact off-pole cancellation in the original multiplier convention. -/
theorem background_energy_eq_off_zero {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    {k : X → ℝ} (hk : ChartSmooth (n := n) k) (ε ρ : ℝ)
    (F : (x : X) → L.Fiber x) {x : X} (hfx : f x ≠ 0) :
    ENNReal.ofReal (backgroundDatum L f ε ρ F x) * multiplierWeight 1 (normalWeight f k x) =
      ENNReal.ofReal (regularBackgroundEnergy L f k ε ρ F x) := by
  have hbot : normalWeight f k x ≠ ⊥ := fun h => hfx ((normalWeight_eq_bot_iff f k x).mp h)
  have htop := (normalWeight_quasiPlurisubharmonic hf hk).ne_top x
  rw [← ofReal_mul_exp_neg_toReal (backgroundDatum L f ε ρ F x) hbot htop,
    normalWeight_toReal k hfx]
  congr 1
  have hr : 0 < nativeRadius f x := sq_pos_of_pos (norm_pos_iff.mpr hfx)
  rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hr]
  unfold backgroundDatum regularBackgroundEnergy
  field_simp

/-- At true poles, the original zero-times-infinity convention gives zero;
no value of the original singular multiplier is replaced. -/
theorem background_energy_le_regular {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    {k : X → ℝ} (hk : ChartSmooth (n := n) k) (ε ρ : ℝ)
    (F : (x : X) → L.Fiber x) (x : X) :
    ENNReal.ofReal (backgroundDatum L f ε ρ F x) * multiplierWeight 1 (normalWeight f k x) ≤
      ENNReal.ofReal (regularBackgroundEnergy L f k ε ρ F x) := by
  by_cases hfx : f x = 0
  · simp only [backgroundDatum, nativeRadius, hfx, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
    exact bot_le
  · exact (background_energy_eq_off_zero L hf hk ε ρ F hfx).le

/-- The actual singular background integral is finite on every original
compact, produced from the true smooth positive volume and literal datum. -/
theorem finite_background_energy_on_compact [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    {k : X → ℝ} (hk : ChartSmooth (n := n) k) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    {K : Set X} (hK : IsCompact K) :
    ∫⁻ x in K, ENNReal.ofReal (backgroundDatum L f ε ρ F x) *
      multiplierWeight 1 (normalWeight f k x) ∂μ < ⊤ := by
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isSmoothPositiveVolume hμ
  have hcont := continuous_regularBackgroundEnergy L hf hL hF hk hε hρ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  calc ∫⁻ x in K, ENNReal.ofReal (backgroundDatum L f ε ρ F x) * multiplierWeight 1 (normalWeight f k x) ∂μ
      ≤ ∫⁻ x in K, ENNReal.ofReal (regularBackgroundEnergy L f k ε ρ F x) ∂μ :=
        lintegral_mono (fun x => background_energy_le_regular L hf hk ε ρ F x)
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂μ := by
      refine setLIntegral_mono' hK.isClosed.measurableSet fun x hx => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)
    _ = ENNReal.ofReal C * μ K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end SGPT.Trace.OptimalNativeNormalEnergy
