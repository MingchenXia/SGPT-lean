import SGPT.Trace.OptimalExtensionGainMass
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Actual annular selection from one finite positive slack

The zero central-norm case is included. The selected actual radius is
strictly inside the original extension disc, with its actual closed ball.
Blueprint: work/sgpt-resume-20261114/bert-e2-annular-selection/blueprint/bert-e2-annular-selection.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalAnnularSelection
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass

def actualWindowMeasure (σ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) σ)).withDensity (fun t => ENNReal.ofReal (annularWindow σ t))

theorem actualWindowMeasure_mass {σ : ℝ} (hσ : 0 < σ) :
    actualWindowMeasure σ univ = ENNReal.ofReal (windowMass σ) := by
  rw [actualWindowMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (((contDiff_annularWindow σ).continuous.intervalIntegrable (μ := volume) 0 σ).1)
    (Filter.Eventually.of_forall fun t => annularWindow_nonneg σ t),
    ← intervalIntegral.integral_of_le hσ.le, ← windowMass_eq_interval hσ]

theorem actualWindowMeasure_concentrated (σ : ℝ) :
    ∀ᵐ t ∂actualWindowMeasure σ, t ∈ Ioc (0 : ℝ) σ :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

theorem exists_actual_point_of_finite_slack {Y : Type} [MeasurableSpace Y]
    (ν : Measure Y) {A : Set Y} (hA : ∀ᵐ x ∂ν, x ∈ A)
    {C₀ η : ℝ} (hC₀ : 0 < C₀) (hη : 0 < η)
    (hν : ν univ = ENNReal.ofReal C₀) {H : Y → ℝ≥0∞} (hH : Measurable H)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : (∫⁻ x, H x ∂ν) ≤ ENNReal.ofReal (C₀ + η * C₀ / 2) * B) :
    ∃ x ∈ A, H x ≤ ENNReal.ofReal (1 + η) * B := by
  have : NeZero ν := ⟨by
    intro hz
    have hzero : ν univ = 0 := by rw [hz]; rfl
    exact (ENNReal.ofReal_pos.mpr hC₀).ne' (hν.symm.trans hzero)⟩
  by_cases hB0 : B = 0
  · have hzero : (∫⁻ x, H x ∂ν) = 0 := le_antisymm (by simpa only [hB0, mul_zero] using hbound) bot_le
    have hz := (lintegral_eq_zero_iff hH).mp hzero
    obtain ⟨x, hxA, hx0⟩ := (hA.and hz).exists
    change H x = 0 at hx0
    exact ⟨x, hxA, by simpa only [hx0, hB0, mul_zero] using (le_refl (0 : ℝ≥0∞))⟩
  by_contra hn
  push Not at hn
  have hlower : ENNReal.ofReal (C₀ * (1 + η)) * B ≤ (∫⁻ x, H x ∂ν) := by
    have hm : ENNReal.ofReal (C₀ * (1 + η)) * B =
        (ENNReal.ofReal (1 + η) * B) * ν univ := by
      rw [hν, ENNReal.ofReal_mul hC₀.le]
      ac_rfl
    rw [hm]
    exact (lintegral_const _).symm.trans_le
      (lintegral_mono_ae (hA.mono fun x hx => (hn x hx).le))
  have hc : C₀ + η * C₀ / 2 < C₀ * (1 + η) := by nlinarith [mul_pos hη hC₀]
  have hc' : ENNReal.ofReal (C₀ + η * C₀ / 2) < ENNReal.ofReal (C₀ * (1 + η)) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos hC₀ (by linarith))).mpr hc
  exact (ENNReal.mul_lt_mul_left hB0 hB hc').not_ge (hlower.trans hbound)

theorem exists_actual_log_radius_of_annular_estimate {σ η : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) {H : ℝ → ℝ≥0∞} (hH : Measurable H)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : (∫⁻ t in Ioc (0 : ℝ) σ, ENNReal.ofReal (annularWindow σ t) * H t) ≤
      ENNReal.ofReal (windowMass σ + slackRegularizer σ η) * B) :
    ∃ t ∈ Ioc (0 : ℝ) σ, H t ≤ ENNReal.ofReal (1 + η) * B := by
  apply exists_actual_point_of_finite_slack (actualWindowMeasure σ)
    (actualWindowMeasure_concentrated σ) (windowMass_pos hσ) hη (actualWindowMeasure_mass hσ) hH hB
  rw [actualWindowMeasure, lintegral_withDensity_eq_lintegral_mul _
    ((contDiff_annularWindow σ).continuous.measurable.ennreal_ofReal) hH]
  exact hbound

theorem exists_actual_log_window {ρ ρ' : ℝ} (_hρ' : 0 < ρ') (hρ : ρ' < ρ) :
    ∃ σ : ℝ, 0 < σ ∧ ρ' < ρ * Real.exp (-σ / 2) := by
  have hc : Continuous (fun σ : ℝ => ρ * Real.exp (-σ / 2)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_neg.div_const 2))
  have ho : IsOpen {σ : ℝ | ρ' < ρ * Real.exp (-σ / 2)} := isOpen_lt continuous_const hc
  have h0 : (0 : ℝ) ∈ {σ : ℝ | ρ' < ρ * Real.exp (-σ / 2)} := by
    simpa only [mem_ofPred_eq, neg_zero, zero_div, Real.exp_zero, mul_one] using hρ
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨R / 2, half_pos hR, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hR)]
  exact half_lt_self hR

theorem actual_selected_radius_inside {ρ ρ' σ t : ℝ} (hρ : 0 < ρ)
    (hann : ρ' < ρ * Real.exp (-σ / 2)) (ht : t ∈ Ioc (0 : ℝ) σ) :
    ρ * Real.exp (-t / 2) ∈ Ioo ρ' ρ ∧
      closedBall (0 : ℂ) (ρ * Real.exp (-t / 2)) ⊆ ball (0 : ℂ) ρ := by
  have hlow : ρ' < ρ * Real.exp (-t / 2) := hann.trans_le
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hρ.le)
  have hhigh : ρ * Real.exp (-t / 2) < ρ := by
    have he : Real.exp (-t / 2) < 1 := by rw [← Real.exp_zero, Real.exp_lt_exp]; linarith [ht.1]
    exact mul_lt_of_lt_one_right hρ he
  refine ⟨⟨hlow, hhigh⟩, fun z hz => ?_⟩
  rw [mem_ball, dist_zero_right]
  simpa only [dist_zero_right] using (mem_closedBall.mp hz).trans_lt hhigh

end SGPT.Trace.OptimalAnnularSelection
