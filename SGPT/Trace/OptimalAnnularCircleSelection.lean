import SGPT.Trace.OptimalPolarCircleEnergy
import SGPT.Trace.OptimalAnnularSelection

/-!
# Actual original annular circles from sharp parameter gain energy

The original pi*rho^2 and rho^2/2 factors are retained and cancelled exactly.
Zero central norm is included; the actual selected closed disc stays inside
its original open extension domain. This is a scalar producer, not a supplied
HasCircleMEP or intrinsic Hodge dictionary.
Blueprint: work/sgpt-resume-20261114/bert-e2-annular-circles/blueprint/bert-e2-annular-circles.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalAnnularCircleSelection
open Set Filter MeasureTheory Metric Complex
open scoped Topology ENNReal
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalPolarCircleEnergy SGPT.Trace.OptimalAnnularSelection

def actualLogCircleProfile (ρ : ℝ) (Q : ℂ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 (ρ * Real.exp (-t / 2)) θ)

theorem measurable_actualLogCircleProfile (ρ : ℝ) {Q : ℂ → ℝ≥0∞} (hQ : Measurable Q) :
    Measurable (actualLogCircleProfile ρ Q) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 (ρ * Real.exp (-p.1 / 2)) p.2) := by
    simp only [circleMap_zero]
    fun_prop
  exact (hQ.comp hc.measurable).lintegral_prod_right'

theorem original_window_circle_energy_le {ρ σ δ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hδ : 0 ≤ δ) {Q : ℂ → ℝ≥0∞} (hQ : Measurable Q) (B : ℝ≥0∞)
    (hbound : (∫⁻ τ in ball (0 : ℂ) ρ,
      ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))) * Q τ) ≤
        ENNReal.ofReal ((windowMass σ + δ) * Real.pi * ρ ^ 2) * B) :
    (∫⁻ t in Ioc (0 : ℝ) σ, ENNReal.ofReal (annularWindow σ t) * actualLogCircleProfile ρ Q t) ≤
      ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (2 * Real.pi) * B) := by
  have hk : 0 < ρ ^ 2 / 2 := by positivity
  have ha : 0 ≤ windowMass σ + δ := add_nonneg (windowMass_pos hσ).le hδ
  have hcoeff : ENNReal.ofReal (ρ ^ 2 / 2) *
      (ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (2 * Real.pi) * B)) =
      ENNReal.ofReal ((windowMass σ + δ) * Real.pi * ρ ^ 2) * B := by
    calc _ = (ENNReal.ofReal (ρ ^ 2 / 2) * ENNReal.ofReal (windowMass σ + δ) *
          ENNReal.ofReal (2 * Real.pi)) * B := by ac_rfl
      _ = ENNReal.ofReal ((ρ ^ 2 / 2 * (windowMass σ + δ)) * (2 * Real.pi)) * B := by
        rw [← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_mul (mul_nonneg hk.le ha)]
      _ = _ := by congr 2; ring
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hk).ne' ENNReal.ofReal_ne_top).mp
  calc ENNReal.ofReal (ρ ^ 2 / 2) *
        (∫⁻ t in Ioc (0 : ℝ) σ, ENNReal.ofReal (annularWindow σ t) * actualLogCircleProfile ρ Q t)
      ≤ ENNReal.ofReal (ρ ^ 2 / 2) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (annularDensity σ δ t) * actualLogCircleProfile ρ Q t := by
        apply mul_le_mul_of_nonneg_left ?_ zero_le
        refine (setLIntegral_mono' measurableSet_Ioc (fun t _ => ?_)).trans
          (lintegral_mono_set Ioc_subset_Ioi_self)
        apply mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        exact le_add_of_nonneg_right (mul_nonneg hδ (Real.exp_pos _).le)
    _ = (∫⁻ τ in ball (0 : ℂ) ρ,
        ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))) * Q τ) :=
      (actual_original_disc_gain_circle_energy hρ σ δ hQ).symm
    _ ≤ ENNReal.ofReal ((windowMass σ + δ) * Real.pi * ρ ^ 2) * B := hbound
    _ = _ := hcoeff.symm

theorem exists_actual_annular_circle_of_sharp_gain {ρ ρ' σ η : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hη : 0 < η)
    (hann : ρ' < ρ * Real.exp (-σ / 2)) {Q : ℂ → ℝ≥0∞} (hQ : Measurable Q)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : (∫⁻ τ in ball (0 : ℂ) ρ,
      ENNReal.ofReal (gain (annularDensity σ (slackRegularizer σ η))
        (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))) * Q τ) ≤
        ENNReal.ofReal ((windowMass σ + slackRegularizer σ η) * Real.pi * ρ ^ 2) * B) :
    ∃ s ∈ Ioo ρ' ρ, closedBall (0 : ℂ) s ⊆ ball (0 : ℂ) ρ ∧
      (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 s θ)) ≤
        ENNReal.ofReal ((1 + η) * (2 * Real.pi)) * B := by
  have hwindow := original_window_circle_energy_le hρ hσ (slackRegularizer_pos hσ hη).le hQ B hbound
  obtain ⟨t, ht, hmean⟩ := exists_actual_log_radius_of_annular_estimate hσ hη
    (measurable_actualLogCircleProfile ρ hQ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) hwindow
  obtain ⟨hs, hclosed⟩ := actual_selected_radius_inside hρ hann ht
  refine ⟨ρ * Real.exp (-t / 2), hs, hclosed, ?_⟩
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + η)] at hmean
  exact hmean

end SGPT.Trace.OptimalAnnularCircleSelection
