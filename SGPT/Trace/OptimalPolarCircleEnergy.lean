import SGPT.Trace.OptimalExtensionODE
import SGPT.Bergman.Quant2SharpSubmean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual original parameter polar and logarithmic circle energy

Every measure is ordinary original parameter Lebesgue. The exact Jacobian
and the original angular interval are proved, never supplied as certificates.
Blueprint: work/sgpt-resume-20261114/bert-e2-polar-circles/blueprint/bert-e2-polar-circles.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalPolarCircleEnergy
open Set Filter MeasureTheory Metric Complex
open scoped Topology ENNReal
open SGPT.Trace.OptimalExtensionODE

theorem original_circle_angular_cut_eq (Q : ℂ → ℝ≥0∞) (r : ℝ) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, Q (circleMap 0 r θ)) =
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 r θ) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hp : Function.Periodic (fun θ => Q (circleMap 0 r θ)) (2 * Real.pi) :=
    (periodic_circleMap 0 r).comp Q
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  have ha : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [ha] at h1
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  simpa only [Function.Periodic.lift_coe, zero_add] using h1.trans h2.symm

theorem original_polar_symm_eq_circle (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

theorem original_disc_lintegral_circle_profile (ρ : ℝ) {Q : ℂ → ℝ≥0∞} (hQ : Measurable Q) :
    (∫⁻ τ in ball (0 : ℂ) ρ, Q τ) =
      ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 r θ) := by
  rw [SGPT.Bergman.SharpLocalUpper.sourceSharp_disk_lintegral_polar]
  simp_rw [original_polar_symm_eq_circle]
  have hcircle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap_zero]
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * Q (circleMap 0 p.1 p.2)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hQ.comp hcircle.measurable)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm.aemeasurable]
  congr 1
  funext r
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, original_circle_angular_cut_eq]

theorem actual_log_radius_image_derivative {ρ : ℝ} (hρ : 0 < ρ) :
    (fun t : ℝ => ρ * Real.exp (-t / 2)) '' Ioi 0 = Ioo 0 ρ ∧
    Function.Injective (fun t : ℝ => ρ * Real.exp (-t / 2)) ∧
    ∀ t : ℝ, HasDerivAt (fun t : ℝ => ρ * Real.exp (-t / 2))
      (-(ρ * Real.exp (-t / 2)) / 2) t := by
  constructor
  · ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨mul_pos hρ (Real.exp_pos _), ?_⟩
      apply mul_lt_of_lt_one_right hρ
      rw [← Real.exp_zero, Real.exp_lt_exp]
      have ht0 : 0 < t := ht
      linarith
    · rintro ⟨hr0, hrρ⟩
      have hq0 : 0 < r / ρ := div_pos hr0 hρ
      have hq1 : r / ρ < 1 := (div_lt_one hρ).mpr hrρ
      refine ⟨-2 * Real.log (r / ρ), ?_, ?_⟩
      · have hlog := Real.log_neg hq0 hq1
        change 0 < -2 * Real.log (r / ρ)
        nlinarith
      · change ρ * Real.exp (-(-2 * Real.log (r / ρ)) / 2) = r
        rw [show -(-2 * Real.log (r / ρ)) / 2 = Real.log (r / ρ) by ring,
          Real.exp_log hq0]
        field_simp
  constructor
  · intro a b hab
    have he := Real.exp_injective (mul_left_cancel₀ hρ.ne' hab)
    linarith
  · intro t
    have hlin : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) t :=
      (hasDerivAt_id t).neg.div_const 2
    convert ((Real.hasDerivAt_exp (-t / 2)).comp t hlin).const_mul ρ using 1 <;> first | rfl | ring

theorem actual_logarithmic_radial_gain_identity {ρ : ℝ} (hρ : 0 < ρ)
    (σ δ : ℝ) (H : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal r *
      ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (r ^ 2 / ρ ^ 2))) * H r) =
      ENNReal.ofReal (ρ ^ 2 / 2) * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (annularDensity σ δ t) * H (ρ * Real.exp (-t / 2)) := by
  obtain ⟨himage, hinj, hd⟩ := actual_log_radius_image_derivative hρ
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn
    (fun r => ENNReal.ofReal r *
      ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (r ^ 2 / ρ ^ 2))) * H r)
  rw [himage] at hcv
  rw [hcv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  have hr : 0 < ρ * Real.exp (-t / 2) := mul_pos hρ (Real.exp_pos _)
  have hnorm : (ρ * Real.exp (-t / 2)) ^ 2 / ρ ^ 2 = Real.exp (-t) := by
    rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hρ.ne'), ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have ht : -Real.log ((ρ * Real.exp (-t / 2)) ^ 2 / ρ ^ 2) = t := by
    rw [hnorm, Real.log_exp, neg_neg]
  rw [ht, abs_of_neg (by linarith : -(ρ * Real.exp (-t / 2)) / 2 < 0)]
  have habs : -(-(ρ * Real.exp (-t / 2)) / 2) = (ρ * Real.exp (-t / 2)) / 2 := by ring
  rw [habs]
  simp only [gain]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (ρ * Real.exp (-t / 2)) / 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (ρ * Real.exp (-t / 2)) / 2 * (ρ * Real.exp (-t / 2))),
    ← mul_assoc (ENNReal.ofReal (ρ ^ 2 / 2)) (ENNReal.ofReal (annularDensity σ δ t))
      (H (ρ * Real.exp (-t / 2))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ ρ ^ 2 / 2)]
  congr 2
  calc (ρ * Real.exp (-t / 2) / 2 * (ρ * Real.exp (-t / 2))) *
        (Real.exp t * annularDensity σ δ t) =
      ρ ^ 2 / 2 * ((Real.exp (-t / 2) * Real.exp (-t / 2) * Real.exp t) * annularDensity σ δ t) := by ring
    _ = ρ ^ 2 / 2 * annularDensity σ δ t := by
      rw [← Real.exp_add, ← Real.exp_add, show -t / 2 + -t / 2 + t = 0 by ring, Real.exp_zero, one_mul]

theorem actual_original_disc_gain_circle_energy {ρ : ℝ} (hρ : 0 < ρ)
    (σ δ : ℝ) {Q : ℂ → ℝ≥0∞} (hQ : Measurable Q) :
    (∫⁻ τ in ball (0 : ℂ) ρ,
      ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))) * Q τ) =
      ENNReal.ofReal (ρ ^ 2 / 2) * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (annularDensity σ δ t) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 (ρ * Real.exp (-t / 2)) θ) := by
  have hm : Measurable (fun τ : ℂ => -Real.log (‖τ / (ρ : ℂ)‖ ^ 2)) :=
    (Real.measurable_log.comp (((continuous_id.div_const (ρ : ℂ)).norm.pow 2).measurable)).neg
  have hg : Continuous (gain (annularDensity σ δ)) :=
    Real.continuous_exp.mul (contDiff_annularDensity σ δ).continuous
  have hW : Measurable (fun τ : ℂ =>
      ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))) * Q τ) :=
    (ENNReal.measurable_ofReal.comp (hg.measurable.comp hm)).mul hQ
  rw [original_disc_lintegral_circle_profile ρ hW]
  calc (∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal r *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (gain (annularDensity σ δ)
            (-Real.log (‖circleMap 0 r θ / (ρ : ℂ)‖ ^ 2))) * Q (circleMap 0 r θ))
      = ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal r *
          (ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (r ^ 2 / ρ ^ 2))) *
            ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 r θ)) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro r _
        dsimp only
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro θ _
        dsimp only
        rw [norm_div, norm_circleMap_zero, Complex.norm_real,
          Real.norm_of_nonneg hρ.le, div_pow, sq_abs]
    _ = _ := by
      simpa only [mul_assoc] using actual_logarithmic_radial_gain_identity hρ σ δ
        (fun r => ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), Q (circleMap 0 r θ))

end SGPT.Trace.OptimalPolarCircleEnergy
