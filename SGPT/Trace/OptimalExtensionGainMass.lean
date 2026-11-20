import SGPT.Trace.OptimalExtensionODE
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact finite annular gain mass and a single positive slack regularizer

This replaces the unnecessary delta-to-zero extension-family limit for the
slack-tolerant HasCircleMEP consumer by an actual positive regularizer choice.
No sharp extension estimate is supplied or asserted here.
Blueprint: work/sgpt-resume-20261114/bert-e2-gain-mass/blueprint/bert-e2-gain-mass.tex.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalExtensionODE Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The literal window mass on the positive logarithmic radial half-line. -/
def windowMass (ε : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), annularWindow ε t

/-- The exact normalized total gain used by optimal extension. -/
def totalGainMass (ε δ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), gain (annularDensity ε δ) t * Real.exp (-t)

/-- A fixed, strictly positive regularizer chosen from the desired slack. -/
def slackRegularizer (ε η : ℝ) : ℝ := η * windowMass ε / 2

theorem integrableOn_annularWindow {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (annularWindow ε) (Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn (annularWindow ε) (Ioc (0 : ℝ) ε) :=
    ((contDiff_annularWindow ε).continuous.intervalIntegrable (μ := volume) 0 ε).1
  have h2 : IntegrableOn (annularWindow ε) (Ioi ε) :=
    integrableOn_zero.congr_fun (fun t ht => (annularWindow_eq_zero hε ht.le).symm) measurableSet_Ioi
  have he : Ioi (0 : ℝ) = Ioc (0 : ℝ) ε ∪ Ioi ε := by
    ext t
    simp only [mem_union, mem_Ioi, mem_Ioc]
    constructor
    · intro ht
      by_cases hte : t ≤ ε
      · exact Or.inl ⟨ht, hte⟩
      · exact Or.inr (lt_of_not_ge hte)
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hε.trans ht
  rw [he]
  exact h1.union h2

theorem windowMass_eq_interval {ε : ℝ} (hε : 0 < ε) :
    windowMass ε = ∫ t in (0 : ℝ)..ε, annularWindow ε t := by
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) (f := annularWindow ε)
    measurableSet_Ioi (show Ioc (0 : ℝ) ε ⊆ Ioi (0 : ℝ) from fun _ ht => ht.1)
    (fun t ht => by
      have hte : ε ≤ t := by
        by_contra h
        exact ht.2 ⟨ht.1, (lt_of_not_ge h).le⟩
      exact annularWindow_eq_zero hε hte)
  exact h.trans (intervalIntegral.integral_of_le hε.le).symm

theorem half_le_windowMass {ε : ℝ} (hε : 0 < ε) : ε / 2 ≤ windowMass ε := by
  have hhalf := half_pos hε
  have he : (∫ t in (0 : ℝ)..ε / 2, annularWindow ε t) = ε / 2 := by
    calc
      _ = ∫ _t in (0 : ℝ)..ε / 2, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hhalf.le] at ht
        exact annularWindow_eq_one hε ht.2
      _ = _ := by simp
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (a := 0) (b := ε / 2) (c := 0) (d := ε) le_rfl hhalf.le (by linarith)
    (ae_of_all _ fun t => annularWindow_nonneg ε t)
    ((contDiff_annularWindow ε).continuous.intervalIntegrable (μ := volume) 0 ε)
  rwa [he, ← windowMass_eq_interval hε] at hmono

theorem windowMass_pos {ε : ℝ} (hε : 0 < ε) : 0 < windowMass ε :=
  (half_pos hε).trans_le (half_le_windowMass hε)

theorem windowMass_le {ε : ℝ} (hε : 0 < ε) : windowMass ε ≤ ε := by
  rw [windowMass_eq_interval hε]
  calc
    _ ≤ ∫ _t in (0 : ℝ)..ε, (1 : ℝ) :=
      intervalIntegral.integral_mono hε.le
        ((contDiff_annularWindow ε).continuous.intervalIntegrable (μ := volume) 0 ε)
        intervalIntegrable_const (fun t => annularWindow_le_one ε t)
    _ = _ := by simp

theorem integrableOn_annularDensity {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    IntegrableOn (annularDensity ε δ) (Ioi (0 : ℝ)) :=
  (integrableOn_annularWindow hε).add ((integrableOn_exp_neg_Ioi 0).const_mul δ)

theorem integral_annularDensity {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    (∫ t in Ioi (0 : ℝ), annularDensity ε δ t) = windowMass ε + δ := by
  change (∫ t in Ioi (0 : ℝ), annularWindow ε t + δ * Real.exp (-t)) = _
  rw [integral_add (integrableOn_annularWindow hε) ((integrableOn_exp_neg_Ioi 0).const_mul δ),
    integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rfl

theorem gain_mul_exp_neg (w : ℝ → ℝ) (t : ℝ) :
    gain w t * Real.exp (-t) = w t := by
  unfold gain
  calc
    _ = (Real.exp t * Real.exp (-t)) * w t := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem totalGainMass_eq {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    totalGainMass ε δ = windowMass ε + δ := by
  unfold totalGainMass
  simp_rw [gain_mul_exp_neg]
  exact integral_annularDensity hε δ

theorem tendsto_mass_annularDensity {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    Tendsto (mass (annularDensity ε δ)) atTop (𝓝 (windowMass ε + δ)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_annularDensity hε δ)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  rw [integral_annularDensity hε δ] at h
  convert h using 1
  rfl

theorem tendsto_potential_annularDensity {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    Tendsto (potential (annularDensity ε δ)) atTop (𝓝 (-Real.log (windowMass ε + δ))) := by
  have hC : 0 < windowMass ε + δ := add_pos_of_pos_of_nonneg (windowMass_pos hε) hδ
  exact ((Real.continuousAt_log hC.ne').tendsto.comp (tendsto_mass_annularDensity hε δ)).neg

theorem slackRegularizer_pos {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    0 < slackRegularizer ε η := div_pos (mul_pos hη (windowMass_pos hε)) (by norm_num)

theorem totalGainMass_slackRegularizer {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    totalGainMass ε (slackRegularizer ε η) = (1 + η / 2) * windowMass ε := by
  rw [totalGainMass_eq hε, slackRegularizer]
  ring

theorem totalGainMass_lt_slack {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    totalGainMass ε (slackRegularizer ε η) < (1 + η) * windowMass ε := by
  rw [totalGainMass_slackRegularizer hε]
  nlinarith [mul_pos hη (windowMass_pos hε)]

theorem windowPart_le_gain {ε δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    Real.exp t * annularWindow ε t ≤ gain (annularDensity ε δ) t := by
  rw [gain_annularDensity]
  exact le_add_of_nonneg_right hδ

theorem actual_positive_regularizer_for_slack {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    0 < slackRegularizer ε η ∧
    totalGainMass ε (slackRegularizer ε η) < (1 + η) * windowMass ε ∧
    ∀ t : ℝ, Real.exp t * annularWindow ε t ≤ gain (annularDensity ε (slackRegularizer ε η)) t :=
  ⟨slackRegularizer_pos hε hη, totalGainMass_lt_slack hε hη,
    windowPart_le_gain (slackRegularizer_pos hε hη).le⟩

theorem contDiff_actualGain (ε δ : ℝ) :
    ContDiff ℝ ∞ (gain (annularDensity ε δ)) :=
  Real.contDiff_exp.mul (contDiff_annularDensity ε δ)

theorem actualGain_pos (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 < gain (annularDensity ε δ) t := mul_pos (Real.exp_pos _) (annularDensity_pos ε hδ t)

theorem integrableOn_normalized_actualGain {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    IntegrableOn (fun t => gain (annularDensity ε δ) t * Real.exp (-t)) (Ioi (0 : ℝ)) :=
  (integrableOn_annularDensity hε δ).congr_fun
    (fun t _ => (gain_mul_exp_neg (annularDensity ε δ) t).symm) measurableSet_Ioi

theorem antitone_normalized_actualGain {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    Antitone (fun t => gain (annularDensity ε δ) t * Real.exp (-t)) := by
  intro a b hab
  change gain (annularDensity ε δ) b * Real.exp (-b) ≤ gain (annularDensity ε δ) a * Real.exp (-a)
  rw [gain_mul_exp_neg, gain_mul_exp_neg]
  exact antitone_annularDensity hε hδ hab

/-- The genuine strict gain-admissibility inequality of Guan–Zhou (2.4)
is produced for the actual positive regularized annular density. -/
theorem actualGain_strict_primitive_inequality {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {t : ℝ} (ht : 0 < t) :
    annularDensity ε δ t * integratedMass (annularDensity ε δ) t < mass (annularDensity ε δ) t ^ 2 :=
  mass_sq_gt_weight_integratedMass (contDiff_annularDensity ε δ).continuous
    (fun r _ => annularDensity_pos ε hδ r) ((antitone_annularDensity hε hδ.le).antitoneOn (Ici 0)) ht


end SGPT.Trace.OptimalExtensionGainMass
