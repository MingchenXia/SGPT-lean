import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Guan–Zhou's actual scalar sharp-extension weights

Integral primitives produce the scalar ODE inputs of the sharp estimate.
No extension estimate or minimal extension property is assumed or asserted.
Blueprint: work/sgpt-resume-20261114/bert-e2-optimal-ode/blueprint/bert-e2-optimal-ode.tex.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.OptimalExtensionODE
open Set Filter MeasureTheory
open scoped Topology ContDiff

def mass (w : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in 0..t, w r

def integratedMass (w : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in 0..t, mass w r

def potential (w : ℝ → ℝ) (t : ℝ) : ℝ := -Real.log (mass w t)

def twist (w : ℝ → ℝ) (t : ℝ) : ℝ := integratedMass w t / mass w t

theorem hasDerivAt_mass {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    HasDerivAt (mass w) (w t) t :=
  intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable _ _)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

theorem continuous_mass {w : ℝ → ℝ} (hw : Continuous w) : Continuous (mass w) :=
  (fun t => (hasDerivAt_mass hw t).continuousAt) |> continuous_iff_continuousAt.mpr

theorem hasDerivAt_integratedMass {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    HasDerivAt (integratedMass w) (mass w t) t :=
  hasDerivAt_mass (continuous_mass hw) t

theorem mass_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    0 < mass w t := by
  apply intervalIntegral.integral_pos ht hw.continuousOn
  · intro r hr
    exact (hpos r hr.1.le).le
  · exact ⟨0, ⟨le_rfl, ht.le⟩, hpos 0 (by simp)⟩

theorem mass_mono {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    mass w a ≤ mass w b := by
  apply intervalIntegral.integral_mono_interval (a := 0) (b := a) (c := 0) (d := b)
    (μ := volume) le_rfl ha hab
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hpos r hr.1.le).le
  · exact hw.intervalIntegrable _ _

theorem integratedMass_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    0 < integratedMass w t := by
  apply intervalIntegral.integral_pos ht (continuous_mass hw).continuousOn
  · intro r hr
    exact (mass_pos hw hpos hr.1).le
  · exact ⟨t, ⟨ht.le, le_rfl⟩, mass_pos hw hpos ht⟩

theorem integratedMass_lt_mul_mass {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    integratedMass w t < t * mass w t := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (continuous_mass hw).continuousOn (continuousOn_const (c := mass w t))
    (fun r hr => mass_mono hw hpos hr.1.le hr.2)
    ⟨0, ⟨le_rfl, ht.le⟩, by simpa [mass] using mass_pos hw hpos ht⟩
  simpa only [integratedMass, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

theorem mul_weight_le_mass {w : ℝ → ℝ} (hw : Continuous w)
    (hanti : AntitoneOn w (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    t * w t ≤ mass w t := by
  have h := intervalIntegral.integral_mono_on ht intervalIntegrable_const
    (hw.intervalIntegrable (μ := volume) _ _) (fun r hr => hanti hr.1 ht hr.2)
  simpa only [mass, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

theorem mass_sq_gt_weight_integratedMass {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    w t * integratedMass w t < mass w t ^ 2 := by
  have hA := mass_pos hw hpos ht
  have hB := integratedMass_lt_mul_mass hw hpos ht
  have hwa := mul_weight_le_mass hw hanti ht.le
  have hwpos := hpos t ht.le
  nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hwa), mul_lt_mul_of_pos_left hB hwpos]

theorem hasDerivAt_potential {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (potential w) (-w t / mass w t) t := by
  convert ((hasDerivAt_mass hw t).log (mass_pos hw hpos ht).ne').neg using 1 <;>
    first | rfl | (simp only [neg_div])

theorem hasDerivAt_twist {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (twist w) (1 - integratedMass w t * w t / mass w t ^ 2) t := by
  have hA := (mass_pos hw hpos ht).ne'
  have h := (hasDerivAt_integratedMass hw t).div (hasDerivAt_mass hw t) hA
  have he : (mass w t * mass w t - integratedMass w t * w t) / mass w t ^ 2 =
      1 - integratedMass w t * w t / mass w t ^ 2 := by
    field_simp
  rw [he] at h
  exact h

theorem deriv_potential {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    deriv (potential w) t = -w t / mass w t := (hasDerivAt_potential hw hpos ht).deriv

theorem deriv_twist {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    deriv (twist w) t = 1 - integratedMass w t * w t / mass w t ^ 2 :=
  (hasDerivAt_twist hw hpos ht).deriv

theorem deriv_potential_neg {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    deriv (potential w) t < 0 := by
  rw [deriv_potential hw hpos ht]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (hpos t ht.le)) (mass_pos hw hpos ht)

theorem deriv_twist_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    0 < deriv (twist w) t := by
  rw [deriv_twist hw hpos ht]
  apply sub_pos.mpr
  apply (div_lt_one (sq_pos_of_pos (mass_pos hw hpos ht))).mpr
  simpa only [mul_comm] using mass_sq_gt_weight_integratedMass hw hpos hanti ht

theorem twist_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    0 < twist w t := div_pos (integratedMass_pos hw hpos ht) (mass_pos hw hpos ht)

theorem first_ode {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    deriv (twist w) t - twist w t * deriv (potential w) t = 1 := by
  rw [deriv_twist hw hpos ht, deriv_potential hw hpos ht, twist]
  field_simp [(mass_pos hw hpos ht).ne']
  ring

theorem hasDerivAt_deriv_potential {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t)
    (hd : DifferentiableAt ℝ w t) :
    HasDerivAt (deriv (potential w))
      ((w t ^ 2 - deriv w t * mass w t) / mass w t ^ 2) t := by
  have he : deriv (potential w) =ᶠ[𝓝 t] (fun r => -w r / mass w r) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact deriv_potential hw hpos hr
  convert (hd.hasDerivAt.neg.div (hasDerivAt_mass hw t)
    (mass_pos hw hpos ht).ne').congr_of_eventuallyEq he using 1 <;>
    first | rfl | (simp only [Pi.neg_apply]; ring)

theorem hasDerivAt_deriv_twist {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t)
    (hd : DifferentiableAt ℝ w t) :
    HasDerivAt (deriv (twist w))
      (-w t / mass w t - integratedMass w t * deriv w t / mass w t ^ 2 +
        2 * integratedMass w t * w t ^ 2 / mass w t ^ 3) t := by
  have he : deriv (twist w) =ᶠ[𝓝 t]
      (fun r => 1 - integratedMass w r * w r / mass w r ^ 2) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact deriv_twist hw hpos hr
  have hA := (mass_pos hw hpos ht).ne'
  convert ((hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_integratedMass hw t).mul hd.hasDerivAt).div
      ((hasDerivAt_mass hw t).pow 2) (pow_ne_zero 2 hA))).congr_of_eventuallyEq he using 1 <;>
    first | rfl | (simp only [Pi.pow_apply, Pi.mul_apply]; field_simp; ring)


/-- The literal second-derivative coefficient in Guan–Zhou's twisted estimate. -/
def curvatureCoefficient (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  twist w t * deriv (deriv (potential w)) t - deriv (deriv (twist w)) t

/-- The actual positive correction multiplying the squared derivative. -/
def correction (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  curvatureCoefficient w t / deriv (twist w) t ^ 2

/-- The actual gain c, for which w=c exp(-t). -/
def gain (w : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp t * w t

theorem curvatureCoefficient_eq {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t)
    (hd : DifferentiableAt ℝ w t) :
    curvatureCoefficient w t = deriv (twist w) t * (-deriv (potential w) t) := by
  rw [curvatureCoefficient, (hasDerivAt_deriv_potential hw hpos ht hd).deriv,
    (hasDerivAt_deriv_twist hw hpos ht hd).deriv,
    deriv_twist hw hpos ht, deriv_potential hw hpos ht, twist]
  field_simp [(mass_pos hw hpos ht).ne']
  ring

theorem curvatureCoefficient_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) (hd : DifferentiableAt ℝ w t) :
    0 < curvatureCoefficient w t := by
  rw [curvatureCoefficient_eq hw hpos ht hd]
  exact mul_pos (deriv_twist_pos hw hpos hanti ht) (neg_pos.mpr (deriv_potential_neg hw hpos ht))

theorem correction_pos {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) (hd : DifferentiableAt ℝ w t) :
    0 < correction w t :=
  div_pos (curvatureCoefficient_pos hw hpos hanti ht hd)
    (sq_pos_of_pos (deriv_twist_pos hw hpos hanti ht))

theorem actual_curvature_cancellation {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) :
    curvatureCoefficient w t - correction w t * deriv (twist w) t ^ 2 = 0 := by
  rw [correction, div_mul_cancel₀ _ (pow_ne_zero 2 (deriv_twist_pos hw hpos hanti ht).ne'), sub_self]

theorem twist_add_reciprocal_correction {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) (hd : DifferentiableAt ℝ w t) :
    twist w t + (correction w t)⁻¹ = mass w t / w t := by
  have hs := (deriv_twist_pos hw hpos hanti ht).ne'
  have hu := (deriv_potential_neg hw hpos ht).ne
  have hc : (correction w t)⁻¹ = -deriv (twist w) t / deriv (potential w) t := by
    rw [correction, inv_div, curvatureCoefficient_eq hw hpos ht hd]
    field_simp
  rw [hc]
  have he : twist w t - deriv (twist w) t / deriv (potential w) t =
      -1 / deriv (potential w) t := by
    field_simp
    nlinarith [first_ode hw hpos ht]
  rw [neg_div, ← sub_eq_add_neg, he, deriv_potential hw hpos ht]
  field_simp [(mass_pos hw hpos ht).ne', (hpos t ht.le).ne']

theorem exp_potential {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    Real.exp (potential w t) = 1 / mass w t := by
  rw [potential, Real.exp_neg, Real.exp_log (mass_pos hw hpos ht), one_div]

theorem sharp_reciprocal_gain {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {t : ℝ} (ht : 0 < t) (hd : DifferentiableAt ℝ w t) :
    (twist w t + (correction w t)⁻¹) * Real.exp (potential w t - t) =
      (gain w t)⁻¹ := by
  rw [twist_add_reciprocal_correction hw hpos hanti ht hd,
    Real.exp_sub, exp_potential hw hpos ht, gain]
  field_simp [(mass_pos hw hpos ht).ne', (hpos t ht.le).ne', Real.exp_ne_zero]


/-- A literal smooth cutoff in the logarithmic radial variable. -/
def annularWindow (ε t : ℝ) : ℝ := Real.smoothTransition ((ε - t) / (ε / 2))

/-- The actual strictly positive decreasing gain density. -/
def annularDensity (ε δ t : ℝ) : ℝ := annularWindow ε t + δ * Real.exp (-t)

theorem annularWindow_nonneg (ε t : ℝ) : 0 ≤ annularWindow ε t :=
  Real.smoothTransition.nonneg _

theorem annularWindow_le_one (ε t : ℝ) : annularWindow ε t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem annularWindow_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    annularWindow ε t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by linarith))

theorem annularWindow_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε / 2) :
    annularWindow ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by linarith : 0 < ε / 2)).mpr
  linarith

theorem contDiff_annularWindow (ε : ℝ) : ContDiff ℝ ∞ (annularWindow ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

theorem antitone_annularWindow {ε : ℝ} (hε : 0 < ε) : Antitone (annularWindow ε) := by
  intro a b hab
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem contDiff_annularDensity (ε δ : ℝ) : ContDiff ℝ ∞ (annularDensity ε δ) :=
  (contDiff_annularWindow ε).add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_id.neg))

theorem annularDensity_pos (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 < annularDensity ε δ t :=
  add_pos_of_nonneg_of_pos (annularWindow_nonneg ε t) (mul_pos hδ (Real.exp_pos _))

theorem antitone_annularDensity {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    Antitone (annularDensity ε δ) := by
  intro a b hab
  exact add_le_add (antitone_annularWindow hε hab)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hab)) hδ)

theorem gain_annularDensity (ε δ t : ℝ) :
    gain (annularDensity ε δ) t = Real.exp t * annularWindow ε t + δ := by
  simp only [gain, annularDensity, mul_add, Real.exp_neg]
  field_simp

theorem actual_annular_weights {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {t : ℝ} (ht : 0 < t) :
    0 < curvatureCoefficient (annularDensity ε δ) t ∧
    0 < correction (annularDensity ε δ) t ∧
    deriv (twist (annularDensity ε δ)) t - twist (annularDensity ε δ) t *
      deriv (potential (annularDensity ε δ)) t = 1 ∧
    (twist (annularDensity ε δ) t + (correction (annularDensity ε δ) t)⁻¹) *
      Real.exp (potential (annularDensity ε δ) t - t) =
        (Real.exp t * annularWindow ε t + δ)⁻¹ := by
  have hc := (contDiff_annularDensity ε δ).continuous
  have hp : ∀ r ∈ Ici (0 : ℝ), 0 < annularDensity ε δ r := fun r _ => annularDensity_pos ε hδ r
  have ha := (antitone_annularDensity hε hδ.le).antitoneOn (s := Ici (0 : ℝ))
  have hd := (contDiff_annularDensity ε δ).differentiable (by simp) t
  refine ⟨curvatureCoefficient_pos hc hp ha ht hd, correction_pos hc hp ha ht hd,
    first_ode hc hp ht, ?_⟩
  simpa only [gain_annularDensity] using sharp_reciprocal_gain hc hp ha ht hd


/-- Smooth density produces smooth actual primitives, by the FTC rather
than by an assumed smoothness certificate. -/
theorem contDiff_mass {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (mass w) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_mass hw.continuous t).differentiableAt, ?_⟩
  have he : deriv (mass w) = w := funext fun t => (hasDerivAt_mass hw.continuous t).deriv
  rwa [he]

theorem contDiff_integratedMass {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (integratedMass w) := contDiff_mass (contDiff_mass hw)

theorem contDiffAt_potential {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (potential w) t := by
  convert ((contDiff_mass hw).contDiffAt.log (mass_pos hw.continuous hpos ht).ne').neg using 1 <;> rfl

theorem contDiffAt_twist {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (twist w) t := by
  exact (contDiff_integratedMass hw).contDiffAt.div (contDiff_mass hw).contDiffAt
    (mass_pos hw.continuous hpos ht).ne'


end SGPT.Trace.OptimalExtensionODE
