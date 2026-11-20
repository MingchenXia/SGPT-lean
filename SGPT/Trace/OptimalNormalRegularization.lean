import SGPT.Trace.OptimalTwistedExhaustion
import SGPT.Trace.OTExt2LocalCalc
import SGPT.Trace.OTExt5Ricci

/-!
# The actual rational normal regularization for optimal extension

The literal scalar normal gives a smooth rational cutoff across the original
fibre and an exact sharp datum identity. This specializes the general
Guan–Zhou cutoff route to the actual one-parameter incidence family.
Blueprint: work/sgpt-resume-20261114/bert-e2-normal-regularization/blueprint/bert-e2-normal-regularization.tex.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNormalRegularization
open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalExtensionCurvature SGPT.Trace.OptimalTwistedExhaustion
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2

/-- The literal regularized logarithmic normal potential, normalized to
zero at radius squared one. -/
def normalLog (ε r : ℝ) : ℝ := Real.log (ε + r) - Real.log (1 + ε)

def normalTime (ε r : ℝ) : ℝ := -normalLog ε r

/-- The actual smooth preliminary-extension multiplier. -/
def normalCutoff (ε r : ℝ) : ℝ := ε / (ε + r)

def normalKernel (ε r : ℝ) : ℝ := ε / (ε + r) ^ 2

def normalDataFactor (ε r : ℝ) : ℝ := ε * r / (ε + r) ^ 2

def normalRadius {n : ℕ} (f : ComplexModel n → ℂ) (z : ComplexModel n) : ℝ := ‖f z‖ ^ 2

theorem normalTime_pos {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 < normalTime ε r := by
  have hlog := Real.log_lt_log (add_pos_of_pos_of_nonneg hε hr) (by linarith : ε + r < 1 + ε)
  dsimp only [normalTime, normalLog]
  linarith

theorem normalTime_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    normalTime ε r ≤ Real.log (1 + ε) - Real.log ε := by
  have hlog := Real.log_le_log hε (by linarith : ε ≤ ε + r)
  dsimp only [normalTime, normalLog]
  linarith

theorem exp_normalTime {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    Real.exp (normalTime ε r) = (1 + ε) / (ε + r) := by
  rw [normalTime, normalLog, neg_sub, Real.exp_sub,
    Real.exp_log (by linarith : 0 < 1 + ε), Real.exp_log (by linarith : 0 < ε + r)]

theorem normalCutoff_zero {ε : ℝ} (hε : 0 < ε) : normalCutoff ε 0 = 1 := by
  simp only [normalCutoff, add_zero, div_self hε.ne']

theorem normalKernel_nonneg {ε r : ℝ} (hε : 0 ≤ ε) : 0 ≤ normalKernel ε r :=
  div_nonneg hε (sq_nonneg _)

theorem normalDataFactor_nonneg {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    0 ≤ normalDataFactor ε r := div_nonneg (mul_nonneg hε hr) (sq_nonneg _)

theorem contDiffAt_normalLog {n : ℕ} {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : ContDiffAt ℝ ∞ R z) {ε : ℝ} (hε : 0 < ε) (hr : 0 ≤ R z) :
    ContDiffAt ℝ ∞ (fun y => normalLog ε (R y)) z :=
  ((contDiffAt_const.add hR).log (by linarith : ε + R z ≠ 0)).sub contDiffAt_const

theorem contDiffAt_normalTime {n : ℕ} {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : ContDiffAt ℝ ∞ R z) {ε : ℝ} (hε : 0 < ε) (hr : 0 ≤ R z) :
    ContDiffAt ℝ ∞ (fun y => normalTime ε (R y)) z :=
  (contDiffAt_normalLog hR hε hr).neg

theorem contDiffAt_normalCutoff {n : ℕ} {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : ContDiffAt ℝ ∞ R z) {ε : ℝ} (hε : 0 < ε) (hr : 0 ≤ R z) :
    ContDiffAt ℝ ∞ (fun y => normalCutoff ε (R y)) z :=
  contDiffAt_const.div (contDiffAt_const.add hR) (by linarith : ε + R z ≠ 0)

theorem hasDerivAt_normalCutoff {ε r : ℝ} (hεr : ε + r ≠ 0) :
    HasDerivAt (normalCutoff ε) (-ε / (ε + r) ^ 2) r := by
  convert (hasDerivAt_const r ε).div ((hasDerivAt_id r).const_add ε) hεr using 1 <;>
    first | rfl | (simp only [zero_mul, mul_one, zero_sub, id_eq])

theorem holDerivSq_normalCutoff {n : ℕ} {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : DifferentiableAt ℝ R z) {ε : ℝ} (hεr : ε + R z ≠ 0) (v : ComplexModel n) :
    holDerivSq (fun y => normalCutoff ε (R y)) z v =
      (ε / (ε + R z) ^ 2) ^ 2 * holDerivSq R z v := by
  rw [holDerivSq_comp (hasDerivAt_normalCutoff hεr).differentiableAt hR,
    (hasDerivAt_normalCutoff hεr).deriv, neg_div, neg_sq]

theorem contDiffAt_normalRadius {n : ℕ} {f : ComplexModel n → ℂ} {O : Set (ComplexModel n)}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {z : ComplexModel n} (hz : z ∈ O) :
    ContDiffAt ℝ ∞ (normalRadius f) z := by
  have hc : ContDiffAt ℝ ∞ f z :=
    (contDiffAt_of_differentiableOn_complex hf hO hz).restrict_scalars ℝ
  have hn : ContDiff ℝ ∞ (fun q : ℂ => ‖q‖ ^ 2) := contDiff_norm_sq ℝ
  exact hn.contDiffAt.comp z hc

theorem leviForm_normalLog {n : ℕ} {R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hR : ContDiffAt ℝ 2 R z) {ε : ℝ} (hε : 0 < ε) (hr : 0 ≤ R z) (v : ComplexModel n) :
    leviForm (fun y => normalLog ε (R y)) z v =
      leviForm (fun y => Real.log (ε + R y)) z v := by
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log (ε + R y)) z :=
    (contDiffAt_const.add hR).log (by linarith : ε + R z ≠ 0)
  have hc : ContDiffAt ℝ 2 (fun _ : ComplexModel n => -Real.log (1 + ε)) z := contDiffAt_const
  have he : (fun y => normalLog ε (R y)) =
      (fun y => Real.log (ε + R y)) + (fun _ : ComplexModel n => -Real.log (1 + ε)) := by
    funext y
    exact sub_eq_add_neg _ _
  rw [he, leviForm_add hlog hc, leviForm_const, add_zero]

/-- The datum identity is for the original holomorphic normal f and
original holomorphic preliminary-section coefficient h. -/
theorem exact_normal_cutoff_datum {n : ℕ} {f h : ComplexModel n → ℂ}
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O)
    {z : ComplexModel n} (hz : z ∈ O) (hfz : f z ≠ 0) (hh : DifferentiableAt ℂ h z)
    {ε : ℝ} (hε : 0 < ε) (v : ComplexModel n) :
    ‖dbarPairing (fun y => h y * (normalCutoff ε (normalRadius f y) : ℂ)) z v‖ ^ 2 =
      normalDataFactor ε (normalRadius f z) * ‖h z‖ ^ 2 *
        leviForm (fun y => normalLog ε (normalRadius f y)) z v := by
  have hR := contDiffAt_normalRadius hO hf hz
  have hr : 0 < normalRadius f z := sq_pos_of_pos (norm_pos_iff.mpr hfz)
  have he : ε + normalRadius f z ≠ 0 := (add_pos hε hr).ne'
  have hlog : leviForm (fun y => Real.log (normalRadius f y)) z v = 0 :=
    SGPT.Trace.OTExt5.leviForm_log_norm_sq_eq_zero
      (by filter_upwards [hO.mem_nhds hz] with y hy; exact (hf y hy).differentiableAt (hO.mem_nhds hy)) hfz v
  have hL := leviForm_log_add (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hr hε v
  rw [hlog, mul_zero, zero_add] at hL
  have hD := holDerivSq_eq_sq_mul_holDerivSq_log
    (hR.differentiableAt (by simp)) (add_pos hε hr) v
  rw [norm_dbarPairing_holo_mul_ofReal_sq hh
      ((contDiffAt_normalCutoff hR hε hr.le).differentiableAt (by simp)),
    holDerivSq_normalCutoff (hR.differentiableAt (by simp)) he,
    leviForm_normalLog (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hε hr.le, hL]
  rw [hD]
  unfold normalDataFactor
  field_simp

/-- The actual annular optimal curvature controls the literal rational
cutoff datum, using only the original base-weight Levi semipositivity. -/
theorem optimal_curvature_controls_cutoff {n : ℕ} {f h : ComplexModel n → ℂ}
    {p₀ : ComplexModel n → ℝ} {O : Set (ComplexModel n)}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {z : ComplexModel n} (hz : z ∈ O)
    (hfz : f z ≠ 0) (hh : DifferentiableAt ℂ h z) (hp : ContDiffAt ℝ 2 p₀ z)
    {σ δ ε : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (hε : 0 < ε)
    (hr1 : normalRadius f z < 1) (v : ComplexModel n) (hLp : 0 ≤ leviForm p₀ z v) :
    ‖dbarPairing (fun y => h y * (normalCutoff ε (normalRadius f y) : ℂ)) z v‖ ^ 2 ≤
      (normalDataFactor ε (normalRadius f z) * ‖h z‖ ^ 2) *
        twistedCurvature
          (localTwist (annularDensity σ δ) (fun y => normalLog ε (normalRadius f y)))
          (localCorrection (annularDensity σ δ) (fun y => normalLog ε (normalRadius f y)))
          (SGPT.Trace.OptimalExtensionCurvature.localWeight (annularDensity σ δ)
            (fun y => normalLog ε (normalRadius f y)) p₀) z v := by
  have hR := contDiffAt_normalRadius hO hf hz
  have hr : 0 < normalRadius f z := sq_pos_of_pos (norm_pos_iff.mpr hfz)
  have hT := normalTime_pos hε hr.le hr1
  have hPsi : ContDiffAt ℝ 2 (fun y => normalLog ε (normalRadius f y)) z :=
    (contDiffAt_normalLog hR hε hr.le).of_le (WithTop.coe_le_coe.mpr le_top)
  have hwpos : ∀ r ∈ Ici (0 : ℝ), 0 < annularDensity σ δ r := fun r _ => annularDensity_pos σ hδ r
  rw [exact_normal_cutoff_datum hO hf hz hfz hh hε v,
    actual_annular_twistedCurvature hσ hδ hPsi hp (neg_pos.mp hT) v]
  have hD : 0 ≤ normalDataFactor ε (normalRadius f z) * ‖h z‖ ^ 2 :=
    mul_nonneg (normalDataFactor_nonneg hε.le hr.le) (sq_nonneg _)
  have hs := twist_pos (contDiff_annularDensity σ δ).continuous hwpos hT
  dsimp only [normalTime] at hs
  nlinarith [mul_nonneg hD (mul_nonneg hs.le hLp)]

/-- The exact scalar coefficient multiplying the original correction norm. -/
def optimalErrorFactor (w : ℝ → ℝ) (ε r : ℝ) : ℝ :=
  Real.exp (-Real.log r - potential w (normalTime ε r)) /
    (twist w (normalTime ε r) + (correction w (normalTime ε r))⁻¹)

theorem exp_neg_potential {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {t : ℝ} (ht : 0 < t) :
    Real.exp (-potential w t) = mass w t := by
  rw [potential, neg_neg, Real.exp_log (mass_pos hw hpos ht)]

theorem optimalErrorFactor_eq {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr1 : r < 1) :
    optimalErrorFactor w ε r = w (normalTime ε r) / r := by
  have ht := normalTime_pos hε hr.le hr1
  have hA := (mass_pos hw.continuous hpos ht).ne'
  have hW := (hpos (normalTime ε r) ht.le).ne'
  rw [optimalErrorFactor, twist_add_reciprocal_correction hw.continuous hpos hanti ht
    (hw.differentiable (by simp) _), sub_eq_add_neg, Real.exp_add,
    exp_neg_potential hw.continuous hpos ht, Real.exp_neg, Real.exp_log hr]
  field_simp

theorem gain_le_optimalErrorFactor {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) (hanti : AntitoneOn w (Ici 0))
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr1 : r < 1) :
    gain w (normalTime ε r) ≤ optimalErrorFactor w ε r := by
  have ht := normalTime_pos hε hr.le hr1
  rw [optimalErrorFactor_eq hw hpos hanti hε hr hr1]
  have he : Real.exp (normalTime ε r) ≤ 1 / r := by
    apply (le_div_iff₀ hr).mpr
    rw [exp_normalTime hε hr.le, div_mul_eq_mul_div, div_le_one (by linarith : 0 < ε + r)]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hr1.le)]
  have h := mul_le_mul_of_nonneg_right he (hpos (normalTime ε r) ht.le).le
  simpa only [gain, one_div, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Before any integration, the original data energy is exactly the
literal rational normal residue kernel times the original primitive mass. -/
theorem exact_normal_data_energy {w : ℝ → ℝ} (hw : Continuous w)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < w r) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hr1 : r < 1) (h : ℂ) :
    normalDataFactor ε r * ‖h‖ ^ 2 *
        Real.exp (-Real.log r - potential w (normalTime ε r)) =
      normalKernel ε r * ‖h‖ ^ 2 * mass w (normalTime ε r) := by
  have ht := normalTime_pos hε hr.le hr1
  rw [sub_eq_add_neg, Real.exp_add, exp_neg_potential hw hpos ht, Real.exp_neg, Real.exp_log hr]
  unfold normalDataFactor normalKernel
  field_simp

/-- The original actual annular primitive yields the sharp finite
normal-data bound, with its exact total mass C0+delta. -/
theorem sharp_normal_data_energy_bound {σ δ ε r : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hε : 0 < ε) (hr : 0 < r) (hr1 : r < 1) (h : ℂ) :
    normalDataFactor ε r * ‖h‖ ^ 2 *
        Real.exp (-Real.log r - potential (annularDensity σ δ) (normalTime ε r)) ≤
      (windowMass σ + δ) * normalKernel ε r * ‖h‖ ^ 2 := by
  have ht := normalTime_pos hε hr.le hr1
  rw [exact_normal_data_energy (contDiff_annularDensity σ δ).continuous
    (fun q _ => annularDensity_pos σ hδ q) hε hr hr1]
  have hmass := mass_annularDensity_le_total hσ hδ ht.le
  have hK : 0 ≤ normalKernel ε r * ‖h‖ ^ 2 :=
    mul_nonneg (normalKernel_nonneg hε.le) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hmass hK]


end SGPT.Trace.OptimalNormalRegularization
