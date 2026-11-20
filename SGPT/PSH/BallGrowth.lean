import SGPT.PSH.LocalL1
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.Pending.PshThreeCircles
import Mathlib.Analysis.Convex.Slope

/-!
# Original logarithmic ball growth

The genuine open-ball supremum is finite and increasing. Existing main Hadamard
three circles bounds strictly smaller endpoint spheres; a one-sided radius limit
gives the exact chord and full convexity, including dimension zero.
-/

namespace SGPT.PSH
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- Exact original Euclidean ball, with the source norm convention. -/
theorem complexModel_ball_eq_norm_lt {n : ℕ} (p : ComplexModel n) (r : ℝ) :
    ball p r = {z : ComplexModel n | ‖z - p‖ < r} := by
  ext z
  simp only [mem_ball, mem_ofPred_eq, dist_eq_norm]

noncomputable def ballSup {n : ℕ} (u : ComplexModel n → EReal)
    (p : ComplexModel n) (r : ℝ) : EReal := ⨆ z ∈ ball p r, u z

theorem ballSup_mono_radius {n : ℕ} (u : ComplexModel n → EReal)
    (p : ComplexModel n) {r s : ℝ} (hrs : r ≤ s) : ballSup u p r ≤ ballSup u p s := by
  apply iSup₂_le
  intro z hz
  exact le_iSup₂ (f := fun z (_ : z ∈ ball p s) ↦ u z) z (ball_subset_ball hrs hz)

/-- The actual original ball supremum is finite, including dimension zero;
finite points and upper bounds are produced by existing source PSH results. -/
theorem PSHOn.ballSup_finite {n : ℕ} {u : ComplexModel n → EReal}
    {p : ComplexModel n} {R r : ℝ} (hu : PSHOn u (ball p R))
    (hr : 0 < r) (hrR : r < R) : ballSup u p r ≠ ⊤ ∧ ballSup u p r ≠ ⊥ := by
  have hR : 0 < R := hr.trans hrR
  have hclosed : closedBall p r ⊆ ball p R := closedBall_subset_ball hrR
  have hraw := hu.disc.plurisubharmonicOn isOpen_ball
  obtain ⟨C, _, hC⟩ := hraw.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall p r) hclosed
  have hupper : ballSup u p r ≤ (C : EReal) :=
    iSup₂_le (fun z hz ↦ hC z (ball_subset_closedBall hz))
  have hfin := hu.ae_finite_on_compact isOpen_ball (isConnected_ball hR).isPreconnected
    volume (isCompact_closedBall p r) hclosed
  obtain ⟨y, hy, hyfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume p hr).ne'
    (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfin)
  refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top C) hupper, ?_⟩
  intro hbot
  have hle : u y ≤ ballSup u p r :=
    le_iSup₂ (f := fun z (_ : z ∈ ball p r) ↦ u z) y hy
  exact hyfin.2 (bot_unique (hbot ▸ hle))

noncomputable def logBallSup {n : ℕ} (u : ComplexModel n → EReal)
    (p : ComplexModel n) (t : ℝ) : ℝ := (ballSup u p (Real.exp t)).toReal

theorem PSHOn.coe_logBallSup {n : ℕ} {u : ComplexModel n → EReal}
    {p : ComplexModel n} {R : ℝ} (hu : PSHOn u (ball p R)) (hR : 0 < R)
    {t : ℝ} (ht : t < Real.log R) :
    (logBallSup u p t : EReal) = ballSup u p (Real.exp t) := by
  have hrR : Real.exp t < R := by
    rw [← Real.exp_log hR]; exact Real.exp_lt_exp.mpr ht
  have hfin := hu.ballSup_finite (Real.exp_pos t) hrR
  exact EReal.coe_toReal hfin.1 hfin.2

theorem PSHOn.monotoneOn_logBallSup {n : ℕ} {u : ComplexModel n → EReal}
    {p : ComplexModel n} {R : ℝ} (hu : PSHOn u (ball p R)) (hR : 0 < R) :
    MonotoneOn (logBallSup u p) (Iio (Real.log R)) := by
  intro s hs t ht hst
  rw [← EReal.coe_le_coe_iff, hu.coe_logBallSup hR hs, hu.coe_logBallSup hR ht]
  exact ballSup_mono_radius u p (Real.exp_le_exp.mpr hst)


/-- The actual open-ball suprema obey the logarithmic chord inequality. The spheres
are strictly inside the original endpoint balls; a genuine one-sided limit removes
the shrinking-radius error. No boundary continuity or maximum certificate is assumed. -/
theorem PSHOn.logBallSup_chord {n : ℕ} {u : ComplexModel n → EReal}
    {p : ComplexModel n} {R : ℝ} (hu : PSHOn u (ball p R)) (hR : 0 < R)
    {s m t : ℝ} (hsm : s < m) (hmt : m < t) (ht : t < Real.log R) :
    logBallSup u p m ≤ logBallSup u p s +
      (m - s) * (logBallSup u p t - logBallSup u p s) / (t - s) := by
  have hs : s < Real.log R := hsm.trans (hmt.trans ht)
  have hm : m < Real.log R := hmt.trans ht
  have hst : s < t := hsm.trans hmt
  have hdiff : 0 ≤ logBallSup u p t - logBallSup u p s :=
    sub_nonneg.mpr (hu.monotoneOn_logBallSup hR hs ht hst.le)
  rw [← EReal.coe_le_coe_iff, hu.coe_logBallSup hR hm]
  apply iSup₂_le
  intro z hz
  have hnz : ‖z - p‖ < Real.exp m := by simpa [mem_ball, dist_eq_norm] using hz
  let A := logBallSup u p s
  let B := logBallSup u p t
  let C : ℝ → ℝ := fun e ↦ A + (m - s + e) * (B - A) / (t - s)
  have hlim : Tendsto (fun e : ℝ ↦ (C e : EReal)) (𝓝[>] 0)
      (𝓝 ((A + (m - s) * (B - A) / (t - s) : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    have hc : Continuous C := by dsimp [C]; fun_prop
    simpa [C] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] 0, e < t - m :=
    (eventually_lt_nhds (sub_pos.mpr hmt)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with e he0 he
  have hepos : 0 < e := he0
  have hAC : A ≤ C e := by
    dsimp [C, A, B]
    apply le_add_of_nonneg_right
    exact div_nonneg (mul_nonneg (by linarith) hdiff) (sub_pos.mpr hst).le
  by_cases hzinner : ‖z - p‖ < Real.exp s
  · have hzball : z ∈ ball p (Real.exp s) := by simpa [mem_ball, dist_eq_norm] using hzinner
    have hzu : u z ≤ (A : EReal) := by
      rw [show (A : EReal) = ballSup u p (Real.exp s) from hu.coe_logBallSup hR hs]
      exact le_iSup₂ (f := fun z (_ : z ∈ ball p (Real.exp s)) ↦ u z) z hzball
    exact hzu.trans (EReal.coe_le_coe_iff.mpr hAC)
  · have hnpos : 0 < ‖z - p‖ := (Real.exp_pos s).trans_le (le_of_not_gt hzinner)
    have hr1 : Real.exp (s - e) < ‖z - p‖ :=
      (Real.exp_lt_exp.mpr (by linarith)).trans_le (le_of_not_gt hzinner)
    have hr3 : ‖z - p‖ < Real.exp (t - e) :=
      hnz.trans (Real.exp_lt_exp.mpr (by linarith))
    have hraw := hu.disc.plurisubharmonicOn isOpen_ball
    have hclosed : closedBall p (Real.exp (t - e)) ⊆ ball p R := by
      apply closedBall_subset_ball
      rw [← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h1 : ∀ w, ‖w - p‖ = Real.exp (s - e) → u w ≤ (A : EReal) := by
      intro w hw
      rw [show (A : EReal) = ballSup u p (Real.exp s) from hu.coe_logBallSup hR hs]
      apply le_iSup₂ (f := fun z (_ : z ∈ ball p (Real.exp s)) ↦ u z) w
      simp only [mem_ball, dist_eq_norm, hw]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h3 : ∀ w, ‖w - p‖ = Real.exp (t - e) → u w ≤ (B : EReal) := by
      intro w hw
      rw [show (B : EReal) = ballSup u p (Real.exp t) from hu.coe_logBallSup hR ht]
      apply le_iSup₂ (f := fun z (_ : z ∈ ball p (Real.exp t)) ↦ u z) w
      simp only [mem_ball, dist_eq_norm, hw]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hc := SGPT.Foundations.Analysis.Pending.PshThreeCircles.le_log_interpolation hraw
      (Real.exp_pos (s - e)) (Real.exp_lt_exp.mpr (by linarith : s - e < t - e))
      hclosed h1 h3 hr1.le hr3.le
    simp only [Real.log_exp] at hc
    apply hc.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hlog : Real.log ‖z - p‖ < m := (Real.log_lt_iff_lt_exp hnpos).mpr hnz
    dsimp [C]
    apply add_le_add le_rfl
    have hden : t - e - (s - e) = t - s := by ring
    rw [hden]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hst).le
    apply mul_le_mul_of_nonneg_right _ hdiff
    linarith

/-- Exact convexity of the actual original logarithmic ball supremum, including
zero dimensions without a punctured-sphere premise. -/
theorem PSHOn.convexOn_logBallSup {n : ℕ} {u : ComplexModel n → EReal}
    {p : ComplexModel n} {R : ℝ} (hu : PSHOn u (ball p R)) (hR : 0 < R) :
    ConvexOn ℝ (Iio (Real.log R)) (logBallSup u p) := by
  apply convexOn_of_slope_mono_adjacent (convex_Iio (Real.log R))
  intro s m t hs ht hsm hmt
  have hc := hu.logBallSup_chord hR hsm hmt ht
  apply (div_le_div_iff₀ (sub_pos.mpr hsm) (sub_pos.mpr hmt)).mpr
  have hst : 0 < t - s := sub_pos.mpr (hsm.trans hmt)
  have hchord : (logBallSup u p m - logBallSup u p s) * (t - s) ≤
      (m - s) * (logBallSup u p t - logBallSup u p s) := by
    apply (le_div_iff₀ hst).mp
    linarith
  nlinarith

end SGPT.PSH
