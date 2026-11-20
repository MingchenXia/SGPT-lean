import SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

/-! # Actual all-point Bergman Lelong lower error

Demailly, Analytic Methods, Theorem 14.2(b), via actual admissible growth
and the Haar volume of a ball avoiding the original center.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.BergmanPointLelongLowerBound

open FirstPass FirstPass.NonKahlerLocus BergmanWeightConvergence LelongNumberChartTransport

noncomputable section

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

private theorem log_volume_half_ball (y : ComplexModel n) {t : ℝ} (ht : 0 < t) :
    Real.log (volume (ball y (t / 2))).toReal =
      2 * (n : ℝ) * Real.log t - 2 * (n : ℝ) * Real.log 2 +
        Real.log (volume (ball (0 : ComplexModel n) 1)).toReal := by
  have hdim : Module.finrank ℝ (ComplexModel n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hV : 0 < (volume (ball (0 : ComplexModel n) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne'
      measure_ball_lt_top.ne
  rw [Measure.addHaar_ball_of_pos volume y (by positivity : 0 < t / 2),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    Real.log_mul (by positivity) hV.ne', Real.log_pow,
    Real.log_div ht.ne' (by norm_num : (2 : ℝ) ≠ 0), hdim]
  push_cast
  ring

private theorem exists_bergman_log_growth {D : Set (ComplexModel n)} (hD : IsOpen D)
    {x : ComplexModel n} (hx : x ∈ D) {P : ComplexModel n → EReal}
    {m : ℕ} (hm : 1 ≤ m) {γ C : ℝ} (hγ : 0 ≤ γ)
    (hadm : ∀ᶠ y in 𝓝[≠] x, P y ≤ ((γ * Real.log ‖y - x‖ + C : ℝ) : EReal)) :
    ∃ C' : ℝ, ∀ᶠ y in 𝓝[≠] x,
      bergmanWeight D P m y ≤
        (((γ - 2 * (n : ℝ) / (m : ℝ)) * Real.log ‖y - x‖ + C' : ℝ) : EReal) := by
  obtain ⟨R, hR, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hadm
  obtain ⟨S, hS, hSsub⟩ := Metric.isOpen_iff.mp hD x hx
  let r : ℝ := min R S / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let L : ℝ := Real.log (volume (ball (0 : ComplexModel n) 1)).toReal
  refine ⟨γ * Real.log 2 + C + (m : ℝ)⁻¹ * (2 * (n : ℝ) * Real.log 2 - L), ?_⟩
  have hball : ∀ᶠ y in 𝓝 x, y ∈ ball x r := ball_mem_nhds x hr
  filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hne
  have hyne : y ≠ x := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  let t : ℝ := ‖y - x‖
  have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
  have hty : t < r := by simpa only [t, mem_ball, dist_eq_norm] using hy
  have htR : 2 * t < R := by
    have hmin := min_le_left R S
    dsimp only [r] at hty
    linarith
  have htS : 2 * t < S := by
    have hmin := min_le_right R S
    dsimp only [r] at hty
    linarith
  have hsub : closedBall y (t / 2) ⊆ D := by
    intro z hz
    apply hSsub
    rw [mem_ball, dist_eq_norm]
    have hzy : ‖z - y‖ ≤ t / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have htri : ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (z - y) (y - x)
    change ‖z - x‖ < S
    change ‖z - x‖ ≤ ‖z - y‖ + t at htri
    linarith
  have hb : ∀ z ∈ ball y (t / 2), P z ≤ ((γ * Real.log (2 * t) + C : ℝ) : EReal) := by
    intro z hz
    have hzy : ‖z - y‖ < t / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hzx : z ≠ x := by
      intro heq
      subst z
      have : ‖x - y‖ = t := by simp only [t, norm_sub_rev]
      rw [this] at hzy
      linarith
    have hzpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    have htri : ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (z - y) (y - x)
    change ‖z - x‖ ≤ ‖z - y‖ + t at htri
    have hz2 : ‖z - x‖ < 2 * t := by linarith
    have hzR : z ∈ ball x R := by rw [mem_ball, dist_eq_norm]; exact hz2.trans htR
    have hraw := hbound ⟨hzR, by simpa only [mem_compl_iff, mem_singleton_iff] using hzx⟩
    refine hraw.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hlog : Real.log ‖z - x‖ ≤ Real.log (2 * t) := Real.log_le_log hzpos hz2.le
    exact add_le_add (mul_le_mul_of_nonneg_left hlog hγ) le_rfl
  have hupper := bergmanWeight_le hD hm (by positivity : 0 < t / 2) hsub hb
  have heq : γ * Real.log (2 * t) + C -
      (m : ℝ)⁻¹ * Real.log (volume (ball y (t / 2))).toReal =
      (γ - 2 * (n : ℝ) / (m : ℝ)) * Real.log ‖y - x‖ +
        (γ * Real.log 2 + C + (m : ℝ)⁻¹ * (2 * (n : ℝ) * Real.log 2 - L)) := by
    rw [log_volume_half_ball y ht, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
    dsimp only [L, t]
    ring
  rwa [heq] at hupper

/-- Actual all-point lower error, from the extremal kernel and Haar scaling.
The original weight and both extended growth readers are never realified. -/
theorem lelongNumber_le_bergmanWeight_add_error {D : Set (ComplexModel n)}
    (hD : IsOpen D) {x : ComplexModel n} (hx : x ∈ D)
    (P : ComplexModel n → EReal) {m : ℕ} (hm : 1 ≤ m) :
    lelongNumber (n := n) P x ≤
      lelongNumber (n := n) (bergmanWeight D P m) x +
        ENNReal.ofReal (2 * (n : ℝ) / (m : ℝ)) := by
  let v : ℝ≥0∞ := lelongNumber (n := n) (bergmanWeight D P m) x
  let e : ℝ := 2 * (n : ℝ) / (m : ℝ)
  have he : 0 ≤ e := by dsimp [e]; positivity
  change lelongNumber (n := n) P x ≤ v + ENNReal.ofReal e
  unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨C, hC⟩ := hγ
  have hadm : ∀ᶠ y in 𝓝[≠] x, P y ≤ (((γ : ℝ) * Real.log ‖y - x‖ + C : ℝ) : EReal) := by
    simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hC
  by_cases hγe : e ≤ (γ : ℝ)
  · obtain ⟨C', hC'⟩ := exists_bergman_log_growth hD hx hm γ.coe_nonneg hadm
    have htarget : ENNReal.ofReal ((γ : ℝ) - e) ≤ v := by
      apply ofReal_le_lelongNumber (sub_nonneg.mpr hγe)
      simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
        id_eq, e] using hC'
    calc
      (γ : ℝ≥0∞) = ENNReal.ofReal ((γ : ℝ) - e) + ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (sub_nonneg.mpr hγe) he]
        simp only [sub_add_cancel, ENNReal.ofReal_coe_nnreal]
      _ ≤ v + ENNReal.ofReal e := add_le_add htarget le_rfl
  · calc
      (γ : ℝ≥0∞) = ENNReal.ofReal (γ : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (le_of_not_ge hγe)
      _ ≤ v + ENNReal.ofReal e := le_add_left le_rfl

end
end SGPT.Foundations.Analysis.Pending.BergmanPointLelongLowerBound
