import SGPT.Foundations.Analysis.Pending.DivisorialSliceBound
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance

set_option autoImplicit false

/-! # Divisorial growth for an actual raw quasi-PSH germ

The actual local PSH-plus-smooth decomposition and three-circle hyperplane
estimate internally provide a growth bound below the literal local generic
reader. No background form, analytic type, nondegeneracy or mass is required.
This local piece is not identified with all global prime divisors here.
Reference: Copy-4, domination lemma, local slice proof; supplementary raw-germ
adaptation of the divisorial argument in Xia's valuative discussion.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshDivisorialSliceBound

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

/-- A raw quasi-PSH germ internally supplies a finite logarithmic growth bound
below its literal hyperplane point infimum, including identically bot germs. -/
theorem exists_slice_bound {m : ℕ} {u : ComplexModel (m + 1) → EReal}
    (hu : QuasiPlurisubharmonicAt u 0) {R : ℝ} (hR : 0 < R) {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) < ⨅ q ∈ ball (0 : ComplexModel (m + 1)) R ∩
      {q | q (Fin.last m) = 0}, lelongNumber (n := m + 1) u q) :
    ∃ (r : ℝ), 0 < r ∧ r ≤ R ∧ ∃ C : ℝ, ∀ z ∈ ball (0 : ComplexModel (m + 1)) r,
      z (Fin.last m) ≠ 0 →
        u z ≤ (((γ : ℝ) * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal) := by
  obtain ⟨P, h, ⟨W, hW, h0W, hP⟩, hh, heq⟩ := hu
  have hPpsh : PlurisubharmonicOn P W := hP.plurisubharmonicOn hW
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (z ∈ W ∧ u z = P z + (h z : EReal)) ∧ ContDiffAt ℝ ∞ h z :=
    ((show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ W from
      hW.mem_nhds h0W).and heq).and hh
  obtain ⟨R₀, hR₀, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hsub : closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) ⊆ ball 0 R₀ :=
    closedBall_subset_ball (by linarith)
  have hhcont : ContinuousOn h (closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)) :=
    fun z hz => ((hball (hsub hz)).2.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)).exists_bound_of_continuousOn hhcont
  have hhM : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2), |h z| ≤ M :=
    fun z hz => by simpa only [Real.norm_eq_abs] using hM z hz
  let r : ℝ := min (R / 2) (R₀ / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r ≤ R := (min_le_left _ _).trans (by linarith)
  have hrR₀ : r ≤ R₀ / 4 := min_le_right _ _
  have hdouble : closedBall (0 : ComplexModel (m + 1)) (2 * r) ⊆
      closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) :=
    closedBall_subset_closedBall (by linarith)
  have hΩ : closedBall (0 : ComplexModel (m + 1)) (2 * r) ⊆ W :=
    fun z hz => (hball (hsub (hdouble hz))).1.1
  obtain ⟨K, _, hK⟩ := hPpsh.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall (0 : ComplexModel (m + 1)) (2 * r)) hΩ
  have hsmall : ball (0 : ComplexModel (m + 1)) r ⊆
      closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) :=
    fun z hz => ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  have hν : ∀ q ∈ ball (0 : ComplexModel (m + 1)) r, q (Fin.last m) = 0 →
      (γ : ℝ≥0∞) < lelongNumber (n := m + 1) P q := by
    intro q hq hq0
    have hqbig : q ∈ ball (0 : ComplexModel (m + 1)) R₀ := hsub (hsmall hq)
    have hgerm : u =ᶠ[𝓝 q] fun z => P z + (h z : EReal) :=
      (show ∀ᶠ z in 𝓝 q, z ∈ ball (0 : ComplexModel (m + 1)) R₀ from
        isOpen_ball.mem_nhds hqbig).mono fun z hz => (hball hz).1.2
    have heqν : lelongNumber (n := m + 1) u q = lelongNumber (n := m + 1) P q := by
      rw [LelongNumberComparison.lelongNumber_congr hgerm,
        LelongChartReaderInvariance.lelongNumber_add_continuous_eq
          (hball hqbig).2.continuousAt]
    rw [← heqν]
    exact hγ.trans_le (iInf₂_le q ⟨ball_subset_ball hrR hq, hq0⟩)
  refine ⟨r, hr, hrR, K - (γ : ℝ) * Real.log r + M, fun z hz hz0 => ?_⟩
  have hPz := DivisorialSliceBound.le_log_last_add_of_lt_lelongNumber
    hPpsh (p := (0 : ComplexModel (m + 1))) (by simp) hΩ hK hν hz hz0
  rw [(hball (hsub (hsmall hz))).1.2]
  calc
    P z + (h z : EReal) ≤
        (((γ : ℝ) * Real.log ‖z (Fin.last m)‖ + (K - (γ : ℝ) * Real.log r) : ℝ) : EReal) +
          (M : EReal) :=
      add_le_add hPz (EReal.coe_le_coe_iff.mpr (abs_le.mp (hhM z (hsmall hz))).2)
    _ = _ := by rw [← EReal.coe_add]; congr 1; ring

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshDivisorialSliceBound
