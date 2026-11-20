import SGPT.Foundations.Analysis.Pending.ScaledSmoothMax

/-!
# Genuine convex cutoffs for the strict comparison set

The regularization is flat on the entire negative half-line, so its
derivative converges to `1_{t>0}` also at `t=0`. This avoids any assumption
that the two distinguished Bedford--Taylor factors have no mass on their
coincidence set.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonPositivePart

open Set Filter SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SmoothMax
open scoped Topology ContDiff

/-- The scale-`ε` smooth convex positive part, flat for `t≤0`. -/
def cutoff (ε t : ℝ) : ℝ := ε * SmoothMax.posPart (t / ε - 1)

theorem contDiff_cutoff (ε : ℝ) : ContDiff ℝ ∞ (cutoff ε) :=
  (contDiff_posPart.comp ((contDiff_id.div_const ε).sub (contDiff_const (c := (1 : ℝ))))).const_smul ε

theorem hasDerivAt_cutoff {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (cutoff ε) (trans (t / ε - 1)) t := by
  have h := ((hasDerivAt_posPart (t / ε - 1)).comp t
    ((hasDerivAt_id t).div_const ε |>.sub_const 1)).const_mul ε
  have hc : ε * (trans (t / ε - 1) * (1 / ε)) = trans (t / ε - 1) := by
    field_simp
  change HasDerivAt (cutoff ε) (ε * (trans (t / ε - 1) * (1 / ε))) t at h
  rwa [hc] at h

theorem deriv_cutoff {ε : ℝ} (hε : 0 < ε) :
    deriv (cutoff ε) = fun t => trans (t / ε - 1) :=
  funext fun t => (hasDerivAt_cutoff hε t).deriv

theorem cutoff_secondDeriv_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (cutoff ε)) t := by
  rw [deriv_cutoff hε]
  have h := ((contDiff_trans.differentiable (by simp) _).hasDerivAt.comp t
    ((hasDerivAt_id t).div_const ε |>.sub_const 1)).deriv
  change 0 ≤ deriv (trans ∘ fun x : ℝ => id x / ε - 1) t
  rw [h]
  exact mul_nonneg (trans_monotone.deriv_nonneg) (one_div_nonneg.mpr hε.le)

theorem deriv_cutoff_mem_Icc {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (cutoff ε) t ∈ Icc 0 1 := by
  rw [deriv_cutoff hε]
  exact ⟨trans_nonneg _, trans_le_one _⟩

theorem cutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) :
    cutoff ε t = 0 := by
  rw [cutoff, posPart_eq_zero (by have := div_nonpos_of_nonpos_of_nonneg ht hε.le; linarith),
    mul_zero]

theorem deriv_cutoff_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) :
    deriv (cutoff ε) t = 0 := by
  rw [deriv_cutoff hε]
  exact trans_eq_zero (by have := div_nonpos_of_nonpos_of_nonneg ht hε.le; linarith)

theorem deriv_cutoff_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε ≤ t) :
    deriv (cutoff ε) t = 1 := by
  rw [deriv_cutoff hε]
  apply trans_eq_one
  have := (le_div_iff₀ hε).mpr ht
  linarith

theorem cutoff_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    max t 0 - ε ≤ cutoff ε t ∧ cutoff ε t ≤ max t 0 + ε := by
  have he : cutoff ε t = ScaledSmoothMax.scaledSmoothMax ε
      (fun s : ℝ => s - ε) (fun _ => 0) t := by
    simp only [cutoff, ScaledSmoothMax.scaledSmoothMax_apply, sub_zero, zero_add]
    congr 2
    field_simp
  rw [he]
  have h := ScaledSmoothMax.max_le_scaledSmoothMax_le_max_add hε
    (fun s : ℝ => s - ε) (fun _ => 0) t
  constructor
  · have hm : max t 0 ≤ max (t - ε) 0 + ε := by
      apply max_le
      · linarith [le_max_left (t - ε) 0]
      · linarith [le_max_right (t - ε) 0]
    linarith [h.1]
  · exact h.2.trans (add_le_add (max_le_max (by linarith : t - ε ≤ t) le_rfl) (le_refl ε))

def scale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_tendsto (t : ℝ) :
    Tendsto (fun j => cutoff (scale j) t) atTop (𝓝 (max t 0)) := by
  have hl : Tendsto (fun j => max t 0 - scale j) atTop (𝓝 (max t 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub scale_tendsto
  have hu : Tendsto (fun j => max t 0 + scale j) atTop (𝓝 (max t 0)) := by
    simpa only [add_zero] using tendsto_const_nhds.add scale_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro j
    exact (cutoff_bounds (scale_pos j) t).1
  · intro j
    exact (cutoff_bounds (scale_pos j) t).2

theorem deriv_cutoff_tendsto (t : ℝ) :
    Tendsto (fun j => deriv (cutoff (scale j)) t) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  by_cases ht : 0 < t
  · rw [if_pos ht]
    apply tendsto_const_nhds.congr'
    have hsmall : ∀ᶠ j in atTop, scale j < t / 2 :=
      (tendsto_order.1 scale_tendsto).2 _ (by linarith)
    filter_upwards [hsmall] with j hj
    exact (deriv_cutoff_eq_one (scale_pos j) (by linarith)).symm
  · rw [if_neg ht]
    have hz : ∀ j, deriv (cutoff (scale j)) t = 0 :=
      fun j => deriv_cutoff_eq_zero (scale_pos j) (not_lt.mp ht)
    simp only [hz]
    exact tendsto_const_nhds

end SGPT.PSH.HermitianComparisonPositivePart
