import SGPT.PSH.GlobalL2PoleTransfer
import SGPT.Foundations.Analysis.Pending.LogCutoffLevi
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A cut-off logarithmic pole in a ball, with a Levi lower bound uniform in the centre

Blueprint `claude-global-l2b.tex`, node `claude-global-l2b:profile`.

The profile `poleProfile t = t (1 - σ t) + σ t` (`σ = Real.smoothTransition`) is smooth,
nondecreasing, equal to `t` for `t ≤ 0` and to `1` for `t ≥ 1`; its second derivative vanishes
off `[0, 1]` and is bounded there.  For a centre `p` and `a = log r²` the chart function

`poleSmooth p a z = poleProfile (log ‖z - p‖² - a) + a`

equals `log ‖z - p‖²` on `‖z - p‖ ≤ r`, is constant (`= 1 + a`) on `‖z - p‖ ≥ 2r`, and off `p`
its Levi form is at least `-(2K / r²) ‖v‖²` (`leviForm_poleSmooth_ge`), with `K` the bound of
`|poleProfile''|`, **independent of `p`**.  (Chain rule
`L(g ∘ ℓ)(v) = g''(ℓ)(dℓ(v)² + dℓ(iv)²)/4 + g'(ℓ) L(ℓ)(v)`, `L(log ‖· - p‖²) ≥ 0`, `g' ≥ 0`, and
`|dℓ(v)| ≤ 2‖v‖/‖z - p‖` with `‖z - p‖ ≥ r` where `g''(ℓ) ≠ 0`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-! ### The profile -/

/-- The profile `t (1 - σ t) + σ t`. -/
def poleProfile (t : ℝ) : ℝ := t * (1 - Real.smoothTransition t) + Real.smoothTransition t

theorem contDiff_poleProfile : ContDiff ℝ ∞ poleProfile := by
  unfold poleProfile
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact (contDiff_id.mul (contDiff_const.sub hσ)).add hσ

theorem poleProfile_of_nonpos {t : ℝ} (ht : t ≤ 0) : poleProfile t = t := by
  simp [poleProfile, Real.smoothTransition.zero_of_nonpos ht]

theorem poleProfile_of_one_le {t : ℝ} (ht : 1 ≤ t) : poleProfile t = 1 := by
  simp [poleProfile, Real.smoothTransition.one_of_one_le ht]

theorem poleProfile_eventuallyEq_of_neg {t : ℝ} (ht : t < 0) : poleProfile =ᶠ[𝓝 t] id := by
  filter_upwards [Iio_mem_nhds ht] with s hs using poleProfile_of_nonpos (le_of_lt hs)

theorem poleProfile_eventuallyEq_of_one_lt {t : ℝ} (ht : 1 < t) :
    poleProfile =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs using poleProfile_of_one_le (le_of_lt hs)

theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  exact Real.smoothTransition.monotone.deriv_nonneg

theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using Real.smoothTransition.one_of_one_le hs.le
  rw [h.deriv_eq, deriv_const]

theorem hasDerivAt_poleProfile (t : ℝ) :
    HasDerivAt poleProfile ((1 - Real.smoothTransition t) +
      (1 - t) * deriv Real.smoothTransition t) t := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hσ := (hd t).hasDerivAt
  have h : HasDerivAt (fun x => x * (1 - Real.smoothTransition x) + Real.smoothTransition x)
      (1 * (1 - Real.smoothTransition t) + t * (0 - deriv Real.smoothTransition t) +
        deriv Real.smoothTransition t) t :=
    ((hasDerivAt_id' t).mul ((hasDerivAt_const t (1 : ℝ)).sub hσ)).add hσ
  exact h.congr_deriv (by ring)

theorem deriv_poleProfile_nonneg (t : ℝ) : 0 ≤ deriv poleProfile t := by
  rw [(hasDerivAt_poleProfile t).deriv]
  have h1 : 0 ≤ 1 - Real.smoothTransition t := sub_nonneg.mpr (Real.smoothTransition.le_one t)
  rcases le_or_gt t 1 with ht | ht
  · have := mul_nonneg (sub_nonneg.mpr ht) (deriv_smoothTransition_nonneg t)
    linarith
  · rw [deriv_smoothTransition_of_one_lt ht, mul_zero, add_zero]
    exact h1

theorem monotone_poleProfile : Monotone poleProfile :=
  monotone_of_deriv_nonneg (contDiff_poleProfile.differentiable (by simp)) deriv_poleProfile_nonneg

theorem poleProfile_le_one (t : ℝ) : poleProfile t ≤ 1 := by
  rcases le_or_gt t 1 with ht | ht
  · calc poleProfile t ≤ poleProfile 1 := monotone_poleProfile ht
      _ = 1 := poleProfile_of_one_le le_rfl
  · rw [poleProfile_of_one_le ht.le]

theorem deriv2_poleProfile_eq_zero {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    deriv (deriv poleProfile) t = 0 := by
  rcases lt_or_ge t 0 with h0 | h0
  · have h : deriv poleProfile =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds h0] with s hs
      rw [(poleProfile_eventuallyEq_of_neg hs).deriv_eq]
      exact deriv_id s
    rw [h.deriv_eq, deriv_const]
  · have h1 : 1 < t := by
      by_contra hle
      exact ht ⟨h0, not_lt.mp hle⟩
    have h : deriv poleProfile =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h1] with s hs
      rw [(poleProfile_eventuallyEq_of_one_lt hs).deriv_eq, deriv_const]
    rw [h.deriv_eq, deriv_const]

/-- `|poleProfile''| ≤ K` everywhere. -/
theorem exists_bound_deriv2_poleProfile :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv (deriv poleProfile) t| ≤ K := by
  have hc : Continuous (deriv (deriv poleProfile)) := by
    have h1 := (contDiff_infty_iff_deriv.mp contDiff_poleProfile).2
    exact ((contDiff_infty_iff_deriv.mp h1).2).continuous
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨|K|, abs_nonneg K, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have := hK t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self K)
  · rw [deriv2_poleProfile_eq_zero ht, abs_zero]
    exact abs_nonneg K

/-- The bound of `|poleProfile''|`. -/
def poleK : ℝ := exists_bound_deriv2_poleProfile.choose

theorem poleK_nonneg : 0 ≤ poleK := exists_bound_deriv2_poleProfile.choose_spec.1

theorem abs_deriv2_poleProfile_le (t : ℝ) : |deriv (deriv poleProfile) t| ≤ poleK :=
  exists_bound_deriv2_poleProfile.choose_spec.2 t

/-! ### The chart function -/

variable {n : ℕ}

/-- The chart function `poleProfile (log ‖z - p‖² - a) + a`. -/
def poleSmooth (p : ComplexModel n) (a : ℝ) (z : ComplexModel n) : ℝ :=
  poleProfile (Real.log (‖z - p‖ ^ 2) - a) + a

theorem contDiffAt_logNormSq_sub {p z : ComplexModel n} (hz : z ≠ p) :
    ContDiffAt ℝ ∞ (fun y => Real.log (‖y - p‖ ^ 2)) z := by
  have hpos : ‖z - p‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    positivity
  exact (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt).log hpos

theorem contDiffAt_poleSmooth {p z : ComplexModel n} (a : ℝ) (hz : z ≠ p) :
    ContDiffAt ℝ ∞ (poleSmooth p a) z :=
  (contDiff_poleProfile.contDiffAt.comp z
    ((contDiffAt_logNormSq_sub hz).sub contDiffAt_const)).add contDiffAt_const

theorem contDiffOn_poleSmooth (p : ComplexModel n) (a : ℝ) :
    ContDiffOn ℝ ∞ (poleSmooth p a) {z | z ≠ p} := fun _ hz =>
  (contDiffAt_poleSmooth a hz).contDiffWithinAt

theorem continuousOn_poleSmooth (p : ComplexModel n) (a : ℝ) :
    ContinuousOn (poleSmooth p a) {z | z ≠ p} :=
  (contDiffOn_poleSmooth p a).continuousOn

theorem poleSmooth_eq_log {p z : ComplexModel n} {r : ℝ} (hz : z ≠ p)
    (hzr : ‖z - p‖ ≤ r) : poleSmooth p (Real.log (r ^ 2)) z = Real.log (‖z - p‖ ^ 2) := by
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hle : Real.log (‖z - p‖ ^ 2) ≤ Real.log (r ^ 2) :=
    Real.log_le_log (by positivity) (pow_le_pow_left₀ hpos.le hzr 2)
  rw [poleSmooth, poleProfile_of_nonpos (by linarith)]
  ring

theorem poleSmooth_eq_const {p z : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hzr : 2 * r ≤ ‖z - p‖) : poleSmooth p (Real.log (r ^ 2)) z = 1 + Real.log (r ^ 2) := by
  have hpos : 0 < ‖z - p‖ := lt_of_lt_of_le (by linarith) hzr
  have h4 : 4 * r ^ 2 ≤ ‖z - p‖ ^ 2 := by nlinarith
  have hlog : 1 ≤ Real.log (‖z - p‖ ^ 2) - Real.log (r ^ 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h4' : 4 ≤ ‖z - p‖ ^ 2 / r ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (‖z - p‖ ^ 2 / r ^ 2) :=
          Real.log_le_log (Real.exp_pos 1) (he.trans h4')
  rw [poleSmooth, poleProfile_of_one_le hlog]

theorem poleSmooth_le (p : ComplexModel n) (a : ℝ) (z : ComplexModel n) :
    poleSmooth p a z ≤ 1 + a := by
  have := poleProfile_le_one (Real.log (‖z - p‖ ^ 2) - a)
  rw [poleSmooth]; linarith

theorem log_le_poleSmooth {p z : ComplexModel n} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hz : ρ ≤ ‖z - p‖) : Real.log (ρ ^ 2) ≤ poleSmooth p (Real.log (r ^ 2)) z := by
  have hlog : Real.log (ρ ^ 2) ≤ Real.log (‖z - p‖ ^ 2) :=
    Real.log_le_log (by positivity) (pow_le_pow_left₀ hρ.le hz 2)
  have hρr' : Real.log (ρ ^ 2) ≤ Real.log (r ^ 2) :=
    Real.log_le_log (by positivity) (pow_le_pow_left₀ hρ.le hρr 2)
  have hmono := monotone_poleProfile (show Real.log (ρ ^ 2) - Real.log (r ^ 2) ≤
    Real.log (‖z - p‖ ^ 2) - Real.log (r ^ 2) by linarith)
  rw [poleProfile_of_nonpos (by linarith)] at hmono
  rw [poleSmooth]; linarith

/-! ### The Levi lower bound -/

theorem hasFDerivAt_logNormSq_sub {p z : ComplexModel n} (hz : z ≠ p) :
    HasFDerivAt (fun y => Real.log (‖y - p‖ ^ 2))
      ((‖z - p‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (z - p)).comp (ContinuousLinearMap.id ℝ _))) z := by
  have hpos : ‖z - p‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
    positivity
  have h1 : HasFDerivAt (fun y : ComplexModel n => y - p) (ContinuousLinearMap.id ℝ _) z :=
    (hasFDerivAt_id z).sub_const p
  exact h1.norm_sq.log hpos

theorem fderiv_logNormSq_sub_sq_le {p z : ComplexModel n} (hz : z ≠ p) (v : ComplexModel n) :
    (fderiv ℝ (fun y => Real.log (‖y - p‖ ^ 2)) z v) ^ 2 ≤ 4 * ‖v‖ ^ 2 / ‖z - p‖ ^ 2 := by
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [(hasFDerivAt_logNormSq_sub hz).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  have hcs := abs_real_inner_le_norm (z - p) v
  have hsq : (inner ℝ (z - p) v) ^ 2 ≤ (‖z - p‖ * ‖v‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [le_div_iff₀ (by positivity)]
  have hne : ‖z - p‖ ^ 2 ≠ 0 := by positivity
  have : ((‖z - p‖ ^ 2)⁻¹ * (2 • inner ℝ (z - p) v)) ^ 2 * ‖z - p‖ ^ 2 =
      4 * (inner ℝ (z - p) v) ^ 2 / ‖z - p‖ ^ 2 := by
    rw [nsmul_eq_mul]; field_simp; ring
  rw [this, div_le_iff₀ (by positivity)]
  nlinarith [hsq]

theorem leviForm_logNormSq_sub_nonneg {p z : ComplexModel n} (hz : z ≠ p) (v : ComplexModel n) :
    0 ≤ leviForm (fun y => Real.log (‖y - p‖ ^ 2)) z v := by
  have h := Pending.LogCutoffLevi.leviForm_log_normSq_nonneg
    (ContinuousLinearMap.id ℂ (ComplexModel n)) (z := z - p) (sub_ne_zero.mpr hz) v
  rw [← Pending.LocalBedfordTaylorCollar.leviForm_comp_sub_const] at h
  simpa using h

/-- **The Levi lower bound, uniform in the centre.** -/
theorem leviForm_poleSmooth_ge {p z : ComplexModel n} {r : ℝ} (hr : 0 < r) (hz : z ≠ p)
    (v : ComplexModel n) :
    -(2 * poleK / r ^ 2 * ‖v‖ ^ 2) ≤ leviForm (poleSmooth p (Real.log (r ^ 2))) z v := by
  set a := Real.log (r ^ 2) with ha
  set ℓ : ComplexModel n → ℝ := fun y => Real.log (‖y - p‖ ^ 2) - a with hℓ
  have hℓ2 : ContDiffAt ℝ 2 ℓ z :=
    ((contDiffAt_logNormSq_sub hz).sub contDiffAt_const).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hfun : poleSmooth p a = (fun y => poleProfile (ℓ y)) + fun _ => a := by
    funext y; simp [poleSmooth, hℓ]
  have hg2 : ContDiffAt ℝ 2 (fun y => poleProfile (ℓ y)) z :=
    (contDiff_poleProfile.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      z hℓ2
  rw [hfun, leviForm_add hg2 contDiffAt_const, leviForm_const, add_zero,
    Pending.LogCutoffLevi.leviForm_comp contDiff_poleProfile hℓ2]
  -- the second term is nonnegative
  have hL : 0 ≤ leviForm ℓ z v := by
    have hfun' : ℓ = (fun y => Real.log (‖y - p‖ ^ 2)) + fun _ => -a := by
      funext y; simp [hℓ, sub_eq_add_neg]
    rw [hfun', leviForm_add ((contDiffAt_logNormSq_sub hz).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) contDiffAt_const, leviForm_const, add_zero]
    exact leviForm_logNormSq_sub_nonneg hz v
  have h2 : 0 ≤ deriv poleProfile (ℓ z) * leviForm ℓ z v :=
    mul_nonneg (deriv_poleProfile_nonneg _) hL
  -- the first term
  have hdℓ : fderiv ℝ ℓ z = fderiv ℝ (fun y => Real.log (‖y - p‖ ^ 2)) z := by
    rw [hℓ, fderiv_sub_const]
  have hQ0 : 0 ≤ (fderiv ℝ ℓ z v ^ 2 + fderiv ℝ ℓ z (Complex.I • v) ^ 2) := by positivity
  have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hIv : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have hQ : (fderiv ℝ ℓ z v ^ 2 + fderiv ℝ ℓ z (Complex.I • v) ^ 2) ≤
      8 * ‖v‖ ^ 2 / ‖z - p‖ ^ 2 := by
    rw [hdℓ]
    have h1 := fderiv_logNormSq_sub_sq_le hz v
    have h2 := fderiv_logNormSq_sub_sq_le hz (Complex.I • v)
    rw [hIv] at h2
    have : 8 * ‖v‖ ^ 2 / ‖z - p‖ ^ 2 = 4 * ‖v‖ ^ 2 / ‖z - p‖ ^ 2 + 4 * ‖v‖ ^ 2 / ‖z - p‖ ^ 2 := by
      ring
    linarith
  have h1 : -(2 * poleK / r ^ 2 * ‖v‖ ^ 2) ≤ deriv (deriv poleProfile) (ℓ z) *
      (fderiv ℝ ℓ z v ^ 2 + fderiv ℝ ℓ z (Complex.I • v) ^ 2) / 4 := by
    by_cases hmem : ℓ z ∈ Icc (0 : ℝ) 1
    · -- here `‖z - p‖ ≥ r`
      have hzr : r ^ 2 ≤ ‖z - p‖ ^ 2 := by
        have h0 : a ≤ Real.log (‖z - p‖ ^ 2) := by have := hmem.1; simp only [hℓ] at this; linarith
        exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h0
      have hQ' : (fderiv ℝ ℓ z v ^ 2 + fderiv ℝ ℓ z (Complex.I • v) ^ 2) ≤ 8 * ‖v‖ ^ 2 / r ^ 2 :=
        hQ.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hzr)
      have hK := abs_deriv2_poleProfile_le (ℓ z)
      have hlow : -poleK ≤ deriv (deriv poleProfile) (ℓ z) := by
        have := neg_abs_le (deriv (deriv poleProfile) (ℓ z)); linarith
      have hK0 := poleK_nonneg
      have e1 : -(2 * poleK / r ^ 2 * ‖v‖ ^ 2) = -poleK * (8 * ‖v‖ ^ 2 / r ^ 2) / 4 := by
        field_simp; ring
      rw [e1]
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
      calc -poleK * (8 * ‖v‖ ^ 2 / r ^ 2)
          ≤ -poleK * (fderiv ℝ ℓ z v ^ 2 + fderiv ℝ ℓ z (Complex.I • v) ^ 2) := by
            have := mul_le_mul_of_nonneg_left hQ' hK0
            linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hlow hQ0
    · rw [deriv2_poleProfile_eq_zero hmem, zero_mul, zero_div]
      have : 0 ≤ 2 * poleK / r ^ 2 * ‖v‖ ^ 2 := by have := poleK_nonneg; positivity
      linarith
  linarith

end SGPT.PSH.GlobalL2
