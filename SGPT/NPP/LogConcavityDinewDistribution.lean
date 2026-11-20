import SGPT.NPP.LogConcavityDinewComparison
import SGPT.Foundations.Analysis.SmoothDistribution
import SGPT.Foundations.Analysis.TestLeviPairing

/-!
# From the comparison with the heat flow to a distributional inequality

If `g ≤ heatFlow g t` for `0 < t ≤ 1` (`le_heatFlow_of_isViscositySub`), then
`∫ g · L χ ≥ 0` for every nonnegative `C²` function `χ` with compact support, where
`L χ = ∑ⱼ leviForm χ · eⱼ = Δχ / 4` (`integral_mul_leviSum_nonneg`). This is the passage from
upper test functions to distributions of FPT `lem:constant-elliptic-upper-tests`, Step 2.

Ingredients: the moment bound for the kernel, pointwise convergence `heatFlow g t → g` as
`t → 0⁺` for upper semicontinuous `g` dominated by its heat flow, the integration by parts
`∫ ∂ₜK(t, x - y) χ(x) dx = ∫ K(t, x - y) Lχ(x) dx` (obtained by differentiating
`s ↦ ∫ K(t, x - y - s e) χ(x) dx` in two ways), and Fubini.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Moments and bounds -/

theorem mul_exp_neg_le_exp_neg_half {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp (-s) ≤ Real.exp (-(s / 2)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ s / 2)
  have h2 : s ≤ Real.exp (s / 2) := by nlinarith [sq_nonneg (s / 2 - 1)]
  have h3 : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  calc s * (Real.exp (-(s / 2)) * Real.exp (-(s / 2)))
      ≤ Real.exp (s / 2) * (Real.exp (-(s / 2)) * Real.exp (-(s / 2))) := by gcongr
    _ = Real.exp (-(s / 2)) := by
        rw [← mul_assoc, ← Real.exp_add]; simp

theorem heatKernel_mul_sq_le {t : ℝ} (ht : 0 < t) (w : ComplexModel n) :
    heatKernel n t w * ‖w‖ ^ 2 ≤ t * (Real.exp (-(1 / (2 * t)) * ‖w‖ ^ 2) / t ^ n) := by
  unfold heatKernel
  have h := mul_exp_neg_le_exp_neg_half (by positivity : 0 ≤ ‖w‖ ^ 2 / t)
  have e : -(1 / (2 * t)) * ‖w‖ ^ 2 = -(‖w‖ ^ 2 / t / 2) := by field_simp
  rw [e]
  calc Real.exp (-(‖w‖ ^ 2 / t)) / t ^ n * ‖w‖ ^ 2
      = t * ((‖w‖ ^ 2 / t) * Real.exp (-(‖w‖ ^ 2 / t))) / t ^ n := by field_simp
    _ ≤ t * Real.exp (-(‖w‖ ^ 2 / t / 2)) / t ^ n := by gcongr
    _ = _ := by ring

theorem integrable_heatKernel_mul_sq {t : ℝ} (ht : 0 < t) :
    Integrable (fun w : ComplexModel n => heatKernel n t w * ‖w‖ ^ 2) := by
  refine (((integrable_exp_neg_mul_sq_norm (n := n) (by positivity : 0 < 1 / (2 * t))).div_const
    (t ^ n)).const_mul t).mono' ?_ (ae_of_all _ fun w => ?_)
  · exact ((continuous_heatKernel_sub t 0).comp (continuous_neg)).aestronglyMeasurable.mul
      (continuous_norm.pow 2).aestronglyMeasurable |>.congr (ae_of_all _ fun w => by simp)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg ht w) (by positivity))]
    exact heatKernel_mul_sq_le ht w

/-- **Second moment**: `∫ K(t, w) ‖w‖² dw ≤ 2ⁿ πⁿ t`. -/
theorem integral_heatKernel_mul_sq_le {t : ℝ} (ht : 0 < t) :
    ∫ w : ComplexModel n, heatKernel n t w * ‖w‖ ^ 2 ≤ 2 ^ n * Real.pi ^ n * t := by
  have hI := ((integrable_exp_neg_mul_sq_norm (n := n) (by positivity : 0 < 1 / (2 * t))).div_const
    (t ^ n)).const_mul t
  refine (integral_mono (integrable_heatKernel_mul_sq ht) hI (heatKernel_mul_sq_le ht)).trans ?_
  rw [integral_const_mul, integral_div, integral_exp_neg_mul_sq_norm (by positivity)]
  rw [show Real.pi / (1 / (2 * t)) = 2 * Real.pi * t by field_simp, mul_pow, mul_pow]
  field_simp
  rfl

theorem heatKernel_comm_sub (t : ℝ) (x y : ComplexModel n) :
    heatKernel n t (x - y) = heatKernel n t (y - x) := heatKernel_sub_comm t x y

/-- The heat flow as an average of translates. -/
theorem heatFlow_eq_integral_translate (g : ComplexModel n → ℝ) (t : ℝ) (x : ComplexModel n) :
    heatFlow g t x = (Real.pi ^ n)⁻¹ * ∫ w, heatKernel n t w * g (x - w) := by
  unfold heatFlow
  congr 1
  have := integral_sub_left_eq_self (fun y => heatKernel n t (x - y) * g y)
    (μ := (volume : Measure (ComplexModel n))) x
  simp only [sub_sub_cancel] at this
  exact this.symm

theorem integrable_heatKernel_mul_translate {g : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) {t : ℝ} (ht : 0 < t)
    (x : ComplexModel n) :
    Integrable (fun w => heatKernel n t w * g (x - w)) := by
  have h := (integrable_heatKernel_mul hC hg ht x).comp_sub_left x
  refine h.congr (ae_of_all _ fun w => ?_)
  simp [sub_sub_cancel]

/-- A uniform bound for the heat flow for `0 < t ≤ 1`. -/
theorem abs_heatFlow_le {g : ComplexModel n → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2))
    (hg : Measurable g) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ComplexModel n) :
    |heatFlow g t x| ≤ C * (1 + 2 * ‖x‖ ^ 2 + 2 ^ (n + 1)) := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  rw [heatFlow_eq_integral_translate, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.pi ^ n)⁻¹)]
  have hint := integrable_heatKernel_mul_translate hC hg ht x
  have hK := integrable_heatKernel (n := n) ht
  have hK2 := integrable_heatKernel_mul_sq (n := n) ht
  have hbound : ∀ w : ComplexModel n, |heatKernel n t w * g (x - w)| ≤
      C * (1 + 2 * ‖x‖ ^ 2) * heatKernel n t w + 2 * C * (heatKernel n t w * ‖w‖ ^ 2) := by
    intro w
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht w)]
    have h1 := hC (x - w)
    have h2 : ‖x - w‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
      have := norm_sub_le x w
      nlinarith [sq_nonneg (‖x‖ - ‖w‖), norm_nonneg (x - w), norm_nonneg x, norm_nonneg w]
    have := heatKernel_nonneg ht w
    calc heatKernel n t w * |g (x - w)| ≤ heatKernel n t w * (C * (1 + ‖x - w‖ ^ 2)) := by gcongr
      _ ≤ heatKernel n t w * (C * (1 + (2 * ‖x‖ ^ 2 + 2 * ‖w‖ ^ 2))) := by gcongr
      _ = _ := by ring
  calc (Real.pi ^ n)⁻¹ * |∫ w, heatKernel n t w * g (x - w)|
      ≤ (Real.pi ^ n)⁻¹ * ∫ w, (C * (1 + 2 * ‖x‖ ^ 2) * heatKernel n t w +
          2 * C * (heatKernel n t w * ‖w‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans ?_) (by positivity)
        exact integral_mono hint.abs ((hK.const_mul _).add (hK2.const_mul _)) hbound
    _ = (Real.pi ^ n)⁻¹ * (C * (1 + 2 * ‖x‖ ^ 2) * Real.pi ^ n +
          2 * C * ∫ w, heatKernel n t w * ‖w‖ ^ 2) := by
        rw [integral_add (hK.const_mul _) (hK2.const_mul _), integral_const_mul,
          integral_const_mul, integral_heatKernel ht]
    _ ≤ (Real.pi ^ n)⁻¹ * (C * (1 + 2 * ‖x‖ ^ 2) * Real.pi ^ n +
          2 * C * (2 ^ n * Real.pi ^ n * t)) := by
        gcongr
        exact integral_heatKernel_mul_sq_le ht
    _ = C * (1 + 2 * ‖x‖ ^ 2) + 2 * C * 2 ^ n * t := by
        field_simp
    _ ≤ C * (1 + 2 * ‖x‖ ^ 2 + 2 ^ (n + 1)) := by
        have h2n := pow_pos (by norm_num : (0 : ℝ) < 2) n
        have : 2 * C * 2 ^ n * t ≤ 2 * C * 2 ^ n * 1 :=
          mul_le_mul_of_nonneg_left ht1 (by positivity)
        have e : C * (1 + 2 * ‖x‖ ^ 2 + 2 ^ (n + 1)) =
            C * (1 + 2 * ‖x‖ ^ 2) + 2 * C * 2 ^ n * 1 := by ring
        rw [e]
        linarith

/-! ### Convergence as `t → 0⁺` -/

theorem tendsto_pow_mul_exp_neg_div {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun t : ℝ => Real.exp (-(c / t)) / t ^ k) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_inv_nhdsGT_zero.const_mul_atTop hc)
  have h2 : Tendsto (fun t : ℝ => (c⁻¹) ^ k * ((c * t⁻¹) ^ k * Real.exp (-(c * t⁻¹))))
      (𝓝[>] 0) (𝓝 ((c⁻¹) ^ k * 0)) := h.const_mul _
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [div_eq_mul_inv c t]
  field_simp
  rw [← mul_pow, ← mul_pow, show 1 / c * (c / t) * t = 1 by field_simp, one_pow]

/-- **Pointwise convergence of the heat flow** of an upper semicontinuous function that lies
below its heat flow. -/
theorem tendsto_heatFlow {g : ComplexModel n → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2))
    (hg : Measurable g) (husc : UpperSemicontinuous g)
    (hlow : ∀ x t, 0 < t → t ≤ 1 → g x ≤ heatFlow g t x) (x : ComplexModel n) :
    Tendsto (fun t => heatFlow g t x) (𝓝[>] 0) (𝓝 (g x)) := by
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds one_pos)] with t ht ht'
    exact ⟨ht, ht'⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hev1] with t ht
    exact ha.trans_le (hlow x t ht.1 ht.2)
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  set ε : ℝ := (b - g x) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (husc x (g x + ε) (by linarith))
  -- the Gaussian tail outside the ball of radius `δ`
  set A : ℝ := ∫ w : ComplexModel n, Real.exp (-(1 / 2) * ‖w‖ ^ 2) * (|g (x - w)| + |g x|) with hA
  have hgw : ∀ w : ComplexModel n, |g (x - w)| + |g x| ≤
      C * (1 + 2 * ‖x‖ ^ 2) + |g x| + 2 * C * ‖w‖ ^ 2 := by
    intro w
    have h1 := hC (x - w)
    have h2 : ‖x - w‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
      have := norm_sub_le x w
      nlinarith [sq_nonneg (‖x‖ - ‖w‖), norm_nonneg (x - w), norm_nonneg x, norm_nonneg w]
    nlinarith [mul_le_mul_of_nonneg_left h2 hC0]
  have hAint : Integrable (fun w : ComplexModel n =>
      Real.exp (-(1 / 2) * ‖w‖ ^ 2) * (|g (x - w)| + |g x|)) := by
    have hG := integrable_exp_neg_mul_sq_norm (n := n) (by norm_num : (0 : ℝ) < 1 / 2)
    have hG2 := integrable_heatKernel_mul_sq (n := n) (by norm_num : (0 : ℝ) < 2)
    refine ((hG.mul_const (C * (1 + 2 * ‖x‖ ^ 2) + |g x|)).add
      ((hG2.const_mul (2 ^ n * (2 * C))))).mono' ?_ (ae_of_all _ fun w => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).measurable.mul
        (((continuous_abs.measurable.comp (hg.comp (measurable_const.sub measurable_id))).add
          measurable_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [Pi.add_apply]
      have e : heatKernel n 2 w * ‖w‖ ^ 2 = Real.exp (-(1 / 2) * ‖w‖ ^ 2) * ‖w‖ ^ 2 / 2 ^ n := by
        unfold heatKernel; ring_nf
      rw [e]
      have := hgw w
      have hpos := Real.exp_pos (-(1 / 2) * ‖w‖ ^ 2)
      calc Real.exp (-(1 / 2) * ‖w‖ ^ 2) * (|g (x - w)| + |g x|)
          ≤ Real.exp (-(1 / 2) * ‖w‖ ^ 2) * (C * (1 + 2 * ‖x‖ ^ 2) + |g x| + 2 * C * ‖w‖ ^ 2) := by
            gcongr
        _ = Real.exp (-(1 / 2) * ‖w‖ ^ 2) * (C * (1 + 2 * ‖x‖ ^ 2) + |g x|) +
            2 ^ n * (2 * C) * (Real.exp (-(1 / 2) * ‖w‖ ^ 2) * ‖w‖ ^ 2 / 2 ^ n) := by
            field_simp
  have htail : Tendsto (fun t : ℝ => (Real.pi ^ n)⁻¹ * (A * (Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n)))
      (𝓝[>] 0) (𝓝 ((Real.pi ^ n)⁻¹ * (A * 0))) :=
    ((tendsto_pow_mul_exp_neg_div (by positivity : 0 < δ ^ 2 / 2) n).const_mul A).const_mul _
  rw [mul_zero, mul_zero] at htail
  filter_upwards [hev1, htail.eventually (gt_mem_nhds hε0)] with t ht htl
  obtain ⟨ht0, ht1⟩ := ht
  have hint := integrable_heatKernel_mul_translate hC hg ht0 x
  have hK := integrable_heatKernel (n := n) ht0
  -- the pointwise bound of the integrand
  have hpt : ∀ w : ComplexModel n, heatKernel n t w * g (x - w) ≤
      heatKernel n t w * (g x + ε) +
        Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n * (Real.exp (-(1 / 2) * ‖w‖ ^ 2) *
          (|g (x - w)| + |g x|)) := by
    intro w
    have hKw := heatKernel_nonneg ht0 w
    by_cases hw : ‖w‖ < δ
    · have hgx : g (x - w) < g x + ε := hδ (by simpa [dist_eq_norm] using hw)
      have : 0 ≤ Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n * (Real.exp (-(1 / 2) * ‖w‖ ^ 2) *
          (|g (x - w)| + |g x|)) := by positivity
      nlinarith
    · push Not at hw
      have hKbound : heatKernel n t w ≤ Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n *
          Real.exp (-(1 / 2) * ‖w‖ ^ 2) := by
        unfold heatKernel
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        gcongr
        have hw2 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ0.le hw 2
        have : ‖w‖ ^ 2 / t ≥ ‖w‖ ^ 2 := by
          rw [ge_iff_le, le_div_iff₀ ht0]; nlinarith [sq_nonneg ‖w‖]
        have e : -(δ ^ 2 / 2 / t) + -(1 / 2) * ‖w‖ ^ 2 = -((δ ^ 2 / t + ‖w‖ ^ 2) / 2) := by ring
        rw [e]
        have h3 : δ ^ 2 / t ≤ ‖w‖ ^ 2 / t := by gcongr
        linarith
      have hgx : heatKernel n t w * g (x - w) ≤ heatKernel n t w * (|g (x - w)| + |g x|) +
          heatKernel n t w * (g x + ε) := by
        have h1 : g (x - w) ≤ |g (x - w)| := le_abs_self _
        have h2 : -|g x| ≤ g x := neg_abs_le _
        nlinarith
      have hpos : 0 ≤ |g (x - w)| + |g x| := by positivity
      calc heatKernel n t w * g (x - w) ≤ heatKernel n t w * (|g (x - w)| + |g x|) +
            heatKernel n t w * (g x + ε) := hgx
        _ ≤ Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n * Real.exp (-(1 / 2) * ‖w‖ ^ 2) *
              (|g (x - w)| + |g x|) + heatKernel n t w * (g x + ε) := by gcongr
        _ = _ := by ring
  have hmono := integral_mono hint ((hK.mul_const (g x + ε)).add (hAint.const_mul _)) hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hK.mul_const _) (hAint.const_mul _), integral_mul_const, integral_const_mul,
    integral_heatKernel ht0, ← hA] at hmono
  rw [heatFlow_eq_integral_translate]
  have hpi : (0 : ℝ) < (Real.pi ^ n)⁻¹ := by positivity
  calc (Real.pi ^ n)⁻¹ * ∫ w, heatKernel n t w * g (x - w)
      ≤ (Real.pi ^ n)⁻¹ * (Real.pi ^ n * (g x + ε) +
          Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n * A) := mul_le_mul_of_nonneg_left hmono hpi.le
    _ = g x + ε + (Real.pi ^ n)⁻¹ * (A * (Real.exp (-(δ ^ 2 / 2 / t)) / t ^ n)) := by
        field_simp
    _ < g x + ε + ε := by linarith
    _ < b := by rw [hε]; linarith

theorem continuous_heatFlow_space {g : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) {t : ℝ} (ht : 0 < t) :
    Continuous (fun x => heatFlow g t x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h := continuousAt_heatFlow hC hg (x' := x) ht
  exact ContinuousAt.comp (f := fun x' : ComplexModel n => (x', t)) h (by fun_prop)

/-- **Convergence of the heat flow against test functions** as `t → 0⁺`. -/
theorem tendsto_integral_heatFlow_mul {g : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) (husc : UpperSemicontinuous g)
    (hlow : ∀ x t, 0 < t → t ≤ 1 → g x ≤ heatFlow g t x) {φ : ComplexModel n → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun t => ∫ x, heatFlow g t x * φ x) (𝓝[>] 0) (𝓝 (∫ x, g x * φ x)) := by
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds one_pos)] with t ht ht'
    exact ⟨ht, ht'⟩
  have hsupp : HasCompactSupport (fun x : ComplexModel n =>
      C * (1 + 2 * ‖x‖ ^ 2 + 2 ^ (n + 1)) * |φ x|) := by
    have h1 : HasCompactSupport (fun x => |φ x|) := hφc.comp_left (g := fun r : ℝ => |r|) abs_zero
    exact h1.mul_left
  have hB : Integrable (fun x : ComplexModel n => C * (1 + 2 * ‖x‖ ^ 2 + 2 ^ (n + 1)) * |φ x|) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hsupp
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hB ?_
  · filter_upwards [hev1] with t ht
    exact ((continuous_heatFlow_space hC hg ht.1).mul hφ).aestronglyMeasurable
  · filter_upwards [hev1] with t ht
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_heatFlow_le hC hg ht.1 ht.2 x) (abs_nonneg _)
  · exact ae_of_all _ fun x => (tendsto_heatFlow hC hg husc hlow x).mul_const (φ x)

/-! ### Integration by parts against the kernel -/

/-- `K(t, ·)·(1 + ‖·‖²)` is bounded. -/
theorem heatKernel_mul_one_add_sq_le {t : ℝ} (ht : 0 < t) (w : ComplexModel n) :
    heatKernel n t w * (1 + ‖w‖ ^ 2) ^ 1 ≤ 2 * t * Real.exp (1 / (2 * t)) / t ^ n := by
  have h := one_add_sq_pow_mul_exp_le ht 1 ‖w‖
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h ⊢
  unfold heatKernel
  have hle : Real.exp (-(‖w‖ ^ 2 / (2 * t))) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ ‖w‖ ^ 2 / (2 * t) := by positivity
    linarith)
  calc Real.exp (-(‖w‖ ^ 2 / t)) / t ^ n * (1 + ‖w‖ ^ 2)
      = (1 + ‖w‖ ^ 2) * Real.exp (-(‖w‖ ^ 2 / t)) / t ^ n := by ring
    _ ≤ 2 * t * Real.exp (1 / (2 * t)) * Real.exp (-(‖w‖ ^ 2 / (2 * t))) / t ^ n := by gcongr
    _ ≤ 2 * t * Real.exp (1 / (2 * t)) * 1 / t ^ n := by gcongr
    _ = _ := by ring

theorem hasDerivAt_heatKernel_shift {t : ℝ} (ht : t ≠ 0) (w e : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel n t (w - s • e)) (heatKernelD t (w - s • e) (-e)) s := by
  have h := hasDerivAt_heatKernel_line ht w (-e) s
  have e1 : ∀ s : ℝ, w + s • (-e) = w - s • e := fun s => by rw [smul_neg, ← sub_eq_add_neg]
  simp only [e1] at h
  exact h

theorem hasDerivAt_heatKernelD_shift {t : ℝ} (ht : t ≠ 0) (w e : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernelD t (w - s • e) (-e))
      (heatKernelDD t (w - s • e) (-e) (-e)) s := by
  have h := hasDerivAt_heatKernelD_line ht w (-e) s
  have e1 : ∀ s : ℝ, w + s • (-e) = w - s • e := fun s => by rw [smul_neg, ← sub_eq_add_neg]
  simp only [e1] at h
  exact h

theorem heatKernelDD_neg (t : ℝ) (w e : ComplexModel n) :
    heatKernelDD t w (-e) (-e) = heatKernelDD t w e e := by
  simp [heatKernelDD, inner_neg_right, inner_neg_left]

/-- **Integration by parts**, by differentiating `s ↦ ∫ K(t, x - y - s e) χ(x) dx` twice, once
on the kernel and once on `χ`. -/
theorem integral_heatKernelDD_mul_eq {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) {t : ℝ} (ht : 0 < t) (y e : ComplexModel n) :
    ∫ x, heatKernelDD t (x - y) e e * χ x = ∫ x, heatKernel n t (x - y) * realHessian χ x e e := by
  have ht0 : t ≠ 0 := ht.ne'
  set B : ℝ := 2 * t * Real.exp (1 / (2 * t)) / t ^ n with hB
  have hKB : ∀ w : ComplexModel n, heatKernel n t w * (1 + ‖w‖ ^ 2) ^ 1 ≤ B :=
    heatKernel_mul_one_add_sq_le ht
  have hχi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hχ1 : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by norm_num)
  have hχ2 : ContDiff ℝ 1 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
  have hf1c : Continuous (fun p => fderiv ℝ χ p e) := hχ1.clm_apply continuous_const
  have hf2c : Continuous (fun p => realHessian χ p e e) := continuous_realHessian hχ e e
  have hf1s : HasCompactSupport (fun p => fderiv ℝ χ p e) := by
    refine hχc.mono' fun p hp => ?_
    by_contra h
    exact hp (by show fderiv ℝ χ p e = 0; rw [fderiv_of_notMem_tsupport ℝ h]; rfl)
  have hf2s : HasCompactSupport (fun p => realHessian χ p e e) := by
    refine hχc.mono' fun p hp => ?_
    by_contra h
    exact hp (realHessian_eq_zero_of_notMem_tsupport h e e)
  obtain ⟨M1, hM1⟩ := hf1c.bounded_above_of_compact_support hf1s
  obtain ⟨M2, hM2⟩ := hf2c.bounded_above_of_compact_support hf2s
  have hKi := integrable_heatKernel (n := n) ht
  -- the kernel side
  set G1 : ℝ → ℝ := fun s => ∫ x, heatKernelD t (x - y - s • e) (-e) * χ x with hG1
  set G2 : ℝ → ℝ := fun s => ∫ x, heatKernelDD t (x - y - s • e) (-e) (-e) * χ x with hG2
  have hD1 : ∀ v h : ComplexModel n, |heatKernelD t v h| ≤ B * (2 / t * ‖h‖) := fun v h =>
    (abs_heatKernelD_le ht v h).trans (by gcongr; exact hKB v)
  have hD2 : ∀ v h : ComplexModel n, |heatKernelDD t v h h| ≤ B * ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖h‖) :=
    fun v h => (abs_heatKernelDD_le ht v h h).trans (by gcongr; exact hKB v)
  have hcontD : ∀ s : ℝ, Continuous (fun x : ComplexModel n => heatKernelD t (x - y - s • e) (-e)) :=
    fun s => by unfold heatKernelD heatKernel; fun_prop
  have hcontDD : ∀ s : ℝ,
      Continuous (fun x : ComplexModel n => heatKernelDD t (x - y - s • e) (-e) (-e)) :=
    fun s => by unfold heatKernelDD heatKernel; fun_prop
  have hcont0 : ∀ s : ℝ, Continuous (fun x : ComplexModel n => heatKernel n t (x - y - s • e)) :=
    fun s => by unfold heatKernel; fun_prop
  have hderK : ∀ s₀ : ℝ, HasDerivAt (fun s => ∫ x, heatKernel n t (x - y - s • e) * χ x)
      (G1 s₀) s₀ := by
    intro s₀
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x => heatKernel n t (x - y - s • e) * χ x)
      (F' := fun s x => heatKernelD t (x - y - s • e) (-e) * χ x)
      (bound := fun x => B * (2 / t * ‖-e‖) * |χ x|) univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun s => ((hcont0 s).mul hχ.continuous).aestronglyMeasurable
    · refine (Continuous.integrable_of_hasCompactSupport ((hcont0 s₀).mul hχ.continuous) ?_)
      exact hχc.mul_left
    · exact ((hcontD s₀).mul hχ.continuous).aestronglyMeasurable
    · refine ae_of_all _ fun x s _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hD1 _ _) (abs_nonneg _)
    · exact hχi.abs.const_mul _
    · exact ae_of_all _ fun x s _ => (hasDerivAt_heatKernel_shift ht0 (x - y) e s).mul_const (χ x)
  have hderK2 : ∀ s₀ : ℝ, HasDerivAt G1 (G2 s₀) s₀ := by
    intro s₀
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x => heatKernelD t (x - y - s • e) (-e) * χ x)
      (F' := fun s x => heatKernelDD t (x - y - s • e) (-e) (-e) * χ x)
      (bound := fun x => B * ((4 / t ^ 2 + 2 / t) * ‖-e‖ * ‖-e‖) * |χ x|) univ_mem ?_ ?_ ?_ ?_ ?_
        ?_).2
    · exact Eventually.of_forall fun s => ((hcontD s).mul hχ.continuous).aestronglyMeasurable
    · refine (Continuous.integrable_of_hasCompactSupport ((hcontD s₀).mul hχ.continuous) ?_)
      exact hχc.mul_left
    · exact ((hcontDD s₀).mul hχ.continuous).aestronglyMeasurable
    · refine ae_of_all _ fun x s _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hD2 _ _) (abs_nonneg _)
    · exact hχi.abs.const_mul _
    · exact ae_of_all _ fun x s _ =>
        (hasDerivAt_heatKernelD_shift ht0 (x - y) e s).mul_const (χ x)
  -- the test-function side
  have hsub : ∀ s : ℝ, ∫ x, heatKernel n t (x - y - s • e) * χ x =
      ∫ z, heatKernel n t z * χ (z + (y + s • e)) := by
    intro s
    have := integral_add_right_eq_self (μ := (volume : Measure (ComplexModel n)))
      (fun x => heatKernel n t (x - y - s • e) * χ x) (y + s • e)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    congr 2
    abel
  set H1 : ℝ → ℝ := fun s => ∫ z, heatKernel n t z * fderiv ℝ χ (z + (y + s • e)) e with hH1
  set H2 : ℝ → ℝ := fun s => ∫ z, heatKernel n t z * realHessian χ (z + (y + s • e)) e e
    with hH2
  have hline : ∀ z : ComplexModel n, ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => z + (y + s • e)) e s := fun z s => by
    have := (((hasDerivAt_id s).smul_const e).const_add y).const_add z
    simpa using this
  have hχd : ∀ p, HasFDerivAt χ (fderiv ℝ χ p) p := fun p =>
    (hχ.differentiable (by norm_num) p).hasFDerivAt
  have hχd2 : ∀ p, HasFDerivAt (fderiv ℝ χ) (fderiv ℝ (fderiv ℝ χ) p) p := fun p =>
    (hχ2.differentiable (by norm_num) p).hasFDerivAt
  have hcz : ∀ s : ℝ, Continuous (fun z : ComplexModel n => z + (y + s • e)) := fun s => by
    fun_prop
  have hderX : ∀ s₀ : ℝ, HasDerivAt (fun s => ∫ z, heatKernel n t z * χ (z + (y + s • e)))
      (H1 s₀) s₀ := by
    intro s₀
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s z => heatKernel n t z * χ (z + (y + s • e)))
      (F' := fun s z => heatKernel n t z * fderiv ℝ χ (z + (y + s • e)) e)
      (bound := fun z => heatKernel n t z * M1) univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun s =>
        ((continuous_heatKernel (n := n) ht0).mul
          (hχ.continuous.comp (hcz s))).aestronglyMeasurable
    · obtain ⟨M0, hM0⟩ := hχ.continuous.bounded_above_of_compact_support hχc
      refine (hKi.mul_const M0).mono' ((continuous_heatKernel (n := n) ht0).mul
          (hχ.continuous.comp (hcz s₀))).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht z)]
      exact mul_le_mul_of_nonneg_left (hM0 _) (heatKernel_nonneg ht z)
    · exact ((continuous_heatKernel (n := n) ht0).mul
          (hf1c.comp (hcz s₀))).aestronglyMeasurable
    · refine ae_of_all _ fun z s _ => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht z)]
      exact mul_le_mul_of_nonneg_left (hM1 _) (heatKernel_nonneg ht z)
    · exact hKi.mul_const _
    · refine ae_of_all _ fun z s _ => ?_
      exact ((hχd _).comp_hasDerivAt s (hline z s)).const_mul (heatKernel n t z)
  have hderX2 : ∀ s₀ : ℝ, HasDerivAt H1 (H2 s₀) s₀ := by
    intro s₀
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s z => heatKernel n t z * fderiv ℝ χ (z + (y + s • e)) e)
      (F' := fun s z => heatKernel n t z * realHessian χ (z + (y + s • e)) e e)
      (bound := fun z => heatKernel n t z * M2) univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun s =>
        ((continuous_heatKernel (n := n) ht0).mul (hf1c.comp (hcz s))).aestronglyMeasurable
    · refine (hKi.mul_const M1).mono' ((continuous_heatKernel (n := n) ht0).mul
          (hf1c.comp (hcz s₀))).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht z)]
      exact mul_le_mul_of_nonneg_left (hM1 _) (heatKernel_nonneg ht z)
    · exact ((continuous_heatKernel (n := n) ht0).mul
          (hf2c.comp (hcz s₀))).aestronglyMeasurable
    · refine ae_of_all _ fun z s _ => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht z)]
      exact mul_le_mul_of_nonneg_left (hM2 _) (heatKernel_nonneg ht z)
    · exact hKi.mul_const _
    · refine ae_of_all _ fun z s _ => ?_
      have hc := (hχd2 _).comp_hasDerivAt s (hline z s)
      have happ := hc.clm_apply (hasDerivAt_const s e)
      simp only [map_zero, add_zero] at happ
      have : HasDerivAt (fun s => fderiv ℝ χ (z + (y + s • e)) e)
          (realHessian χ (z + (y + s • e)) e e) s := by
        rw [realHessian_eq_fderiv]
        exact happ
      exact this.const_mul (heatKernel n t z)
  -- comparison of the two computations
  have hGH : ∀ s, G1 s = H1 s := fun s => by
    have h1 := hderK s
    have h2 := hderX s
    have heq : (fun s => ∫ x, heatKernel n t (x - y - s • e) * χ x) =
        fun s => ∫ z, heatKernel n t z * χ (z + (y + s • e)) := funext hsub
    rw [heq] at h1
    exact h1.unique h2
  have hG1H1 : G1 = H1 := funext hGH
  have h0 : G2 0 = H2 0 := by
    have h1 := hderK2 0
    rw [hG1H1] at h1
    exact h1.unique (hderX2 0)
  simp only [hG2, hH2, zero_smul, sub_zero, add_zero, heatKernelDD_neg] at h0
  rw [h0]
  have := integral_add_right_eq_self (μ := (volume : Measure (ComplexModel n)))
    (fun x => heatKernel n t (x - y) * realHessian χ x e e) y
  simp only [add_sub_cancel_right] at this
  exact this

/-- The complex Laplacian `L χ = ∑ⱼ ∂²χ/∂zⱼ∂z̄ⱼ = Δχ/4`. -/
def leviSum (χ : ComplexModel n → ℝ) (x : ComplexModel n) : ℝ :=
  ∑ j, leviForm χ x (coordinateVector j)

theorem heatKernelT_neg (t : ℝ) (w : ComplexModel n) : heatKernelT t (-w) = heatKernelT t w := by
  simp [heatKernelT, heatKernel_neg]

theorem continuous_leviSum {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ) :
    Continuous (leviSum χ) := by
  unfold leviSum leviForm
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_realHessian hχ _ _).add (continuous_realHessian hχ _ _)).div_const 4

theorem hasCompactSupport_leviSum {χ : ComplexModel n → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (leviSum χ) := by
  refine hχc.mono' fun p hp => ?_
  by_contra h
  apply hp
  simp only [leviSum, leviForm, realHessian_eq_zero_of_notMem_tsupport h, add_zero, zero_div,
    Finset.sum_const_zero]

/-- **Integration by parts for the time derivative of the kernel**:
`∫ ∂ₜK(t, x - y) χ(x) dx = ∫ K(t, x - y) Lχ(x) dx`. -/
theorem integral_heatKernelT_mul_eq {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) {t : ℝ} (ht : 0 < t) (y : ComplexModel n) :
    ∫ x, heatKernelT t (x - y) * χ x = ∫ x, heatKernel n t (x - y) * leviSum χ x := by
  have ht0 : t ≠ 0 := ht.ne'
  have hχi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hKi := integrable_heatKernel (n := n) ht
  have hDDi : ∀ e : ComplexModel n, Integrable (fun x => heatKernelDD t (x - y) e e * χ x) := by
    intro e
    refine Continuous.integrable_of_hasCompactSupport ?_ hχc.mul_left
    have : Continuous (fun x : ComplexModel n => heatKernelDD t (x - y) e e) := by
      unfold heatKernelDD heatKernel; fun_prop
    exact this.mul hχ.continuous
  have hHi : ∀ e : ComplexModel n, Integrable (fun x => heatKernel n t (x - y) * realHessian χ x e e) := by
    intro e
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (by unfold heatKernel; fun_prop :
        Continuous fun x : ComplexModel n => heatKernel n t (x - y)).mul
          (continuous_realHessian hχ e e)
    · refine HasCompactSupport.mul_left ?_
      refine hχc.mono' fun p hp => ?_
      by_contra h
      exact hp (realHessian_eq_zero_of_notMem_tsupport h e e)
  have e1 : (fun x => heatKernelT t (x - y) * χ x) = fun x => (1 / 4 : ℝ) * ∑ j,
      (heatKernelDD t (x - y) (coordinateVector j) (coordinateVector j) * χ x +
        heatKernelDD t (x - y) (Complex.I • coordinateVector j) (Complex.I • coordinateVector j) *
          χ x) := by
    funext x
    simp only [← add_mul, ← Finset.sum_mul, sum_heatKernelDD_coordinate]
    ring
  have e2 : (fun x => heatKernel n t (x - y) * leviSum χ x) = fun x => (1 / 4 : ℝ) * ∑ j,
      (heatKernel n t (x - y) * realHessian χ x (coordinateVector j) (coordinateVector j) +
        heatKernel n t (x - y) * realHessian χ x (Complex.I • coordinateVector j)
          (Complex.I • coordinateVector j)) := by
    funext x
    simp only [leviSum, leviForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, integral_const_mul, integral_const_mul,
    integral_finsetSum (f := fun j x =>
      heatKernelDD t (x - y) (coordinateVector j) (coordinateVector j) * χ x +
        heatKernelDD t (x - y) (Complex.I • coordinateVector j) (Complex.I • coordinateVector j) *
          χ x) _ (fun j _ => by exact (hDDi _).add (hDDi _)),
    integral_finsetSum (f := fun j x =>
      heatKernel n t (x - y) * realHessian χ x (coordinateVector j) (coordinateVector j) +
        heatKernel n t (x - y) * realHessian χ x (Complex.I • coordinateVector j)
          (Complex.I • coordinateVector j)) _ (fun j _ => by exact (hHi _).add (hHi _))]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add (hDDi _) (hDDi _), integral_add (hHi _) (hHi _),
    integral_heatKernelDD_mul_eq hχ hχc ht, integral_heatKernelDD_mul_eq hχ hχc ht]

/-- The time derivative of the heat flow of a test function is the heat flow of its complex
Laplacian. -/
theorem heatFlowT_eq_heatFlow_leviSum {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) {t : ℝ} (ht : 0 < t) (y : ComplexModel n) :
    heatFlowT χ t y = heatFlow (leviSum χ) t y := by
  unfold heatFlowT heatFlow
  congr 1
  have h1 : ∫ x, heatKernelT t (y - x) * χ x = ∫ x, heatKernelT t (x - y) * χ x := by
    congr 1; funext x; rw [← neg_sub, heatKernelT_neg]
  have h2 : ∫ x, heatKernel n t (y - x) * leviSum χ x = ∫ x, heatKernel n t (x - y) * leviSum χ x := by
    congr 1; funext x; rw [heatKernel_sub_comm]
  rw [h1, h2, integral_heatKernelT_mul_eq hχ hχc ht]

/-! ### Fubini and decay -/

theorem integral_mul_heatFlow_swap {g : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) {f : ComplexModel n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) :
    ∫ y, g y * heatFlow f t y = ∫ x, heatFlow g t x * f x := by
  have hga : ∀ y, |(fun y => |g y|) y| ≤ C * (1 + ‖y‖ ^ 2) := fun y => by
    simpa only [abs_abs] using hC y
  have hgam : Measurable fun y => |g y| := continuous_abs.measurable.comp hg
  set F : ComplexModel n → ComplexModel n → ℝ := fun y x => g y * heatKernel n t (y - x) * f x
    with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : Measurable fun p : ComplexModel n × ComplexModel n => g p.1 := hg.comp measurable_fst
    have h2 : Continuous fun p : ComplexModel n × ComplexModel n => heatKernel n t (p.1 - p.2) := by
      unfold heatKernel; fun_prop
    have h3 : Continuous fun p : ComplexModel n × ComplexModel n => f p.2 := hf.comp continuous_snd
    exact ((h1.mul h2.measurable).mul h3.measurable).aestronglyMeasurable
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine ae_of_all _ fun x => ?_
      have := (integrable_heatKernel_mul hC hg ht x).mul_const (f x)
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [hF, Function.uncurry_apply_pair, heatKernel_sub_comm t x y]
      ring
    · have hcont := continuous_heatFlow_space hga hgam ht
      have heq : (fun x => ∫ y, ‖Function.uncurry F (y, x)‖) =
          fun x => Real.pi ^ n * heatFlow (fun y => |g y|) t x * |f x| := by
        funext x
        unfold heatFlow
        rw [mul_inv_cancel_left₀ (pow_ne_zero n Real.pi_ne_zero), ← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [hF, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (heatKernel_nonneg ht _), heatKernel_sub_comm t y x]
        ring
      rw [heq]
      refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
      exact (hfc.comp_left (g := fun r : ℝ => |r|) abs_zero).mul_left
  have hswap := integral_integral_swap hint
  unfold heatFlow
  simp only [hF] at hswap
  have e1 : ∀ y, g y * ((Real.pi ^ n)⁻¹ * ∫ x, heatKernel n t (y - x) * f x) =
      (Real.pi ^ n)⁻¹ * ∫ x, g y * heatKernel n t (y - x) * f x := by
    intro y
    have : ∫ x, g y * heatKernel n t (y - x) * f x = g y * ∫ x, heatKernel n t (y - x) * f x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
    rw [this]; ring
  have e2 : ∀ x, ((Real.pi ^ n)⁻¹ * ∫ y, heatKernel n t (x - y) * g y) * f x =
      (Real.pi ^ n)⁻¹ * ∫ y, g y * heatKernel n t (y - x) * f x := by
    intro x
    have : ∫ y, g y * heatKernel n t (y - x) * f x = (∫ y, heatKernel n t (x - y) * g y) * f x := by
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [heatKernel_sub_comm t y x]
      ring
    rw [this]; ring
  simp only [e1, e2]
  rw [integral_const_mul, integral_const_mul, hswap]

/-- Gaussian decay of the heat flow of a compactly supported function. -/
theorem abs_heatFlow_le_of_compactSupport {f : ComplexModel n → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {ρ : ℝ} (hρ : tsupport f ⊆ Metric.closedBall 0 ρ)
    {a b r : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b) (y : ComplexModel n) :
    |heatFlow f r y| ≤ (Real.pi ^ n)⁻¹ * (Real.exp (ρ ^ 2 / b) / a ^ n * ∫ x, |f x|) *
      Real.exp (-(‖y‖ ^ 2 / (2 * b))) := by
  have hr : 0 < r := ha.trans_le har
  have hb : 0 < b := hr.trans_le hrb
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  unfold heatFlow
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.pi ^ n)⁻¹), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpt : ∀ x, |heatKernel n r (y - x) * f x| ≤
      Real.exp (ρ ^ 2 / b) / a ^ n * Real.exp (-(‖y‖ ^ 2 / (2 * b))) * |f x| := by
    intro x
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hr _)]
    by_cases hx : x ∈ tsupport f
    · have hxρ : ‖x - 0‖ ≤ ρ := by simpa [dist_eq_norm] using hρ hx
      have h1 := heatKernel_le_of_mem_Icc ha har hrb (y - x)
      have h2 := exp_neg_sq_norm_sub_le (n := n) hb (y := y) hxρ
      rw [norm_sub_rev y x] at h1
      simp only [zero_sub, norm_neg] at h2
      gcongr
      calc heatKernel n r (y - x) ≤ Real.exp (-(‖x - y‖ ^ 2 / b)) / a ^ n := h1
        _ ≤ Real.exp (ρ ^ 2 / b) * Real.exp (-(‖y‖ ^ 2 / (2 * b))) / a ^ n := by gcongr
        _ = _ := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfg : ∀ y, |f y| ≤ M * (1 + ‖y‖ ^ 2) := fun y => by
    have := hM y
    rw [Real.norm_eq_abs] at this
    nlinarith [sq_nonneg ‖y‖]
  calc |∫ x, heatKernel n r (y - x) * f x| ≤ ∫ x, |heatKernel n r (y - x) * f x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, Real.exp (ρ ^ 2 / b) / a ^ n * Real.exp (-(‖y‖ ^ 2 / (2 * b))) * |f x| :=
        integral_mono (integrable_heatKernel_mul hfg hf.measurable hr y).abs
          (hfi.abs.const_mul _) hpt
    _ = _ := by rw [integral_const_mul]; ring

/-! ### The distributional inequality -/

theorem integrable_one_add_sq_mul_exp {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ComplexModel n => (1 + ‖y‖ ^ 2) * Real.exp (-(‖y‖ ^ 2 / c))) := by
  have h1 := integrable_exp_neg_mul_sq_norm (n := n) (inv_pos.mpr hc)
  have h2 := (integrable_heatKernel_mul_sq (n := n) hc).const_mul (c ^ n)
  refine (h1.add h2).congr (ae_of_all _ fun y => ?_)
  simp only [Pi.add_apply, heatKernel]
  have : -(c⁻¹) * ‖y‖ ^ 2 = -(‖y‖ ^ 2 / c) := by ring
  rw [this]
  field_simp

/-- **Upper tests to distributions.** If an upper semicontinuous function of quadratic growth
satisfies `g + F t ≤ heatFlow g t` (`F ≥ 0`), then `∫ g · Lχ ≥ F ∫ χ` for all nonnegative
compactly supported `C²` functions `χ`. -/
theorem integral_mul_leviSum_ge {g : ComplexModel n → ℝ} {C F : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) (husc : UpperSemicontinuous g)
    (hF : 0 ≤ F) (hle' : ∀ x t, 0 < t → t ≤ 1 → g x + F * t ≤ heatFlow g t x)
    {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    F * ∫ x, χ x ≤ ∫ x, g x * leviSum χ x := by
  have hle : ∀ x t, 0 < t → t ≤ 1 → g x ≤ heatFlow g t x := fun x t ht0 ht1 => by
    have := hle' x t ht0 ht1
    nlinarith [mul_nonneg hF ht0.le]
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  have hLc := continuous_leviSum hχ
  have hLs := hasCompactSupport_leviSum hχc
  obtain ⟨ρ, hρχ⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  have hρ : tsupport (leviSum χ) ⊆ Metric.closedBall 0 ρ := by
    refine (closure_minimal (fun p hp => ?_) (isClosed_tsupport χ)).trans hρχ
    by_contra h
    apply hp
    simp only [leviSum, leviForm, realHessian_eq_zero_of_notMem_tsupport h, add_zero, zero_div,
      Finset.sum_const_zero]
  obtain ⟨Mχ, hMχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0)
  have hχg : ∀ y, |χ y| ≤ Mχ * (1 + ‖y‖ ^ 2) := fun y => by
    have := hMχ y
    rw [Real.norm_eq_abs] at this
    nlinarith [sq_nonneg ‖y‖]
  obtain ⟨ML, hML⟩ := hLc.bounded_above_of_compact_support hLs
  have hML0 : 0 ≤ ML := (norm_nonneg _).trans (hML 0)
  have hLg : ∀ y, |leviSum χ y| ≤ ML * (1 + ‖y‖ ^ 2) := fun y => by
    have := hML y
    rw [Real.norm_eq_abs] at this
    nlinarith [sq_nonneg ‖y‖]
  set Φ : ℝ → ℝ := fun t => ∫ x, heatFlow g t x * χ x with hΦ
  set Ψ : ℝ → ℝ := fun t => ∫ x, heatFlow g t x * leviSum χ x with hΨ
  have hΦlim : Tendsto Φ (𝓝[>] 0) (𝓝 (∫ x, g x * χ x)) :=
    tendsto_integral_heatFlow_mul hC hg husc hle hχ.continuous hχc
  have hΨlim : Tendsto Ψ (𝓝[>] 0) (𝓝 (∫ x, g x * leviSum χ x)) :=
    tendsto_integral_heatFlow_mul hC hg husc hle hLc hLs
  have habsχ : HasCompactSupport (fun x => |χ x|) := hχc.comp_left (g := fun r : ℝ => |r|) abs_zero
  have hbχc : HasCompactSupport (fun x : ComplexModel n => C * (1 + ‖x‖ ^ 2) * |χ x|) :=
    habsχ.mul_left
  have hbχ : Continuous (fun x : ComplexModel n => C * (1 + ‖x‖ ^ 2) * |χ x|) :=
    (continuous_const.mul (continuous_const.add (continuous_norm.pow 2))).mul
      (continuous_abs.comp hχ.continuous)
  have hgχ : Integrable (fun x => g x * χ x) := by
    refine Integrable.mono' (hbχ.integrable_of_hasCompactSupport hbχc)
      (hg.mul hχ.continuous.measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  have hχi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hΦge : ∀ t, 0 < t → t ≤ 1 → (∫ x, g x * χ x) + F * t * ∫ x, χ x ≤ Φ t := by
    intro t ht0 ht1
    rw [← integral_const_mul, ← integral_add hgχ (hχi.const_mul _)]
    refine integral_mono (hgχ.add (hχi.const_mul _)) (Continuous.integrable_of_hasCompactSupport
      ((continuous_heatFlow_space hC hg ht0).mul hχ.continuous) hχc.mul_left) fun x => ?_
    have := mul_le_mul_of_nonneg_right (hle' x t ht0 ht1) (hχ0 x)
    simp only
    linarith
  -- differentiability of `Φ`
  have hderiv : ∀ t, 0 < t → HasDerivAt Φ (Ψ t) t := by
    intro t ht
    have hΦeq : ∀ s, 0 < s → Φ s = ∫ y, g y * heatFlow χ s y := fun s hs =>
      (integral_mul_heatFlow_swap hC hg hχ.continuous hχc hs).symm
    have hΨeq : Ψ t = ∫ y, g y * heatFlowT χ t y := by
      rw [hΨ]
      simp only
      rw [← integral_mul_heatFlow_swap hC hg hLc hLs ht]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show g y * heatFlow (leviSum χ) t y = g y * heatFlowT χ t y
      rw [heatFlowT_eq_heatFlow_leviSum hχ hχc ht]
    set D : ℝ := (Real.pi ^ n)⁻¹ * (Real.exp (ρ ^ 2 / (2 * t)) / (t / 2) ^ n *
      ∫ x, |leviSum χ x|) with hD
    have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure (ComplexModel n)))
      (F := fun s y => g y * heatFlow χ s y) (F' := fun s y => g y * heatFlowT χ s y)
      (bound := fun y => C * D * ((1 + ‖y‖ ^ 2) * Real.exp (-(‖y‖ ^ 2 / (2 * (2 * t))))))
      (x₀ := t) hs ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hΨeq]
      refine key.2.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s (hs' : 0 < s)
      exact hΦeq s hs'
    · filter_upwards [Ioi_mem_nhds ht] with s (hs' : 0 < s)
      exact (hg.mul (continuous_heatFlow_space hχg hχ.continuous.measurable hs').measurable
        ).aestronglyMeasurable
    · have hdec := fun y => abs_heatFlow_le_of_compactSupport hχ.continuous hχc hρχ ht le_rfl
        le_rfl y
      refine ((integrable_one_add_sq_mul_exp (n := n) (by positivity : 0 < 2 * t)).const_mul
        (C * ((Real.pi ^ n)⁻¹ * (Real.exp (ρ ^ 2 / t) / t ^ n * ∫ x, |χ x|)))).mono'
        (hg.mul (continuous_heatFlow_space hχg hχ.continuous.measurable ht).measurable
          ).aestronglyMeasurable (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |g y| * |heatFlow χ t y|
          ≤ (C * (1 + ‖y‖ ^ 2)) * ((Real.pi ^ n)⁻¹ * (Real.exp (ρ ^ 2 / t) / t ^ n *
            ∫ x, |χ x|) * Real.exp (-(‖y‖ ^ 2 / (2 * t)))) :=
            mul_le_mul (hC y) (hdec y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hmeas : Measurable fun y => heatFlowT χ t y := by
        have : (fun y => heatFlowT χ t y) = fun y => heatFlow (leviSum χ) t y := funext fun y =>
          heatFlowT_eq_heatFlow_leviSum hχ hχc ht y
        rw [this]
        exact (continuous_heatFlow_space hLg hLc.measurable ht).measurable
      exact (hg.mul hmeas).aestronglyMeasurable
    · refine ae_of_all _ fun y s hs' => ?_
      have hs0 : 0 < s := by linarith [hs'.1]
      rw [heatFlowT_eq_heatFlow_leviSum hχ hχc hs0, Real.norm_eq_abs, abs_mul]
      have hdec := abs_heatFlow_le_of_compactSupport hLc hLs hρ (by positivity : 0 < t / 2)
        hs'.1.le hs'.2.le y
      calc |g y| * |heatFlow (leviSum χ) s y|
          ≤ (C * (1 + ‖y‖ ^ 2)) * (D * Real.exp (-(‖y‖ ^ 2 / (2 * (2 * t))))) :=
            mul_le_mul (hC y) (by rw [hD]; exact hdec) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · exact (integrable_one_add_sq_mul_exp (by positivity)).const_mul _
    · refine ae_of_all _ fun y s hs' => ?_
      exact (hasDerivAt_heatFlow_time hχg hχ.continuous.measurable
        (by linarith [hs'.1] : 0 < s) y).const_mul (g y)
  -- the mean value argument
  by_contra hneg
  push Not at hneg
  set I : ℝ := ∫ x, g x * leviSum χ x with hI
  set J : ℝ := F * ∫ x, χ x with hJ
  set ν : ℝ := (J - I) / 2 with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Ψ t < J - ν :=
    hΨlim.eventually (gt_mem_nhds (by rw [hν]; linarith))
  obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0' : 0 < u := hu0
  set r₀ : ℝ := min (u / 2) (1 / 2) with hr₀
  have hr₀0 : 0 < r₀ := lt_min (by linarith) (by norm_num)
  have hr₀u : r₀ < u := (min_le_left _ _).trans_lt (by linarith)
  have hr₀1 : r₀ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hbound : ∀ s, 0 < s → s < r₀ → Φ r₀ ≤ Φ s + (J - ν) * (r₀ - s) := by
    intro s hs hsr
    have hcont : ContinuousOn Φ (Icc s r₀) := fun x hx =>
      (hderiv x (hs.trans_le hx.1)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hcΨ⟩ := exists_hasDerivAt_eq_slope Φ Ψ hsr hcont
      (fun x hx => hderiv x (hs.trans hx.1))
    have hΨc : Ψ c < J - ν := hu ⟨hs.trans hc.1, hc.2.trans hr₀u⟩
    rw [hcΨ, div_lt_iff₀ (by linarith)] at hΨc
    linarith
  have hlim : Tendsto (fun s => Φ s + (J - ν) * (r₀ - s)) (𝓝[>] 0)
      (𝓝 ((∫ x, g x * χ x) + (J - ν) * (r₀ - 0))) := by
    refine hΦlim.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub ?_))
    exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle2 : Φ r₀ ≤ (∫ x, g x * χ x) + (J - ν) * (r₀ - 0) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀0] with s hs
    exact hbound s hs.1 hs.2
  have := hΦge r₀ hr₀0 hr₀1
  have h3 : F * r₀ * ∫ x, χ x = J * r₀ := by rw [hJ]; ring
  have h4 : 0 < ν * r₀ := mul_pos hν0 hr₀0
  nlinarith

end SGPT.NPP.LogConcavityDinew
