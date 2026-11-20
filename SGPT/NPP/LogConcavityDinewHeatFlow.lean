import SGPT.NPP.LogConcavityDinewHeatKernel
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The heat flow of a function of quadratic growth

For `g : ℂⁿ → ℝ` of quadratic growth, `heatFlow g t x = π^{-n} ∫ K(t, x - y) g(y) dy` (with the
kernel of `SGPT.NPP.LogConcavityDinewHeatKernel`). We prove that it is jointly continuous for
`t > 0`, differentiable in `t` with derivative `π^{-n} ∫ ∂ₜK(t, x - y) g(y) dy`, and that it has a
second-order Taylor expansion in `x` whose quadratic part `M` satisfies
`stdTrace M = 4 ∂ₜ (heatFlow g)` (the heat equation for `(1/4) Δ`). These are the inputs of the
parabolic comparison argument in `SGPT.NPP.LogConcavityDinewViscosity`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- The heat flow `π^{-n} ∫ K(t, x - y) g(y) dy`. -/
def heatFlow (g : ComplexModel n → ℝ) (t : ℝ) (x : ComplexModel n) : ℝ :=
  (Real.pi ^ n)⁻¹ * ∫ y, heatKernel n t (x - y) * g y

/-! ### Gaussian domination -/

/-- The basic domination: a Gaussian centred at `x`, times a polynomial in `x - y`, times a
function of quadratic growth, is dominated by a Gaussian centred at `x'` when `‖x - x'‖ ≤ 1`. -/
theorem exists_gauss_dom {g : ComplexModel n → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2))
    {c : ℝ} (hc : 0 < c) (k : ℕ) (x' : ComplexModel n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ComplexModel n, ‖x - x'‖ ≤ 1 → ∀ y : ComplexModel n,
      Real.exp (-(‖x - y‖ ^ 2 / c)) * (1 + ‖x - y‖ ^ 2) ^ k * |g y| ≤
        D * Real.exp (-(‖x' - y‖ ^ 2 / (8 * c))) := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  set A₁ : ℝ := (2 * c) ^ k * k.factorial * Real.exp (1 / (2 * c)) with hA₁
  set A₂ : ℝ := 8 * c * Real.exp (1 / (8 * c)) with hA₂
  refine ⟨A₁ * Real.exp (1 / (2 * c)) * (2 * C * (1 + ‖x'‖ ^ 2)) * A₂, by positivity, ?_⟩
  intro x hx y
  have h1 := one_add_sq_pow_mul_exp_le hc k ‖x - y‖
  have h2 : Real.exp (-(‖x - y‖ ^ 2 / (2 * c))) ≤
      Real.exp (1 ^ 2 / (2 * c)) * Real.exp (-(‖x' - y‖ ^ 2 / (2 * (2 * c)))) :=
    exp_neg_sq_norm_sub_le (by positivity) hx
  have h3 : |g y| ≤ 2 * C * (1 + ‖x'‖ ^ 2) * (1 + ‖x' - y‖ ^ 2) := by
    refine (hC y).trans ?_
    have := one_add_sq_le_mul x' y
    nlinarith
  have h4 : (1 + ‖x' - y‖ ^ 2) * Real.exp (-(‖x' - y‖ ^ 2 / (4 * c))) ≤
      A₂ * Real.exp (-(‖x' - y‖ ^ 2 / (8 * c))) := by
    have := one_add_sq_pow_mul_exp_le (by positivity : 0 < 4 * c) 1 ‖x' - y‖
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at this
    rw [show 2 * (4 * c) = 8 * c by ring] at this
    exact this
  have e1 : (2 * (2 * c)) = 4 * c := by ring
  rw [e1] at h2
  simp only [one_pow] at h2
  calc Real.exp (-(‖x - y‖ ^ 2 / c)) * (1 + ‖x - y‖ ^ 2) ^ k * |g y|
      = ((1 + ‖x - y‖ ^ 2) ^ k * Real.exp (-(‖x - y‖ ^ 2 / c))) * |g y| := by ring
    _ ≤ (A₁ * Real.exp (-(‖x - y‖ ^ 2 / (2 * c)))) * |g y| :=
        mul_le_mul_of_nonneg_right (by simpa [hA₁] using h1) (abs_nonneg _)
    _ ≤ (A₁ * (Real.exp (1 / (2 * c)) * Real.exp (-(‖x' - y‖ ^ 2 / (4 * c))))) *
        (2 * C * (1 + ‖x'‖ ^ 2) * (1 + ‖x' - y‖ ^ 2)) := by gcongr
    _ = A₁ * Real.exp (1 / (2 * c)) * (2 * C * (1 + ‖x'‖ ^ 2)) *
        ((1 + ‖x' - y‖ ^ 2) * Real.exp (-(‖x' - y‖ ^ 2 / (4 * c)))) := by ring
    _ ≤ A₁ * Real.exp (1 / (2 * c)) * (2 * C * (1 + ‖x'‖ ^ 2)) *
        (A₂ * Real.exp (-(‖x' - y‖ ^ 2 / (8 * c)))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem integrable_gauss (x' : ComplexModel n) {c : ℝ} (hc : 0 < c) (D : ℝ) :
    Integrable (fun y : ComplexModel n => D * Real.exp (-(‖x' - y‖ ^ 2 / (8 * c)))) :=
  (integrable_exp_neg_sq_norm_div (by positivity) x').const_mul D

/-- The kernel, for `t ∈ [a, b]`, against a polynomial weight and a function of quadratic
growth. -/
theorem exists_kernel_dom {g : ComplexModel n → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) (x' : ComplexModel n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a b, ∀ x : ComplexModel n, ‖x - x'‖ ≤ 1 → ∀ y : ComplexModel n,
      heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ k * |g y| ≤
        D * Real.exp (-(‖x' - y‖ ^ 2 / (8 * b))) := by
  obtain ⟨D, hD0, hD⟩ := exists_gauss_dom hC (ha.trans_le hab) k x'
  refine ⟨D / a ^ n, by positivity, fun t ht x hx y => ?_⟩
  have hK := heatKernel_le_of_mem_Icc ha ht.1 ht.2 (x - y)
  calc heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ k * |g y|
      ≤ Real.exp (-(‖x - y‖ ^ 2 / b)) / a ^ n * (1 + ‖x - y‖ ^ 2) ^ k * |g y| := by gcongr
    _ = (Real.exp (-(‖x - y‖ ^ 2 / b)) * (1 + ‖x - y‖ ^ 2) ^ k * |g y|) / a ^ n := by ring
    _ ≤ (D * Real.exp (-(‖x' - y‖ ^ 2 / (8 * b)))) / a ^ n :=
        div_le_div_of_nonneg_right (hD x hx y) (by positivity)
    _ = _ := by ring

/-! ### Pointwise bounds of the derivatives -/

theorem abs_heatKernelD_le {t : ℝ} (ht : 0 < t) (w h : ComplexModel n) :
    |heatKernelD t w h| ≤ heatKernel n t w * (1 + ‖w‖ ^ 2) ^ 1 * (2 / t * ‖h‖) := by
  unfold heatKernelD
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / t),
    abs_of_nonneg (heatKernel_nonneg ht w)]
  have hi := abs_real_inner_le_norm w h
  have hw : ‖w‖ ≤ 1 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖w‖ - 1)]
  have := heatKernel_nonneg ht w
  calc 2 / t * |inner ℝ w h| * heatKernel n t w ≤ 2 / t * (‖w‖ * ‖h‖) * heatKernel n t w := by
        gcongr
    _ ≤ 2 / t * ((1 + ‖w‖ ^ 2) * ‖h‖) * heatKernel n t w := by gcongr
    _ = _ := by ring

theorem abs_heatKernelDD_le {t : ℝ} (ht : 0 < t) (w h k : ComplexModel n) :
    |heatKernelDD t w h k| ≤
      heatKernel n t w * (1 + ‖w‖ ^ 2) ^ 1 * ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖k‖) := by
  unfold heatKernelDD
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht w), pow_one,
    mul_assoc (heatKernel n t w) (1 + ‖w‖ ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg ht w)
  have h1 := abs_real_inner_le_norm w h
  have h2 := abs_real_inner_le_norm w k
  have h3 := abs_real_inner_le_norm h k
  calc abs (4 / t ^ 2 * inner ℝ w h * inner ℝ w k - 2 / t * inner ℝ h k)
      ≤ 4 / t ^ 2 * (|inner ℝ w h| * |inner ℝ w k|) + 2 / t * |inner ℝ h k| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 4 / t ^ 2),
          abs_of_pos (by positivity : 0 < 2 / t)]
        ring_nf; rfl
    _ ≤ 4 / t ^ 2 * ((‖w‖ * ‖h‖) * (‖w‖ * ‖k‖)) + 2 / t * (‖h‖ * ‖k‖) := by gcongr
    _ = (4 / t ^ 2 * ‖w‖ ^ 2 + 2 / t) * (‖h‖ * ‖k‖) := by ring
    _ ≤ (1 + ‖w‖ ^ 2) * (4 / t ^ 2 + 2 / t) * (‖h‖ * ‖k‖) := by
        gcongr
        nlinarith [sq_nonneg ‖w‖, (by positivity : (0 : ℝ) ≤ 4 / t ^ 2),
          (by positivity : (0 : ℝ) ≤ 2 / t)]
    _ = _ := by ring

theorem abs_heatKernelT_le {t : ℝ} (ht : 0 < t) (w : ComplexModel n) :
    |heatKernelT t w| ≤ heatKernel n t w * (1 + ‖w‖ ^ 2) ^ 1 * (1 / t ^ 2 + n / t) := by
  unfold heatKernelT
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht w), pow_one,
    mul_assoc (heatKernel n t w) (1 + ‖w‖ ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg ht w)
  calc abs (‖w‖ ^ 2 / t ^ 2 - n / t) ≤ ‖w‖ ^ 2 / t ^ 2 + n / t := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ (1 + ‖w‖ ^ 2) * (1 / t ^ 2 + n / t) := by
        have h1 : ‖w‖ ^ 2 / t ^ 2 ≤ (1 + ‖w‖ ^ 2) * (1 / t ^ 2) := by
          rw [mul_one_div]; gcongr; linarith
        have h2 : (n : ℝ) / t ≤ (1 + ‖w‖ ^ 2) * (n / t) := by
          have : (0 : ℝ) ≤ n / t := by positivity
          nlinarith [sq_nonneg ‖w‖]
        nlinarith

/-! ### Integrability, continuity and the time derivative -/

section Flow

variable {g : ComplexModel n → ℝ} {C : ℝ}

theorem aestronglyMeasurable_mul_of_continuous {f : ComplexModel n → ℝ} (hf : Continuous f)
    (hg : Measurable g) : AEStronglyMeasurable (fun y => f y * g y) :=
  (hf.measurable.mul hg).aestronglyMeasurable

theorem continuous_heatKernel_sub (t : ℝ) (x : ComplexModel n) :
    Continuous (fun y : ComplexModel n => heatKernel n t (x - y)) := by
  unfold heatKernel
  fun_prop

theorem integrable_heatKernel_mul (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : ComplexModel n) :
    Integrable (fun y => heatKernel n t (x - y) * g y) := by
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC ht le_rfl 0 x
  refine (integrable_gauss x ht D).mono'
    (aestronglyMeasurable_mul_of_continuous (continuous_heatKernel_sub t x) hg)
    (ae_of_all _ fun y => ?_)
  have := hD t ⟨le_rfl, le_rfl⟩ x (by simp) y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht _)]
  simpa using this

theorem integrable_heatKernelT_mul (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : ComplexModel n) :
    Integrable (fun y => heatKernelT t (x - y) * g y) := by
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC ht le_rfl 1 x
  have hcont : Continuous (fun y : ComplexModel n => heatKernelT t (x - y)) := by
    unfold heatKernelT heatKernel; fun_prop
  refine ((integrable_gauss x ht D).mul_const (1 / t ^ 2 + n / t)).mono'
    (aestronglyMeasurable_mul_of_continuous hcont hg) (ae_of_all _ fun y => ?_)
  have h1 := hD t ⟨le_rfl, le_rfl⟩ x (by simp) y
  have h2 := abs_heatKernelT_le ht (x - y)
  rw [Real.norm_eq_abs, abs_mul]
  calc |heatKernelT t (x - y)| * |g y|
      ≤ heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * (1 / t ^ 2 + n / t) * |g y| := by gcongr
    _ = heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * |g y| * (1 / t ^ 2 + n / t) := by ring
    _ ≤ D * Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) * (1 / t ^ 2 + n / t) := by gcongr

theorem integrable_heatKernelD_mul (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x h : ComplexModel n) :
    Integrable (fun y => heatKernelD t (x - y) h * g y) := by
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC ht le_rfl 1 x
  have hcont : Continuous (fun y : ComplexModel n => heatKernelD t (x - y) h) := by
    unfold heatKernelD heatKernel; fun_prop
  refine ((integrable_gauss x ht D).mul_const (2 / t * ‖h‖)).mono'
    (aestronglyMeasurable_mul_of_continuous hcont hg) (ae_of_all _ fun y => ?_)
  have h1 := hD t ⟨le_rfl, le_rfl⟩ x (by simp) y
  have h2 := abs_heatKernelD_le ht (x - y) h
  rw [Real.norm_eq_abs, abs_mul]
  calc |heatKernelD t (x - y) h| * |g y|
      ≤ heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * (2 / t * ‖h‖) * |g y| := by gcongr
    _ = heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * |g y| * (2 / t * ‖h‖) := by ring
    _ ≤ D * Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) * (2 / t * ‖h‖) := by gcongr

theorem integrable_heatKernelDD_mul (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x h k : ComplexModel n) :
    Integrable (fun y => heatKernelDD t (x - y) h k * g y) := by
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC ht le_rfl 1 x
  have hcont : Continuous (fun y : ComplexModel n => heatKernelDD t (x - y) h k) := by
    unfold heatKernelDD heatKernel; fun_prop
  refine ((integrable_gauss x ht D).mul_const ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖k‖)).mono'
    (aestronglyMeasurable_mul_of_continuous hcont hg) (ae_of_all _ fun y => ?_)
  have h1 := hD t ⟨le_rfl, le_rfl⟩ x (by simp) y
  have h2 := abs_heatKernelDD_le ht (x - y) h k
  rw [Real.norm_eq_abs, abs_mul]
  calc |heatKernelDD t (x - y) h k| * |g y|
      ≤ heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖k‖) *
          |g y| := by gcongr
    _ = heatKernel n t (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * |g y| *
          ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖k‖) := by ring
    _ ≤ D * Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) * ((4 / t ^ 2 + 2 / t) * ‖h‖ * ‖k‖) := by
        gcongr

/-- **Joint continuity** of the heat flow for positive time. -/
theorem continuousAt_heatFlow (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {x' : ComplexModel n} {t' : ℝ} (ht' : 0 < t') :
    ContinuousAt (fun p : ComplexModel n × ℝ => heatFlow g p.2 p.1) (x', t') := by
  unfold heatFlow
  apply ContinuousAt.mul continuousAt_const
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC (by positivity : 0 < t' / 2)
    (by linarith : t' / 2 ≤ 2 * t') 0 x'
  have hnear : ∀ᶠ p : ComplexModel n × ℝ in 𝓝 (x', t'),
      ‖p.1 - x'‖ ≤ 1 ∧ p.2 ∈ Icc (t' / 2) (2 * t') := by
    have h1 : ∀ᶠ p : ComplexModel n × ℝ in 𝓝 (x', t'), ‖p.1 - x'‖ < 1 := by
      have : Continuous (fun p : ComplexModel n × ℝ => ‖p.1 - x'‖) := by fun_prop
      exact this.continuousAt.eventually (gt_mem_nhds (by simp))
    have h2 : ∀ᶠ p : ComplexModel n × ℝ in 𝓝 (x', t'), p.2 ∈ Ioo (t' / 2) (2 * t') :=
      continuous_snd.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1.le, Ioo_subset_Icc_self hp2⟩
  refine continuousAt_of_dominated (bound := fun y => D * Real.exp (-(‖x' - y‖ ^ 2 /
    (8 * (2 * t'))))) ?_ ?_ (integrable_gauss x' (by positivity) D) ?_
  · exact Eventually.of_forall fun p =>
      aestronglyMeasurable_mul_of_continuous (continuous_heatKernel_sub p.2 p.1) hg
  · filter_upwards [hnear] with p hp
    refine ae_of_all _ fun y => ?_
    have := hD p.2 hp.2 p.1 hp.1 y
    have hp0 : 0 < p.2 := by linarith [hp.2.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hp0 _)]
    simpa using this
  · refine ae_of_all _ fun y => ?_
    have hne : t' ≠ 0 := ht'.ne'
    unfold heatKernel
    apply ContinuousAt.mul _ continuousAt_const
    refine ContinuousAt.div (f := fun p : ComplexModel n × ℝ => Real.exp (-(‖p.1 - y‖ ^ 2 / p.2)))
      (g := fun p : ComplexModel n × ℝ => p.2 ^ n) ?_ ?_ (by simpa using pow_ne_zero n hne)
    · apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.neg
      apply ContinuousAt.div _ continuousAt_snd hne
      exact ((continuous_fst.sub continuous_const).norm.pow 2).continuousAt
    · exact continuousAt_snd.pow n

theorem continuousOn_heatFlow (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) :
    ContinuousOn (fun p : ComplexModel n × ℝ => heatFlow g p.2 p.1) {p | 0 < p.2} :=
  fun p hp => (continuousAt_heatFlow hC hg (x' := p.1) (t' := p.2) hp).continuousWithinAt

/-- The time derivative of the heat flow, `π^{-n} ∫ ∂ₜK(t, x - y) g(y) dy`. -/
def heatFlowT (g : ComplexModel n → ℝ) (t : ℝ) (x : ComplexModel n) : ℝ :=
  (Real.pi ^ n)⁻¹ * ∫ y, heatKernelT t (x - y) * g y

theorem hasDerivAt_heatFlow_time (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x : ComplexModel n) :
    HasDerivAt (fun s => heatFlow g s x) (heatFlowT g t x) t := by
  unfold heatFlow heatFlowT
  apply HasDerivAt.const_mul
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC (by positivity : 0 < t / 2)
    (by linarith : t / 2 ≤ 2 * t) 1 x
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => heatKernel n s (x - y) * g y)
    (F' := fun s y => heatKernelT s (x - y) * g y)
    (bound := fun y => D * Real.exp (-(‖x - y‖ ^ 2 / (8 * (2 * t)))) *
      (1 / (t / 2) ^ 2 + n / (t / 2))) hs ?_ (integrable_heatKernel_mul hC hg ht x) ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s =>
      aestronglyMeasurable_mul_of_continuous (continuous_heatKernel_sub s x) hg
  · have hcont : Continuous (fun y : ComplexModel n => heatKernelT t (x - y)) := by
      unfold heatKernelT heatKernel; fun_prop
    exact aestronglyMeasurable_mul_of_continuous hcont hg
  · refine ae_of_all _ fun y s hs' => ?_
    have hs0 : 0 < s := by linarith [hs'.1]
    have h1 := hD s (Ioo_subset_Icc_self hs') x (by simp) y
    have h2 := abs_heatKernelT_le hs0 (x - y)
    have h3 : 1 / s ^ 2 + n / s ≤ 1 / (t / 2) ^ 2 + n / (t / 2) := by
      gcongr <;> linarith [hs'.1]
    rw [Real.norm_eq_abs, abs_mul]
    calc |heatKernelT s (x - y)| * |g y|
        ≤ heatKernel n s (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * (1 / s ^ 2 + n / s) * |g y| := by
          gcongr
      _ ≤ heatKernel n s (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * (1 / (t / 2) ^ 2 + n / (t / 2)) *
          |g y| := by
          have := heatKernel_nonneg hs0 (x - y)
          gcongr
      _ = heatKernel n s (x - y) * (1 + ‖x - y‖ ^ 2) ^ 1 * |g y| *
          (1 / (t / 2) ^ 2 + n / (t / 2)) := by ring
      _ ≤ _ := by gcongr
  · exact (integrable_gauss x (by positivity) D).mul_const _
  · refine ae_of_all _ fun y s hs' => ?_
    have hs0 : 0 < s := by linarith [hs'.1]
    exact (hasDerivAt_heatKernel_time hs0 (x - y)).mul_const (g y)

end Flow

/-! ### The second-order Taylor expansion in space -/

section Taylor

variable {g : ComplexModel n → ℝ} {C : ℝ}

/-- The gradient of the heat flow (as a vector). -/
def heatFlowGrad (g : ComplexModel n → ℝ) (t : ℝ) (x₀ : ComplexModel n) : ComplexModel n :=
  (Real.pi ^ n)⁻¹ • ∫ y, (-(2 / t) * heatKernel n t (x₀ - y) * g y) • (x₀ - y)

/-- The Hessian of the heat flow, as a scalar function of two directions. -/
def heatFlowHess (g : ComplexModel n → ℝ) (t : ℝ) (x₀ h k : ComplexModel n) : ℝ :=
  (Real.pi ^ n)⁻¹ * ∫ y, heatKernelDD t (x₀ - y) h k * g y

theorem integrable_grad_integrand (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ : ComplexModel n) :
    Integrable (fun y => (-(2 / t) * heatKernel n t (x₀ - y) * g y) • (x₀ - y)) := by
  obtain ⟨D, -, hD⟩ := exists_kernel_dom hC ht le_rfl 1 x₀
  have hm : AEStronglyMeasurable (fun y => (-(2 / t) * heatKernel n t (x₀ - y) * g y) • (x₀ - y)) :=
    (((measurable_const.mul (continuous_heatKernel_sub t x₀).measurable).mul hg).smul
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine ((integrable_gauss x₀ ht D).mul_const (2 / t)).mono' hm (ae_of_all _ fun y => ?_)
  have h1 := hD t ⟨le_rfl, le_rfl⟩ x₀ (by simp) y
  have hw : ‖x₀ - y‖ ≤ (1 + ‖x₀ - y‖ ^ 2) ^ 1 := by
    rw [pow_one]; nlinarith [sq_nonneg (‖x₀ - y‖ - 1)]
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / t),
    abs_of_nonneg (heatKernel_nonneg ht _)]
  have := heatKernel_nonneg ht (x₀ - y)
  calc 2 / t * heatKernel n t (x₀ - y) * |g y| * ‖x₀ - y‖
      ≤ 2 / t * heatKernel n t (x₀ - y) * |g y| * (1 + ‖x₀ - y‖ ^ 2) ^ 1 := by gcongr
    _ = heatKernel n t (x₀ - y) * (1 + ‖x₀ - y‖ ^ 2) ^ 1 * |g y| * (2 / t) := by ring
    _ ≤ D * Real.exp (-(‖x₀ - y‖ ^ 2 / (8 * t))) * (2 / t) := by gcongr

theorem inner_heatFlowGrad (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ h : ComplexModel n) :
    inner ℝ (heatFlowGrad g t x₀) h =
      (Real.pi ^ n)⁻¹ * ∫ y, heatKernelD t (x₀ - y) h * g y := by
  rw [heatFlowGrad, real_inner_smul_left, real_inner_comm,
    ← integral_inner (integrable_grad_integrand hC hg ht x₀) h]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [real_inner_smul_right, heatKernelD]
  rw [real_inner_comm]
  ring

theorem heatFlowHess_add_left (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ h h' k : ComplexModel n) :
    heatFlowHess g t x₀ (h + h') k = heatFlowHess g t x₀ h k + heatFlowHess g t x₀ h' k := by
  unfold heatFlowHess
  rw [← mul_add, ← integral_add (integrable_heatKernelDD_mul hC hg ht x₀ h k)
    (integrable_heatKernelDD_mul hC hg ht x₀ h' k)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [heatKernelDD, inner_add_right, inner_add_left]
  ring

theorem heatFlowHess_smul_left (x₀ : ComplexModel n) (t c : ℝ) (h k : ComplexModel n) :
    heatFlowHess g t x₀ (c • h) k = c * heatFlowHess g t x₀ h k := by
  unfold heatFlowHess
  have e : (fun y => heatKernelDD t (x₀ - y) (c • h) k * g y) =
      fun y => c * (heatKernelDD t (x₀ - y) h k * g y) := by
    funext y; simp only [heatKernelDD, real_inner_smul_right, real_inner_smul_left]; ring
  rw [e, integral_const_mul]
  ring

theorem heatFlowHess_comm (x₀ : ComplexModel n) (t : ℝ) (h k : ComplexModel n) :
    heatFlowHess g t x₀ h k = heatFlowHess g t x₀ k h := by
  unfold heatFlowHess
  congr 2
  funext y
  simp only [heatKernelDD, real_inner_comm h k]
  ring

/-- The Hessian is a genuine continuous bilinear form. -/
theorem exists_heatFlowHess_clm (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ : ComplexModel n) :
    ∃ M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ, ∀ h k, M h k = heatFlowHess g t x₀ h k := by
  let B : ComplexModel n →ₗ[ℝ] ComplexModel n →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (heatFlowHess g t x₀) (heatFlowHess_add_left hC hg ht x₀)
      (fun c h k => by rw [heatFlowHess_smul_left, smul_eq_mul])
      (fun h k k' => by
        rw [heatFlowHess_comm, heatFlowHess_add_left hC hg ht, heatFlowHess_comm x₀ t k,
          heatFlowHess_comm x₀ t k'])
      (fun c h k => by
        rw [heatFlowHess_comm, heatFlowHess_smul_left, heatFlowHess_comm x₀ t k, smul_eq_mul])
  let B' : ComplexModel n →ₗ[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (ComplexModel n →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B
  refine ⟨LinearMap.toContinuousLinearMap B', fun h k => ?_⟩
  simp [B', B]

/-- **Second-order Taylor expansion of the heat flow** at a point, with cubic remainder. -/
theorem heatFlow_taylor (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ : ComplexModel n) :
    ∃ C' : ℝ, ∀ h : ComplexModel n, ‖h‖ ≤ 1 →
      |heatFlow g t (x₀ + h) - heatFlow g t x₀ - inner ℝ (heatFlowGrad g t x₀) h -
          heatFlowHess g t x₀ h h / 2| ≤ C' * ‖h‖ ^ 3 := by
  obtain ⟨CK, hCK0, hCK⟩ := abs_heatKernel_taylor_le (n := n) ht
  obtain ⟨D, hD0, hD⟩ := exists_gauss_dom hC (by positivity : 0 < 4 * t) 0 x₀
  have hcont4 : Continuous (fun y : ComplexModel n => Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t)))) := by
    fun_prop
  have hInt : Integrable (fun y : ComplexModel n =>
      Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t))) * |g y|) := by
    refine (integrable_gauss x₀ (by positivity : 0 < 4 * t) D).mono'
      ((hcont4.measurable.mul (continuous_abs.measurable.comp hg)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    have := hD x₀ (by simp) y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_abs]
    simpa using this
  refine ⟨(Real.pi ^ n)⁻¹ * CK * ∫ y, Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t))) * |g y|,
    fun h hh => ?_⟩
  have hI0 := integrable_heatKernel_mul hC hg ht x₀
  have hI1 := integrable_heatKernel_mul hC hg ht (x₀ + h)
  have hI2 := integrable_heatKernelD_mul hC hg ht x₀ h
  have hI3 := integrable_heatKernelDD_mul hC hg ht x₀ h h
  rw [inner_heatFlowGrad hC hg ht]
  unfold heatFlow heatFlowHess
  set R : ComplexModel n → ℝ := fun y => (heatKernel n t (x₀ - y + h) - heatKernel n t (x₀ - y) -
    heatKernelD t (x₀ - y) h - heatKernelDD t (x₀ - y) h h / 2) * g y with hRdef
  have hRint : Integrable R := by
    have := ((hI1.sub hI0).sub hI2).sub (hI3.div_const 2)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [hRdef, Pi.sub_apply]
    rw [show x₀ + h - y = x₀ - y + h by abel]
    ring
  have e : (Real.pi ^ n)⁻¹ * (∫ y, heatKernel n t (x₀ + h - y) * g y) -
      (Real.pi ^ n)⁻¹ * (∫ y, heatKernel n t (x₀ - y) * g y) -
      (Real.pi ^ n)⁻¹ * (∫ y, heatKernelD t (x₀ - y) h * g y) -
      (Real.pi ^ n)⁻¹ * (∫ y, heatKernelDD t (x₀ - y) h h * g y) / 2 =
      (Real.pi ^ n)⁻¹ * ∫ y, R y := by
    have e2 : ∫ y, R y = ∫ y, (heatKernel n t (x₀ + h - y) * g y - heatKernel n t (x₀ - y) * g y -
        heatKernelD t (x₀ - y) h * g y - heatKernelDD t (x₀ - y) h h * g y / 2) := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hRdef]
      rw [show x₀ + h - y = x₀ - y + h by abel]
      ring
    rw [e2, integral_sub (by exact (hI1.sub hI0).sub hI2) (by exact hI3.div_const 2),
      integral_sub (by exact hI1.sub hI0) hI2, integral_sub hI1 hI0, integral_div]
    ring
  have hRle : ∀ y, |R y| ≤ CK * ‖h‖ ^ 3 * (Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t))) * |g y|) := by
    intro y
    simp only [hRdef]
    rw [abs_mul]
    calc |heatKernel n t (x₀ - y + h) - heatKernel n t (x₀ - y) - heatKernelD t (x₀ - y) h -
          heatKernelDD t (x₀ - y) h h / 2| * |g y|
        ≤ CK * ‖h‖ ^ 3 * Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t))) * |g y| :=
          mul_le_mul_of_nonneg_right (hCK (x₀ - y) h hh) (abs_nonneg _)
      _ = _ := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.pi ^ n)⁻¹)]
  calc (Real.pi ^ n)⁻¹ * |∫ y, R y| ≤ (Real.pi ^ n)⁻¹ * ∫ y, |R y| := by
        gcongr; exact abs_integral_le_integral_abs
    _ ≤ (Real.pi ^ n)⁻¹ * ∫ y, CK * ‖h‖ ^ 3 * (Real.exp (-(‖x₀ - y‖ ^ 2 / (4 * t))) * |g y|) := by
        exact mul_le_mul_of_nonneg_left (integral_mono hRint.abs (hInt.const_mul _) hRle)
          (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- **The heat equation for the flow**: the trace of the Hessian in the real frame is
`4 ∂ₜ heatFlow`. -/
theorem sum_heatFlowHess_coordinate (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g)
    {t : ℝ} (ht : 0 < t) (x₀ : ComplexModel n) :
    ∑ j, (heatFlowHess g t x₀ (coordinateVector j) (coordinateVector j) +
      heatFlowHess g t x₀ (Complex.I • coordinateVector j) (Complex.I • coordinateVector j)) =
      4 * heatFlowT g t x₀ := by
  unfold heatFlowHess heatFlowT
  simp only [← mul_add, ← Finset.mul_sum]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable (fun y =>
      heatKernelDD t (x₀ - y) (coordinateVector j) (coordinateVector j) * g y +
      heatKernelDD t (x₀ - y) (Complex.I • coordinateVector j) (Complex.I • coordinateVector j) *
        g y) := fun j _ =>
    (integrable_heatKernelDD_mul hC hg ht x₀ _ _).add (integrable_heatKernelDD_mul hC hg ht x₀ _ _)
  have e1 : ∀ j, (∫ y, heatKernelDD t (x₀ - y) (coordinateVector j) (coordinateVector j) * g y) +
      (∫ y, heatKernelDD t (x₀ - y) (Complex.I • coordinateVector j)
        (Complex.I • coordinateVector j) * g y) =
      ∫ y, (heatKernelDD t (x₀ - y) (coordinateVector j) (coordinateVector j) * g y +
      heatKernelDD t (x₀ - y) (Complex.I • coordinateVector j) (Complex.I • coordinateVector j) *
        g y) := fun j =>
    (integral_add (integrable_heatKernelDD_mul hC hg ht x₀ _ _)
      (integrable_heatKernelDD_mul hC hg ht x₀ _ _)).symm
  simp only [e1]
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [← add_mul, ← Finset.sum_mul, sum_heatKernelDD_coordinate]
  ring

end Taylor

end SGPT.NPP.LogConcavityDinew
