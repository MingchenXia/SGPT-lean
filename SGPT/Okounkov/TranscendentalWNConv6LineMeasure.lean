import SGPT.Okounkov.TranscendentalWNConv6Obstacle
import SGPT.Toric.ProjectiveScalarSmoothMeasure
import SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The measures `ω_k` on `ℂ` (WN21 §6; lane WN-CONV6)

Blueprint `tok-wn-conv6:line-measure` (chapter `claude-tok-wn-conv6`); source WN21 §6
(`ω_k = ω_FS + ddᶜg_k = ddᶜχ(log |τ|² + k)`, a probability measure, the pushforward of `ω_0` under
`τ ↦ e^{-k/2} τ`, with `ω(\{|τ| < r\}) > 0` for all `r > 0`).

`cutoffLineDensity χ k z` is the Monge–Ampère density (TN's `smoothDensity`, i.e. `Δ/(4π)`) of
`cutoffLineProfile χ k = χ(log |z|² + k)` on the one-dimensional model, and
`cutoffLineMeasure χ k` is the measure with this density on `ℂ`.

* `cutoffLineDensity_eq_of_ne`: for `z ≠ 0`, the density is `χ''(log |z|² + k) / (π |z|²)`;
  `cutoffLineDensity_eq_of_small`: for `eᵏ |z|² < e⁻¹` it is `eᵏ / π`; it is `≥ 0`.
* `cutoffLineMeasure_singleton_zero`: no atom at `0`.
* `cutoffLineMeasure_univ`: `ω_k(ℂ) = 1` (polar coordinates, `r = e^{(s - k)/2}`, and
  `∫_ℝ χ'' = 1`).
* `le_cutoffLineMeasure_ball`: `ω_k(B(0, r e^{-k/2})) ≥ min(r, e^{-1/2})²` for all `k`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal Real
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Toric

/-! ### The second derivative of the cutoff -/

namespace IsWNCutoff

variable {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
include hχ

theorem continuous_deriv2 : Continuous (deriv (deriv χ)) :=
  (hχ.contDiff.iterate_deriv 2).continuous

theorem deriv2_nonneg (x : ℝ) : 0 ≤ deriv (deriv χ) x := hχ.monotone_deriv.deriv_nonneg

theorem deriv2_of_neg {x : ℝ} (hx : x < -1) : deriv (deriv χ) x = Real.exp x := by
  have hev : deriv χ =ᶠ[𝓝 x] Real.exp := by
    filter_upwards [Iio_mem_nhds hx] with y hy using hχ.deriv_of_neg hy
  rw [hev.deriv_eq, Real.deriv_exp]

theorem deriv2_of_pos {x : ℝ} (hx : 0 < x) : deriv (deriv χ) x = 0 := by
  have hev : deriv χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using hχ.deriv_of_pos hy
  rw [hev.deriv_eq, deriv_const]

theorem differentiable_deriv : Differentiable ℝ (deriv χ) :=
  (hχ.contDiff.iterate_deriv 1).differentiable (by simp)

/-- `∫_ℝ χ'' = 1`. -/
theorem lintegral_deriv2 : ∫⁻ s, ENNReal.ofReal (deriv (deriv χ) s) = 1 := by
  have hc := hχ.continuous_deriv2
  have h1 : ∫⁻ s in Iic (-2 : ℝ), ENNReal.ofReal (deriv (deriv χ) s) =
      ENNReal.ofReal (Real.exp (-2)) := by
    rw [← integral_exp_Iic (-2 : ℝ)]
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_Iic (-2))
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    refine setLIntegral_congr_fun measurableSet_Iic fun s hs => ?_
    rw [hχ.deriv2_of_neg (lt_of_le_of_lt hs (by norm_num))]
  have h2 : ∫⁻ s in Ioc (-2 : ℝ) 1, ENNReal.ofReal (deriv (deriv χ) s) =
      ENNReal.ofReal (1 - Real.exp (-2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall hχ.deriv2_nonneg)]
    congr 1
    rw [← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hχ.differentiable_deriv x)
        (hc.intervalIntegrable _ _),
      hχ.deriv_of_pos one_pos, hχ.deriv_of_neg (by norm_num)]
  have h3 : ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (deriv (deriv χ) s) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun s hs => by
      rw [hχ.deriv2_of_pos (lt_trans one_pos hs), ENNReal.ofReal_zero]]
    simp
  have hsplit : (univ : Set ℝ) = Iic (-2) ∪ (Ioc (-2) 1 ∪ Ioi 1) := by
    ext s; simp only [mem_univ, mem_union, mem_Iic, mem_Ioc, mem_Ioi, true_iff]
    by_cases h : s ≤ -2
    · exact Or.inl h
    · by_cases h' : s ≤ 1
      · exact Or.inr (Or.inl ⟨lt_of_not_ge h, h'⟩)
      · exact Or.inr (Or.inr (lt_of_not_ge h'))
  rw [← setLIntegral_univ, hsplit,
    lintegral_union (measurableSet_Ioc.union measurableSet_Ioi)
      (disjoint_union_right.mpr ⟨Iic_disjoint_Ioc le_rfl, Iic_disjoint_Ioi (by norm_num)⟩),
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, h1, h2, h3, add_zero]
  have hle : 0 ≤ 1 - Real.exp (-2) := by
    have h := Real.exp_le_exp.mpr (show (-2 : ℝ) ≤ 0 by norm_num)
    rw [Real.exp_zero] at h
    linarith
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hle, add_sub_cancel, ENNReal.ofReal_one]

end IsWNCutoff

/-! ### The density -/

/-- The Monge–Ampère density of `χ(log |z|² + k)` on the one-dimensional model (WN21's `ω_k`). -/
def cutoffLineDensity (χ : ℝ → ℝ) (k : ℕ) (z : ComplexModel 1) : ℝ :=
  smoothDensity (cutoffLineProfile χ k) z

/-- The measure `ω_k` on `ℂ`. -/
def cutoffLineMeasure (χ : ℝ → ℝ) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun τ => ENNReal.ofReal (cutoffLineDensity χ k (projectiveModelEquiv τ))

theorem cutoffLineMeasure_singleton_zero (χ : ℝ → ℝ) (k : ℕ) :
    cutoffLineMeasure χ k {0} = 0 :=
  withDensity_absolutelyContinuous _ _ (measure_singleton 0)

theorem normSq_projectiveModelEquiv (τ : ℂ) : ‖(projectiveModelEquiv τ) 0‖ ^ 2 = ‖τ‖ ^ 2 := by
  rw [projectiveModelEquiv_apply_zero]

theorem norm_sq_eq_zero_coord (z : ComplexModel 1) : ‖z‖ ^ 2 = ‖z 0‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]

/-- For `eᵏ |z|² < e⁻¹` the density is `eᵏ / π`. -/
theorem cutoffLineDensity_eq_of_small {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    {z : ComplexModel 1} (hz : Real.exp k * ‖z 0‖ ^ 2 < Real.exp (-1)) :
    cutoffLineDensity χ k z = Real.exp k / π := by
  have hn : Continuous fun y : ComplexModel 1 => Real.exp k * ‖y 0‖ ^ 2 :=
    continuous_const.mul (contDiff_normSq_zero.continuous)
  have hev : cutoffLineProfile χ k =ᶠ[𝓝 z]
      (Real.exp k : ℝ) • (fun y : ComplexModel 1 => ‖y‖ ^ 2) + fun _ => (-1 : ℝ) := by
    filter_upwards [hn.continuousAt.eventually (gt_mem_nhds hz)] with y hy
    rw [cutoffLineProfile, cutoffLog_of_le hχ (by positivity) hy.le]
    simp [norm_sq_eq_zero_coord, sub_eq_add_neg]
  have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel 1 => ‖y‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt
  unfold cutoffLineDensity smoothDensity
  have h3 : ContDiffAt ℝ 2 ((Real.exp k : ℝ) • (fun y : ComplexModel 1 => ‖y‖ ^ 2)) z := by
    have := h2.const_smul (Real.exp k)
    exact this
  rw [SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity.complexHessian_congr_of_eventuallyEq hev,
    complexHessian_add h3 contDiffAt_const, complexHessian_smul h2,
    complexHessian_norm_sq, complexHessian_const, add_zero]
  have hre : (Complex.exp (k : ℂ)).re = Real.exp k := by
    rw [← Complex.ofReal_natCast, Complex.exp_ofReal_re]
  simp only [Nat.factorial_one, Nat.cast_one, pow_one]
  simp [hre]
  ring

/-- For `z ≠ 0` the density is `χ''(log |z|² + k) / (π |z|²)`. -/
theorem cutoffLineDensity_eq_of_ne {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    cutoffLineDensity χ k z =
      deriv (deriv χ) (Real.log (‖z 0‖ ^ 2) + k) / (π * ‖z 0‖ ^ 2) := by
  set h : ℝ → ℝ := fun s => χ (s + k) with hh
  have hhs : ContDiff ℝ ∞ h := hχ.contDiff.comp (contDiff_id.add contDiff_const)
  have hzD : z ∈ (⟨complexTorus 1, isOpen_complexTorus 1⟩ : TopologicalSpace.Opens _) := by
    intro i; rw [Fin.eq_zero i]; exact hz
  have hcoord : Continuous fun y : ComplexModel 1 => y 0 :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous
  have hev : cutoffLineProfile χ k =ᶠ[𝓝 z] scalarPuncturedProfile h := by
    filter_upwards [hcoord.continuousAt.eventually_ne hz] with y hy
    have hy2 : 0 < ‖y 0‖ ^ 2 := by positivity
    rw [cutoffLineProfile, cutoffLog_of_pos χ (by positivity), scalarPuncturedProfile,
      tropicalization_apply_eq_log_norm_sq, Real.log_mul (Real.exp_pos _).ne' hy2.ne',
      Real.log_exp, hh]
    simp only [add_comm]
  have hd : smoothDensity (cutoffLineProfile χ k) z = smoothDensity (scalarPuncturedProfile h) z := by
    unfold smoothDensity
    rw [SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity.complexHessian_congr_of_eventuallyEq hev]
  unfold cutoffLineDensity
  rw [hd, smoothDensity_scalarPuncturedProfile hhs hzD]
  have hhess : realHessian h (Real.log (Complex.normSq (z 0))) 1 1 =
      deriv (deriv χ) (Real.log (Complex.normSq (z 0)) + k) := by
    rw [realHessian, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [Matrix.cons_val_zero, Fin.prod_univ_two, Matrix.cons_val_one, mul_one, one_smul]
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv h = fun s => deriv χ (s + k) := funext fun s => by
      rw [hh, deriv_comp_add_const]
    rw [hd1, deriv_comp_add_const]
  rw [hhess, ← Complex.sq_norm]

theorem cutoffLineDensity_nonneg {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) (z : ComplexModel 1) :
    0 ≤ cutoffLineDensity χ k z := by
  by_cases hz : z 0 = 0
  · rw [cutoffLineDensity_eq_of_small hχ k (by rw [hz]; simpa using Real.exp_pos (-1))]
    positivity
  · rw [cutoffLineDensity_eq_of_ne hχ k hz]
    exact div_nonneg (hχ.deriv2_nonneg _) (by positivity)

/-! ### The total mass -/

theorem measurable_deriv2 {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) : Measurable (deriv (deriv χ)) :=
  hχ.continuous_deriv2.measurable

/-- **`ω_k(ℂ) = 1`.** -/
theorem cutoffLineMeasure_univ {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    cutoffLineMeasure χ k univ = 1 := by
  rw [cutoffLineMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  set R : ℝ → ℝ := fun r => deriv (deriv χ) (Real.log (r ^ 2) + k) / (π * r ^ 2) with hR
  -- the density in polar coordinates
  have hpol : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal (cutoffLineDensity χ k (projectiveModelEquiv (Complex.polarCoord.symm p))) =
        ENNReal.ofReal (R p.1) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hne : (projectiveModelEquiv (Complex.polarCoord.symm p)) 0 ≠ 0 := by
      rw [projectiveModelEquiv_apply_zero]
      intro h0
      have := Complex.norm_polarCoord_symm p
      rw [h0, norm_zero] at this
      exact hp1.ne' (abs_eq_zero.mp this.symm)
    rw [cutoffLineDensity_eq_of_ne hχ k hne, projectiveModelEquiv_apply_zero,
      Complex.norm_polarCoord_symm, abs_of_pos hp1]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  rw [setLIntegral_congr_fun (polarCoord.open_target.measurableSet)
    (g := fun p => ENNReal.ofReal p.1 * ENNReal.ofReal (R p.1)) fun p hp => by
      rw [smul_eq_mul, hpol p hp]]
  have hmeasR : Measurable fun r : ℝ => ENNReal.ofReal r * ENNReal.ofReal (R r) := by
    refine (ENNReal.measurable_ofReal.comp measurable_id).mul ?_
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((measurable_deriv2 hχ).comp ((Real.measurable_log.comp (measurable_id.pow_const 2)).add
      measurable_const)).div (measurable_const.mul (measurable_id.pow_const 2))
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun x : ℝ × ℝ => ENNReal.ofReal x.1 * ENNReal.ofReal (R x.1))
      (hmeasR.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, sub_neg_eq_add]
  rw [lintegral_mul_const _ hmeasR]
  -- the radial integral, with `r = e^{(s - k)/2}`
  set f : ℝ → ℝ := fun s => Real.exp ((s - k) / 2) with hf
  have hf' : ∀ s ∈ (univ : Set ℝ), HasDerivWithinAt f (f s / 2) univ s := by
    intro s _
    have h := ((((hasDerivAt_id s).sub_const (k : ℝ)).div_const 2).exp)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [hf, id]
    ring
  have hinj : InjOn f univ := fun a _ b _ h => by
    have := Real.exp_injective h
    linarith
  have himage : f '' univ = Ioi 0 := by
    ext r
    simp only [mem_image, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨s, rfl⟩; exact Real.exp_pos _
    · intro hr
      refine ⟨2 * Real.log r + k, ?_⟩
      simp only [hf]
      rw [show (2 * Real.log r + k - k) / 2 = Real.log r by ring, Real.exp_log hr]
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hf' hinj,
    setLIntegral_univ]
  have hint : ∀ s, ENNReal.ofReal |f s / 2| * (ENNReal.ofReal (f s) * ENNReal.ofReal (R (f s))) =
      ENNReal.ofReal (deriv (deriv χ) s) * ENNReal.ofReal (1 / (2 * π)) := by
    intro s
    have hfs : 0 < f s := Real.exp_pos _
    have hlog : Real.log (f s ^ 2) + k = s := by
      rw [Real.log_pow, hf, Real.log_exp]; push_cast; ring
    have hsq : f s ^ 2 = Real.exp (s - k) := by
      rw [hf, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (hχ.deriv2_nonneg s)]
    congr 1
    simp only [hR, hlog]
    rw [show f s / 2 * (f s * (deriv (deriv χ) s / (π * f s ^ 2))) =
      deriv (deriv χ) s * (f s ^ 2 / f s ^ 2) / (2 * π) by
        field_simp]
    rw [div_self (by positivity), mul_one, div_eq_mul_one_div]
  rw [lintegral_congr hint, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hχ.lintegral_deriv2, one_mul, ← ENNReal.ofReal_mul (by positivity)]
  rw [show 1 / (2 * π) * (π + π) = 1 by field_simp; ring, ENNReal.ofReal_one]

/-! ### The mass at the scale `e^{-k/2}` -/

/-- **`ω_k(B(0, r e^{-k/2})) ≥ min(r, e^{-1/2})²`.** -/
theorem le_cutoffLineMeasure_ball {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (min r (Real.exp (-1 / 2)) ^ 2) ≤
      cutoffLineMeasure χ k (ball 0 (r * Real.exp (-((k : ℝ) / 2)))) := by
  set ρ := min r (Real.exp (-1 / 2)) * Real.exp (-((k : ℝ) / 2)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hsub : ball (0 : ℂ) ρ ⊆ ball 0 (r * Real.exp (-((k : ℝ) / 2))) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
  refine le_trans ?_ (measure_mono hsub)
  rw [cutoffLineMeasure, withDensity_apply _ measurableSet_ball]
  have hden : ∀ τ ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (cutoffLineDensity χ k (projectiveModelEquiv τ)) =
        ENNReal.ofReal (Real.exp k / π) := by
    intro τ hτ
    rw [cutoffLineDensity_eq_of_small hχ k]
    rw [normSq_projectiveModelEquiv]
    rw [mem_ball, dist_zero_right] at hτ
    have h1 : ‖τ‖ ^ 2 < ρ ^ 2 := by gcongr
    have h2 : ρ ^ 2 ≤ Real.exp (-1) * Real.exp (-(k : ℝ)) := by
      rw [hρ, mul_pow]
      gcongr
      · calc min r (Real.exp (-1 / 2)) ^ 2 ≤ Real.exp (-1 / 2) ^ 2 := by
              gcongr; exact min_le_right _ _
          _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
      · rw [← Real.exp_nat_mul]; apply le_of_eq; congr 1; push_cast; ring
    calc Real.exp k * ‖τ‖ ^ 2 < Real.exp k * (Real.exp (-1) * Real.exp (-(k : ℝ))) :=
          mul_lt_mul_of_pos_left (h1.trans_le h2) (Real.exp_pos _)
      _ = Real.exp (-1) := by
          rw [mul_comm (Real.exp (-1)), ← mul_assoc, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, one_mul]
  rw [setLIntegral_congr_fun measurableSet_ball hden, setLIntegral_const, Complex.volume_ball,
    ← ENNReal.ofReal_pow hρ0.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  have he : Real.exp (-((k : ℝ) / 2)) ^ 2 * Real.exp k = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpi := Real.pi_pos
  rw [hρ, mul_pow]
  field_simp
  linear_combination -he

end SGPT.Okounkov.TranscendentalWN
