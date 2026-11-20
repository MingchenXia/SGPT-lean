import SGPT.Okounkov.TranscendentalWNLipschitzCalculus
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The Lipschitz bound for smooth functions with bounded Laplacian (package WN-LIP)

Blueprint `claude-tok-wn-lip`, nodes `tok-wn-lip:poisson-lipschitz`, `tok-wn-lip:log-potential`
and `tok-wn-lip:smooth`: the smooth case of `tok-wn:lipschitz` (WN21 Corollary 7.6).

* `abs_sub_le_of_harmonicOnNhd`: a harmonic function on a neighbourhood of `closedBall 0 R`,
  bounded by `M` on the circle, satisfies `|u w - u 0| ≤ M · 2(R + r)/(R - r)² · |w|` for
  `|w| ≤ r < R` (Poisson formula, Mathlib `HarmonicOnNhd.circleAverage_poissonKernel_smul`);
* `laplacian_logPotential`: for `ψ` smooth with compact support, the logarithmic potential
  `log ‖·‖ ⋆ ψ` satisfies `Δ (log ‖·‖ ⋆ ψ) = 2π ψ` (TN's one-variable Lelong--Poincaré formula
  `∫ log ‖z - u‖ Δχ(z) dz = 2π χ(u)` and `laplacian_convolution_right`);
* `abs_logPotential_le`, `abs_logPotential_sub_le`: for `|ψ| ≤ 1` supported in the unit disc,
  `|log ‖·‖ ⋆ ψ| ≤ K₀` and `|(log ‖·‖ ⋆ ψ)(w) - (log ‖·‖ ⋆ ψ)(0)| ≤ 2 K₁ |w|` on the closed unit
  disc, with `K₀ = ∫_{|t|<2} |log |t||` and `K₁ = ∫_{|t|<2} |t|⁻¹`;
* `exists_lipschitz_of_smooth`: a universal `A₀` such that every smooth `f` with `|f| ≤ 1` and
  `|Δ f| ≤ 1` on the disc of radius `15/16` satisfies `|f w - f 0| ≤ A₀ |w|` for `|w| ≤ 1/2`.
  Proof: with a cutoff `χ` equal to `1` on the disc of radius `7/8`, `u = f - (2π)⁻¹ log ‖·‖ ⋆ (χ Δf)`
  is harmonic on that disc and bounded by `1 + K₀/(2π)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN.Lipschitz

open MeasureTheory Metric Laplacian Complex Set Filter InnerProductSpace
open scoped Convolution ContDiff Topology

/-! ### Harmonic functions: the Lipschitz bound at the centre from the Poisson formula -/

/-- The Poisson kernel of the disc of radius `R` centred at `0` is `1` at the centre. -/
theorem poissonKernel_zero_zero {z : ℂ} (hz : z ≠ 0) : poissonKernel 0 0 z = 1 := by
  rw [poissonKernel_def]
  simp only [sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have : ‖z‖ ^ 2 ≠ 0 := by positivity
  field_simp

/-- **The Poisson kernel is Lipschitz at the centre.**  For `|w| ≤ r < R` and `|z| = R`,
`|P(w, z) - 1| ≤ 2(R + r)/(R - r)² · |w|`. -/
theorem abs_poissonKernel_sub_one_le {R r : ℝ} (hr : 0 ≤ r) (hrR : r < R) {w z : ℂ}
    (hw : ‖w‖ ≤ r) (hz : ‖z‖ = R) :
    |poissonKernel 0 w z - 1| ≤ 2 * (R + r) / (R - r) ^ 2 * ‖w‖ := by
  have hd : R - r ≤ ‖z - w‖ := by
    have := norm_sub_norm_le z w
    linarith
  have hdpos : 0 < ‖z - w‖ := by linarith
  have hd2 : (R - r) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    exact pow_le_pow_left₀ (by linarith) hd 2
  have hRr : 0 < (R - r) ^ 2 := by
    have : 0 < R - r := by linarith
    positivity
  have hdu : ‖z - w‖ ≤ R + r := by
    have := norm_sub_le z w
    linarith
  have hnorm : |‖z‖ - ‖z - w‖| ≤ ‖w‖ := by
    have := abs_norm_sub_norm_le z (z - w)
    simpa using this
  have hwn : 0 ≤ ‖w‖ := norm_nonneg w
  rw [poissonKernel_def]
  simp only [sub_zero]
  have hne : ‖z - w‖ ^ 2 ≠ 0 := by positivity
  rw [div_sub_one hne, abs_div, abs_of_pos (by positivity : 0 < ‖z - w‖ ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  -- the numerator
  have hnum : |‖z‖ ^ 2 - ‖w‖ ^ 2 - ‖z - w‖ ^ 2| ≤ 2 * (R + r) * ‖w‖ := by
    have hfac : ‖z‖ ^ 2 - ‖w‖ ^ 2 - ‖z - w‖ ^ 2 =
        (‖z‖ - ‖z - w‖) * (‖z‖ + ‖z - w‖) - ‖w‖ ^ 2 := by ring
    rw [hfac]
    have h1 : |(‖z‖ - ‖z - w‖) * (‖z‖ + ‖z - w‖)| ≤ ‖w‖ * (2 * R + r) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖z‖ + ‖z - w‖)]
      exact mul_le_mul hnorm (by linarith) (by positivity) hwn
    have h2 : ‖w‖ ^ 2 ≤ ‖w‖ * r := by nlinarith
    calc |(‖z‖ - ‖z - w‖) * (‖z‖ + ‖z - w‖) - ‖w‖ ^ 2|
        ≤ |(‖z‖ - ‖z - w‖) * (‖z‖ + ‖z - w‖)| + |‖w‖ ^ 2| := abs_sub _ _
      _ ≤ ‖w‖ * (2 * R + r) + ‖w‖ * r := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ ^ 2)]
          linarith
      _ = 2 * (R + r) * ‖w‖ := by ring
  calc |‖z‖ ^ 2 - ‖w‖ ^ 2 - ‖z - w‖ ^ 2| ≤ 2 * (R + r) * ‖w‖ := hnum
    _ = 2 * (R + r) / (R - r) ^ 2 * ‖w‖ * (R - r) ^ 2 := by
        have : R - r ≠ 0 := by linarith
        field_simp
    _ ≤ 2 * (R + r) / (R - r) ^ 2 * ‖w‖ * ‖z - w‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left hd2 ?_
        have : 0 ≤ R + r := by linarith
        positivity

/-- **Lipschitz bound at the centre for bounded harmonic functions.**  If `u` is harmonic on a
neighbourhood of `closedBall 0 R` and `|u| ≤ M` on the circle of radius `R`, then
`|u w - u 0| ≤ M · 2(R + r)/(R - r)² · |w|` for `|w| ≤ r < R`. -/
theorem abs_sub_le_of_harmonicOnNhd {u : ℂ → ℝ} {R r M : ℝ}
    (hu : HarmonicOnNhd u (closedBall 0 R)) (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, |u z| ≤ M) {w : ℂ} (hw : ‖w‖ ≤ r) :
    |u w - u 0| ≤ M * (2 * (R + r) / (R - r) ^ 2) * ‖w‖ := by
  have hR : 0 < R := by linarith
  have hwb : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    linarith
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hw' := hu.circleAverage_poissonKernel_smul hwb
  have h0' := hu.circleAverage_poissonKernel_smul h0b
  have hsph : sphere (0 : ℂ) |R| = sphere 0 R := by rw [abs_of_pos hR]
  have hucont : ContinuousOn u (sphere (0 : ℂ) R) :=
    (hu.contDiffOn.continuousOn).mono sphere_subset_closedBall
  have hPcont : ∀ v ∈ ball (0 : ℂ) R, ContinuousOn (poissonKernel 0 v) (sphere (0 : ℂ) R) := by
    intro v hv
    have hne : ∀ z ∈ sphere (0 : ℂ) R, (z - 0) - (v - 0) ≠ 0 := by
      intro z hz h
      rw [mem_sphere, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right] at hv
      have : z = v := by simpa using sub_eq_zero.mp h
      rw [this] at hz
      linarith
    have : poissonKernel 0 v = fun z => (‖z - 0‖ ^ 2 - ‖v - 0‖ ^ 2) / ‖(z - 0) - (v - 0)‖ ^ 2 := by
      funext z
      exact poissonKernel_def 0 v z
    rw [this]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne z hz))
  have hint : ∀ v ∈ ball (0 : ℂ) R, CircleIntegrable (poissonKernel 0 v • u) 0 R := by
    intro v hv
    exact ContinuousOn.circleIntegrable hR.le ((hPcont v hv).smul hucont)
  have hdiff : u w - u 0 =
      Real.circleAverage (poissonKernel 0 w • u - poissonKernel 0 0 • u) 0 R := by
    rw [Real.circleAverage_sub (hint w hwb) (hint 0 h0b), hw', h0']
  rw [hdiff]
  refine (Real.abs_circleAverage_le_circleAverage_abs).trans ?_
  refine Real.circleAverage_mono_on_of_le_circle ?_ ?_
  · exact ContinuousOn.circleIntegrable hR.le
      ((((hPcont w hwb).smul hucont).sub ((hPcont 0 h0b).smul hucont)).abs)
  · intro z hz
    rw [hsph] at hz
    have hzR : ‖z‖ = R := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hzR
      linarith
    simp only [Pi.abs_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
    rw [poissonKernel_zero_zero hz0, ← sub_mul, abs_mul]
    have hP := abs_poissonKernel_sub_one_le hr hrR hw hzR
    have hMz := hM z hz
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hMz
    calc |poissonKernel 0 w z - 1| * |u z|
        ≤ (2 * (R + r) / (R - r) ^ 2 * ‖w‖) * M :=
          mul_le_mul hP hMz (abs_nonneg _) (by
            have : 0 ≤ R + r := by linarith
            positivity)
      _ = M * (2 * (R + r) / (R - r) ^ 2) * ‖w‖ := by ring

/-! ### The logarithmic potential of a bounded smooth density -/

/-- The logarithmic kernel `t ↦ log |t|` on `ℂ`. -/
def logNorm (t : ℂ) : ℝ := Real.log ‖t‖

/-- `log |t|` is locally integrable on `ℂ` (TN, `locallyIntegrable_log_norm`). -/
theorem locallyIntegrable_logNorm : LocallyIntegrable logNorm :=
  SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable.locallyIntegrable_log_norm

/-- **`Δ (log ‖·‖ ⋆ ψ) = 2π ψ`** for `ψ` smooth with compact support. -/
theorem laplacian_logPotential {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (w : ℂ) : Δ (logNorm ⋆ ψ) w = 2 * Real.pi * ψ w := by
  rw [laplacian_convolution_right locallyIntegrable_logNorm hψc hψ w, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, logNorm]
  rw [← SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable.integral_log_norm_sub_mul_laplacian
    hψ hψc w]
  congr 1
  funext t
  rw [norm_sub_rev]

/-- The constant `K₀ = ∫_{|t| < 2} |log |t||`. -/
def logConst : ℝ := ∫ t in ball (0 : ℂ) 2, |Real.log ‖t‖|

/-- The constant `K₁ = ∫_{|t| < 2} |t|⁻¹`. -/
def invConst : ℝ := ∫ t in ball (0 : ℂ) 2, ‖t‖⁻¹

/-- `|log |t||` is integrable on the disc of radius `2`. -/
theorem integrableOn_abs_log_norm_ball :
    IntegrableOn (fun t : ℂ => |Real.log ‖t‖|) (ball 0 2) :=
  ((locallyIntegrable_logNorm.integrableOn_isCompact (isCompact_closedBall 0 2)).mono_set
    ball_subset_closedBall).abs

/-- `|t|⁻¹` is integrable on discs of `ℂ` (polar coordinates). -/
theorem integrableOn_inv_norm_ball (r : ℝ) :
    IntegrableOn (fun t : ℂ => ‖t‖⁻¹) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y⁻¹)]
  simp only [Complex.finrank_real_complex]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp) (by simp)).congr_fun
    (fun y hy => ?_) measurableSet_Ioo
  have hy0 : y ≠ 0 := hy.1.ne'
  simp [hy0]

/-- **The potential is bounded.**  If `|ψ| ≤ 1` and `ψ` vanishes off the unit disc, then
`|(log ‖·‖ ⋆ ψ)(w)| ≤ K₀` for `|w| ≤ 1`. -/
theorem abs_logPotential_le {ψ : ℂ → ℝ} (hψb : ∀ t, |ψ t| ≤ (ball (0 : ℂ) 1).indicator 1 t)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : |(logNorm ⋆ ψ) w| ≤ logConst := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hb : ∀ t, ‖logNorm t * ψ (w - t)‖ ≤
      (ball (0 : ℂ) 2).indicator (fun t => |Real.log ‖t‖|) t := by
    intro t
    by_cases ht : w - t ∈ ball (0 : ℂ) 1
    · have ht2 : t ∈ ball (0 : ℂ) 2 := by
        rw [mem_ball, dist_zero_right] at ht ⊢
        calc ‖t‖ = ‖w - (w - t)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖w‖ + ‖w - t‖ := norm_sub_le _ _
          _ < 2 := by linarith
      have hψt := hψb (w - t)
      rw [indicator_of_mem ht, Pi.one_apply] at hψt
      rw [indicator_of_mem ht2, Real.norm_eq_abs, abs_mul]
      calc |logNorm t| * |ψ (w - t)| ≤ |logNorm t| * 1 :=
            mul_le_mul_of_nonneg_left hψt (abs_nonneg _)
        _ = |Real.log ‖t‖| := by rw [mul_one]; rfl
    · have hψt := hψb (w - t)
      rw [indicator_of_notMem ht] at hψt
      rw [abs_nonpos_iff.mp hψt, mul_zero, norm_zero]
      exact indicator_nonneg (fun _ _ => abs_nonneg _) t
  have hint : Integrable ((ball (0 : ℂ) 2).indicator (fun t => |Real.log ‖t‖|)) :=
    (integrable_indicator_iff measurableSet_ball).mpr integrableOn_abs_log_norm_ball
  calc |∫ t, logNorm t * ψ (w - t)| = ‖∫ t, logNorm t * ψ (w - t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, (ball (0 : ℂ) 2).indicator (fun t => |Real.log ‖t‖|) t :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hb)
    _ = logConst := integral_indicator measurableSet_ball

/-- `|log a - log b| ≤ |a - b| (a⁻¹ + b⁻¹)` for `a, b > 0`. -/
theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| * (a⁻¹ + b⁻¹) := by
  have key : ∀ {x y : ℝ}, 0 < x → 0 < y → x ≤ y →
      |Real.log x - Real.log y| ≤ |x - y| * (x⁻¹ + y⁻¹) := by
    intro x y hx hy hxy
    have h1 : Real.log y - Real.log x ≤ (y - x) * x⁻¹ := by
      rw [← Real.log_div hy.ne' hx.ne']
      calc Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
        _ = (y - x) * x⁻¹ := by field_simp
    have h2 : 0 ≤ Real.log y - Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy)
    rw [abs_sub_comm, abs_of_nonneg h2, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    calc Real.log y - Real.log x ≤ (y - x) * x⁻¹ := h1
      _ ≤ (y - x) * (x⁻¹ + y⁻¹) :=
          mul_le_mul_of_nonneg_left (by have := inv_pos.mpr hy; linarith) (sub_nonneg.mpr hxy)
  rcases le_total a b with hab | hab
  · exact key ha hb hab
  · have := key hb ha hab
    rw [abs_sub_comm, abs_sub_comm b a, add_comm b⁻¹] at this
    exact this

/-- **The potential is Lipschitz at the centre.**  If `ψ` is continuous with compact support,
`|ψ| ≤ 1` and `ψ` vanishes off the unit disc, then
`|(log ‖·‖ ⋆ ψ)(w) - (log ‖·‖ ⋆ ψ)(0)| ≤ 2 K₁ |w|` for `|w| ≤ 1`. -/
theorem abs_logPotential_sub_le {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψb : ∀ t, |ψ t| ≤ (ball (0 : ℂ) 1).indicator 1 t) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    |(logNorm ⋆ ψ) w - (logNorm ⋆ ψ) 0| ≤ 2 * invConst * ‖w‖ := by
  have hrep : ∀ x, (logNorm ⋆ ψ) x = ∫ t, logNorm (x - t) * ψ t := by
    intro x
    rw [convolution_eq_swap]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ x, Integrable (fun t => logNorm (x - t) * ψ t) := by
    intro x
    have h := SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable.integrable_log_norm_sub_mul
      hψ hψc x
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [logNorm, norm_sub_rev]
  rw [hrep, hrep, ← integral_sub (hint w) (hint 0)]
  set I : ℂ → ℝ := (ball (0 : ℂ) 2).indicator (fun t => ‖t‖⁻¹) with hI
  have hIint : Integrable I :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_norm_ball 2)
  have hIw : Integrable (fun t => I (w - t)) := hIint.comp_sub_left w
  have hgint : Integrable (fun t => ‖w‖ * (I (w - t) + I t)) := (hIw.add hIint).const_mul _
  have hInn : ∀ t, 0 ≤ I t := fun t =>
    indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) t
  have hae : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 ∧ t ≠ w := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 := by
      rw [ae_iff]
      simp [measure_singleton]
    have hw' : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ w := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [h0, hw'] with t h1 h2 using ⟨h1, h2⟩
  have hb : ∀ᵐ t ∂(volume : Measure ℂ), ‖logNorm (w - t) * ψ t - logNorm (0 - t) * ψ t‖ ≤
      ‖w‖ * (I (w - t) + I t) := by
    filter_upwards [hae] with t ht
    by_cases hts : t ∈ ball (0 : ℂ) 1
    · have hψt := hψb t
      rw [indicator_of_mem hts, Pi.one_apply] at hψt
      have ht1 : ‖t‖ < 1 := by simpa using hts
      have ht2 : t ∈ ball (0 : ℂ) 2 := by
        rw [mem_ball, dist_zero_right]
        linarith
      have hwt2 : w - t ∈ ball (0 : ℂ) 2 := by
        rw [mem_ball, dist_zero_right]
        calc ‖w - t‖ ≤ ‖w‖ + ‖t‖ := norm_sub_le _ _
          _ < 2 := by linarith
      have hIt : I t = ‖t‖⁻¹ := by rw [hI, indicator_of_mem ht2]
      have hIwt : I (w - t) = ‖w - t‖⁻¹ := by rw [hI, indicator_of_mem hwt2]
      rw [hIt, hIwt]
      have hpos1 : 0 < ‖w - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm ht.2))
      have hpos2 : 0 < ‖t‖ := norm_pos_iff.mpr ht.1
      have hlog := abs_log_sub_log_le hpos1 hpos2
      have hnn : |‖w - t‖ - ‖t‖| ≤ ‖w‖ := by
        have := abs_norm_sub_norm_le (w - t) (-t)
        simpa [norm_neg] using this
      rw [← sub_mul, Real.norm_eq_abs, abs_mul]
      simp only [logNorm, zero_sub, norm_neg]
      calc |Real.log ‖w - t‖ - Real.log ‖t‖| * |ψ t|
          ≤ |Real.log ‖w - t‖ - Real.log ‖t‖| * 1 :=
            mul_le_mul_of_nonneg_left hψt (abs_nonneg _)
        _ ≤ |‖w - t‖ - ‖t‖| * (‖w - t‖⁻¹ + ‖t‖⁻¹) := by rw [mul_one]; exact hlog
        _ ≤ ‖w‖ * (‖w - t‖⁻¹ + ‖t‖⁻¹) := mul_le_mul_of_nonneg_right hnn (by positivity)
    · have hψt := hψb t
      rw [indicator_of_notMem hts] at hψt
      rw [abs_nonpos_iff.mp hψt, mul_zero, mul_zero, sub_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (add_nonneg (hInn _) (hInn _))
  calc |∫ t, (logNorm (w - t) * ψ t - logNorm (0 - t) * ψ t)|
      = ‖∫ t, (logNorm (w - t) * ψ t - logNorm (0 - t) * ψ t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖w‖ * (I (w - t) + I t) := norm_integral_le_of_norm_le hgint hb
    _ = 2 * invConst * ‖w‖ := by
        rw [integral_const_mul, integral_add hIw hIint, integral_sub_left_eq_self I volume w,
          hI, integral_indicator measurableSet_ball]
        simp only [invConst]
        ring

/-! ### The smooth case -/

/-- The cutoff of the smooth case: `χ = 1` on the disc of radius `7/8`, `χ` supported in the
disc of radius `29/32`. -/
def cutoff : ContDiffBump (0 : ℂ) := ⟨7 / 8, 29 / 32, by norm_num, by norm_num⟩

/-- **`tok-wn-lip:smooth`.**  There is a universal constant `A₀` such that every smooth `f` on `ℂ`
with `|f| ≤ 1` and `|Δ f| ≤ 1` on the disc of radius `15/16` satisfies `|f w - f 0| ≤ A₀ |w|`
for `|w| ≤ 1/2`. -/
theorem exists_lipschitz_of_smooth : ∃ A₀ : ℝ, ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f →
    (∀ x ∈ ball (0 : ℂ) (15 / 16), |f x| ≤ 1) → (∀ x ∈ ball (0 : ℂ) (15 / 16), |Δ f x| ≤ 1) →
    ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → |f w - f 0| ≤ A₀ * ‖w‖ := by
  refine ⟨40 * (1 + logConst / (2 * Real.pi)) + invConst / Real.pi, ?_⟩
  intro f hf hf1 hΔ w hw
  have h2 : ∀ {g : ℂ → ℝ} {x : ℂ}, ContDiff ℝ ∞ g → ContDiffAt ℝ 2 g x := fun hg =>
    hg.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  set χ : ContDiffBump (0 : ℂ) := cutoff with hχ
  set ψ : ℂ → ℝ := fun t => χ t * Δ f t with hψ
  have hψs : ContDiff ℝ ∞ ψ := (χ.contDiff (n := ⊤)).mul (contDiff_laplacian hf)
  have hψc : HasCompactSupport ψ := χ.hasCompactSupport.mul_right
  have hψb : ∀ t, |ψ t| ≤ (ball (0 : ℂ) 1).indicator 1 t := by
    intro t
    by_cases ht : t ∈ ball (0 : ℂ) (29 / 32)
    · have ht1 : t ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) ht
      have ht15 : t ∈ ball (0 : ℂ) (15 / 16) := ball_subset_ball (by norm_num) ht
      rw [indicator_of_mem ht1, Pi.one_apply, hψ, abs_mul]
      have h1 : |χ t| ≤ 1 := by
        rw [abs_of_nonneg χ.nonneg]
        exact χ.le_one
      calc |χ t| * |Δ f t| ≤ 1 * 1 := mul_le_mul h1 (hΔ t ht15) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · have hχ0 : χ t = 0 := by
        have : t ∉ Function.support χ := by
          rw [χ.support_eq]
          exact ht
        simpa using this
      simp only [hψ, hχ0, zero_mul, abs_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  set N : ℂ → ℝ := fun x => (2 * Real.pi)⁻¹ * (logNorm ⋆ ψ) x with hN
  have hNs : ContDiff ℝ ∞ (logNorm ⋆ ψ) :=
    hψc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) locallyIntegrable_logNorm hψs
  have hNs' : ContDiff ℝ ∞ N := contDiff_const.mul hNs
  set u : ℂ → ℝ := fun x => f x - N x with hu
  have hus : ContDiff ℝ ∞ u := hf.sub hNs'
  have hΔu : ∀ x, Δ u x = Δ f x - ψ x := by
    intro x
    have hue : u = f - N := rfl
    rw [hue, ContDiffAt.laplacian_sub (h2 hf) (h2 hNs')]
    have hNe : N = (2 * Real.pi)⁻¹ • (logNorm ⋆ ψ) := by
      funext y
      simp [hN, smul_eq_mul]
    rw [hNe, laplacian_smul _ (h2 hNs), laplacian_logPotential hψs hψc x, smul_eq_mul]
    field_simp
  have hharm : HarmonicOnNhd u (closedBall 0 (3 / 4)) := by
    intro x hx
    refine ⟨h2 hus, ?_⟩
    have hx' : x ∈ ball (0 : ℂ) (7 / 8) := closedBall_subset_ball (by norm_num) hx
    filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
    rw [hΔu y, Pi.zero_apply]
    have hχy : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [hψ, hχy]
  have hNb : ∀ x : ℂ, ‖x‖ ≤ 1 → |N x| ≤ logConst / (2 * Real.pi) := by
    intro x hx
    simp only [hN, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (abs_logPotential_le hψb hx) (by positivity)
  have hub : ∀ z ∈ sphere (0 : ℂ) (3 / 4), |u z| ≤ 1 + logConst / (2 * Real.pi) := by
    intro z hz
    have hz' : ‖z‖ = 3 / 4 := by simpa using hz
    have hzb : z ∈ ball (0 : ℂ) (15 / 16) := by
      rw [mem_ball, dist_zero_right]
      linarith
    calc |u z| = |f z - N z| := rfl
      _ ≤ |f z| + |N z| := abs_sub _ _
      _ ≤ 1 + logConst / (2 * Real.pi) := add_le_add (hf1 z hzb) (hNb z (by linarith))
  have hul := abs_sub_le_of_harmonicOnNhd hharm (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 3 / 4) hub hw
  have hNl : |N w - N 0| ≤ invConst / Real.pi * ‖w‖ := by
    have h := abs_logPotential_sub_le hψs.continuous hψc hψb (le_trans hw (by norm_num))
    simp only [hN]
    rw [← mul_sub, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    calc (2 * Real.pi)⁻¹ * |(logNorm ⋆ ψ) w - (logNorm ⋆ ψ) 0|
        ≤ (2 * Real.pi)⁻¹ * (2 * invConst * ‖w‖) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = invConst / Real.pi * ‖w‖ := by
          field_simp
  have hfu : f w - f 0 = (u w - u 0) + (N w - N 0) := by
    simp only [hu]
    ring
  rw [hfu]
  calc |(u w - u 0) + (N w - N 0)| ≤ |u w - u 0| + |N w - N 0| := abs_add_le _ _
    _ ≤ (1 + logConst / (2 * Real.pi)) * (2 * (3 / 4 + 1 / 2) / (3 / 4 - 1 / 2) ^ 2) * ‖w‖ +
          invConst / Real.pi * ‖w‖ := add_le_add hul hNl
    _ = (40 * (1 + logConst / (2 * Real.pi)) + invConst / Real.pi) * ‖w‖ := by ring

end SGPT.Okounkov.TranscendentalWN.Lipschitz
