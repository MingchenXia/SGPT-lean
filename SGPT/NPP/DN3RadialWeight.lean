import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization

/-!
# The radial weight of the Chern smoothing

Lane DN3 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`,
`chapters/inputs/q10-big-envelope-regularity.tex`, lines 12–54 and Step 1).

FPT builds its smoothing kernel from the radial weight
`χ(t) = C_n (1 - t)⁻² e^{-1/(1-t)}` for `t < 1`, `χ(t) = 0` for `t ≥ 1`, with its primitive
`χ₁(t) = -C_n e^{-1/(1-t)}` (`χ₁' = χ`, `-χ₁/χ = (1 - t)²`), the constant `C_n > 0` being chosen
so that `∫_{ℂⁿ} χ(|ζ|²) dζ = 1`.  Here:

* `weightGlue t = e^{-1/(1-t)}` (`t < 1`), `0` (`t ≥ 1`), i.e. `-χ₁ / C_n`, built from mathlib's
  `expNegInvGlue`; it is smooth (`contDiff_weightGlue`);
* `weightCore = -weightGlue'`, i.e. `χ / C_n`, with the explicit formula
  `weightCore_eq_of_lt` and `weightCore_eq_zero_of_le`;
* `weightMass n = ∫_{ℂⁿ} weightCore(‖ζ‖²) dζ > 0` (`weightMass_pos`), `chi n = C_n · weightCore`
  and `chiOne n = -C_n · weightGlue` with `C_n = (weightMass n)⁻¹`, so that
  `HasDerivAt (chiOne n) (chi n t) t` (`hasDerivAt_chiOne`);
* `kernel n ζ = χ(‖ζ‖²)` is a smooth radial kernel in the sense of TN `PshRadialRegularization`
  (`isRadialKernel_kernel`): smooth, nonnegative, of integral one, supported in the closed unit
  ball and invariant under the circle action.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization

/-! ### The profile `e^{-1/(1-t)}` -/

/-- `t ↦ e^{-1/(1-t)}` for `t < 1`, `0` for `t ≥ 1` (FPT's `-χ₁ / C_n`). -/
def weightGlue (t : ℝ) : ℝ := expNegInvGlue (1 - t)

theorem contDiff_weightGlue : ContDiff ℝ ∞ weightGlue :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)

theorem weightGlue_nonneg (t : ℝ) : 0 ≤ weightGlue t := expNegInvGlue.nonneg _

theorem weightGlue_eq_zero_of_le {t : ℝ} (ht : 1 ≤ t) : weightGlue t = 0 :=
  expNegInvGlue.zero_of_nonpos (by linarith)

theorem weightGlue_eq_of_lt {t : ℝ} (ht : t < 1) :
    weightGlue t = Real.exp (-(1 - t)⁻¹) := by
  have h : ¬ (1 - t ≤ 0) := by linarith
  simp [weightGlue, expNegInvGlue, h]

theorem weightGlue_pos_of_lt {t : ℝ} (ht : t < 1) : 0 < weightGlue t := by
  rw [weightGlue_eq_of_lt ht]; exact Real.exp_pos _

theorem weightGlue_le_one (t : ℝ) : weightGlue t ≤ 1 := by
  rcases lt_or_ge t 1 with ht | ht
  · rw [weightGlue_eq_of_lt ht, Real.exp_le_one_iff, neg_nonpos]
    exact inv_nonneg.mpr (by linarith)
  · rw [weightGlue_eq_zero_of_le ht]; norm_num

/-- `weightCore = -weightGlue'`, i.e. FPT's `χ / C_n`. -/
def weightCore (t : ℝ) : ℝ := -deriv weightGlue t

theorem differentiable_weightGlue : Differentiable ℝ weightGlue :=
  contDiff_weightGlue.differentiable (by simp)

theorem hasDerivAt_weightGlue (t : ℝ) : HasDerivAt weightGlue (-weightCore t) t := by
  rw [weightCore, neg_neg]
  exact differentiable_weightGlue.differentiableAt.hasDerivAt

theorem contDiff_weightCore : ContDiff ℝ ∞ weightCore :=
  ((contDiff_infty_iff_deriv.mp contDiff_weightGlue).2).neg

/-- For `t ≥ 1`, `weightGlue` attains its minimum `0` at `t`, so its derivative vanishes. -/
theorem weightCore_eq_zero_of_le {t : ℝ} (ht : 1 ≤ t) : weightCore t = 0 := by
  have hmin : IsLocalMin weightGlue t := by
    refine Filter.Eventually.of_forall fun s => ?_
    rw [weightGlue_eq_zero_of_le ht]
    exact weightGlue_nonneg s
  rw [weightCore, hmin.deriv_eq_zero, neg_zero]

/-- The explicit formula `χ/C_n = (1-t)⁻² e^{-1/(1-t)}` for `t < 1`. -/
theorem weightCore_eq_of_lt {t : ℝ} (ht : t < 1) :
    weightCore t = ((1 - t) ^ 2)⁻¹ * Real.exp (-(1 - t)⁻¹) := by
  have hpos : 0 < 1 - t := by linarith
  have hev : weightGlue =ᶠ[𝓝 t] fun s => Real.exp (-(1 - s)⁻¹) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact weightGlue_eq_of_lt hs
  have hd1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have hd2 : HasDerivAt (fun s : ℝ => (1 - s)⁻¹) (-(-1) / (1 - t) ^ 2) t :=
    hd1.inv hpos.ne'
  have hd3 : HasDerivAt (fun s : ℝ => Real.exp (-(1 - s)⁻¹))
      (Real.exp (-(1 - t)⁻¹) * -(-(-1) / (1 - t) ^ 2)) t :=
    hd2.neg.exp
  rw [weightCore, hev.deriv_eq, hd3.deriv]
  field_simp

theorem weightCore_pos_of_lt {t : ℝ} (ht : t < 1) : 0 < weightCore t := by
  rw [weightCore_eq_of_lt ht]
  have : 0 < 1 - t := by linarith
  positivity

theorem weightCore_nonneg (t : ℝ) : 0 ≤ weightCore t := by
  rcases lt_or_ge t 1 with ht | ht
  · exact (weightCore_pos_of_lt ht).le
  · rw [weightCore_eq_zero_of_le ht]

/-- `-χ₁/χ = (1 - t)²` (FPT, Step 1): `weightGlue t = (1 - t)² · weightCore t` for `t < 1`. -/
theorem weightGlue_eq_sq_mul_weightCore {t : ℝ} (ht : t < 1) :
    weightGlue t = (1 - t) ^ 2 * weightCore t := by
  have h1 : 0 < 1 - t := by linarith
  have : (1 - t) ^ 2 ≠ 0 := by positivity
  rw [weightCore_eq_of_lt ht, weightGlue_eq_of_lt ht, ← mul_assoc, mul_inv_cancel₀ this, one_mul]

/-! ### Normalisation on `ℂⁿ` -/

variable (n : ℕ)

/-- `∫_{ℂⁿ} weightCore(‖ζ‖²) dζ`. -/
def weightMass : ℝ := ∫ ζ : ComplexModel n, weightCore (‖ζ‖ ^ 2)

theorem continuous_weightCore_normSq :
    Continuous fun ζ : ComplexModel n => weightCore (‖ζ‖ ^ 2) :=
  contDiff_weightCore.continuous.comp (continuous_norm.pow 2)

theorem weightCore_normSq_eq_zero {ζ : ComplexModel n} (hζ : 1 ≤ ‖ζ‖) :
    weightCore (‖ζ‖ ^ 2) = 0 :=
  weightCore_eq_zero_of_le (by nlinarith)

theorem support_weightCore_normSq :
    Function.support (fun ζ : ComplexModel n => weightCore (‖ζ‖ ^ 2)) = ball 0 1 := by
  ext ζ
  simp only [Function.mem_support, mem_ball, dist_zero_right]
  constructor
  · intro h
    by_contra hζ
    exact h (weightCore_normSq_eq_zero n (not_lt.mp hζ))
  · intro hζ
    have : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
    exact (weightCore_pos_of_lt this).ne'

theorem hasCompactSupport_weightCore_normSq :
    HasCompactSupport fun ζ : ComplexModel n => weightCore (‖ζ‖ ^ 2) := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) 1) fun ζ hζ => ?_
  refine weightCore_normSq_eq_zero n ?_
  simp only [mem_closedBall, dist_zero_right, not_le] at hζ
  exact hζ.le

theorem integrable_weightCore_normSq :
    Integrable fun ζ : ComplexModel n => weightCore (‖ζ‖ ^ 2) :=
  (continuous_weightCore_normSq n).integrable_of_hasCompactSupport
    (hasCompactSupport_weightCore_normSq n)

theorem weightMass_pos : 0 < weightMass n := by
  rw [weightMass, integral_pos_iff_support_of_nonneg (fun ζ => weightCore_nonneg _)
    (integrable_weightCore_normSq n), support_weightCore_normSq]
  exact measure_ball_pos _ _ one_pos

/-- FPT's weight `χ = C_n · weightCore`, `C_n = (weightMass n)⁻¹`. -/
def chi (t : ℝ) : ℝ := (weightMass n)⁻¹ * weightCore t

/-- FPT's primitive `χ₁ = -C_n · weightGlue`. -/
def chiOne (t : ℝ) : ℝ := -((weightMass n)⁻¹ * weightGlue t)

theorem hasDerivAt_chiOne (t : ℝ) : HasDerivAt (chiOne n) (chi n t) t := by
  have h := ((hasDerivAt_weightGlue t).const_mul (weightMass n)⁻¹).neg
  have he : chiOne n = fun y => -((weightMass n)⁻¹ * weightGlue y) := rfl
  rw [he]
  have hc : chi n t = -((weightMass n)⁻¹ * -weightCore t) := by rw [chi]; ring
  rw [hc]
  exact h

theorem contDiff_chi : ContDiff ℝ ∞ (chi n) := contDiff_const.mul contDiff_weightCore

theorem contDiff_chiOne : ContDiff ℝ ∞ (chiOne n) := (contDiff_const.mul contDiff_weightGlue).neg

theorem chi_nonneg (t : ℝ) : 0 ≤ chi n t :=
  mul_nonneg (inv_nonneg.mpr (weightMass_pos n).le) (weightCore_nonneg t)

theorem chi_pos_of_lt {t : ℝ} (ht : t < 1) : 0 < chi n t :=
  mul_pos (inv_pos.mpr (weightMass_pos n)) (weightCore_pos_of_lt ht)

theorem chi_eq_zero_of_le {t : ℝ} (ht : 1 ≤ t) : chi n t = 0 := by
  rw [chi, weightCore_eq_zero_of_le ht, mul_zero]

theorem chiOne_nonpos (t : ℝ) : chiOne n t ≤ 0 :=
  neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (weightMass_pos n).le) (weightGlue_nonneg t))

theorem chiOne_eq_zero_of_le {t : ℝ} (ht : 1 ≤ t) : chiOne n t = 0 := by
  rw [chiOne, weightGlue_eq_zero_of_le ht, mul_zero, neg_zero]

theorem neg_chiOne_pos_of_lt {t : ℝ} (ht : t < 1) : 0 < -chiOne n t := by
  rw [chiOne, neg_neg]
  exact mul_pos (inv_pos.mpr (weightMass_pos n)) (weightGlue_pos_of_lt ht)

/-- `-χ₁ = (1 - t)² χ` for `t < 1`. -/
theorem neg_chiOne_eq {t : ℝ} (ht : t < 1) : -chiOne n t = (1 - t) ^ 2 * chi n t := by
  rw [chiOne, neg_neg, chi, weightGlue_eq_sq_mul_weightCore ht]
  ring

/-! ### The kernel `ζ ↦ χ(‖ζ‖²)` -/

/-- The smoothing kernel `ζ ↦ χ(‖ζ‖²)` on `ℂⁿ`. -/
def kernel (ζ : ComplexModel n) : ℝ := chi n (‖ζ‖ ^ 2)

theorem kernel_eq_zero {ζ : ComplexModel n} (hζ : 1 ≤ ‖ζ‖) : kernel n ζ = 0 :=
  chi_eq_zero_of_le n (by nlinarith)

theorem contDiff_kernel : ContDiff ℝ ∞ (kernel n) :=
  (contDiff_chi n).comp (contDiff_norm_sq ℝ)

theorem integral_kernel : ∫ ζ, kernel n ζ = 1 := by
  simp only [kernel, chi]
  rw [integral_const_mul, ← weightMass, inv_mul_cancel₀ (weightMass_pos n).ne']

/-- **The kernel `χ(‖ζ‖²)` is a smooth radial kernel** (TN `IsRadialKernel`). -/
theorem isRadialKernel_kernel : IsRadialKernel (kernel n) where
  contDiff := contDiff_kernel n
  nonneg ζ := chi_nonneg n _
  integral_eq_one := integral_kernel n
  tsupport_subset := by
    refine closure_minimal (fun ζ hζ => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hζ (kernel_eq_zero n (not_le.mp h).le)
  circle_invariant a ha ζ := by
    simp only [kernel, norm_smul, ha, one_mul]

end SGPT.NPP.DN3
