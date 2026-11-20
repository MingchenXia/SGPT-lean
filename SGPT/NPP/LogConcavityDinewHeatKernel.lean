import SGPT.Foundations.Analysis.FirstPass.MongeAmpere
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The heat kernel of the complex Laplacian on `ℂⁿ`

Analytic input for Dinew's mixed Monge–Ampère inequality (Xia, *Foundations of pluripotential
theory*, `lem:constant-elliptic-upper-tests` and `prop:bounded-monge-ampere-linear-density`),
used in `SGPT/NPP/LogConcavityDinew*.lean` for the general case of source `thm:logconc`.

On `ℂⁿ = ComplexModel n` (real dimension `2n`) the function
`K(t, w) = t^{-n} exp(-‖w‖² / t)` (`heatKernel`) solves the heat equation for the operator
`L = ∑ⱼ ∂²/∂zⱼ∂z̄ⱼ = Δ/4`:
`∂ₜ K = (1/4) ∑ⱼ (∂²_{eⱼ} K + ∂²_{i eⱼ} K)` (`sum_heatKernelDD_coordinate`).
We record the explicit first, second and third derivatives along real lines, the time
derivative, the total mass `∫ K(t, ·) = πⁿ`, the circle invariance, and the Gaussian bounds used
for differentiation under the integral sign. The second-order Taylor remainder along a segment is
bounded by the third derivative (`abs_heatKernel_taylor_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Coordinates -/

theorem inner_coordinateVector (w : ComplexModel n) (j : Fin n) :
    inner ℝ w (coordinateVector j) = (w j).re := by
  simp [coordinateVector, PiLp.inner_apply, Complex.inner, apply_ite Complex.re,
    Finset.sum_ite_eq']

theorem inner_I_coordinateVector (w : ComplexModel n) (j : Fin n) :
    inner ℝ w (Complex.I • coordinateVector j) = (w j).im := by
  simp [coordinateVector, PiLp.inner_apply, Complex.inner, apply_ite Complex.re,
    Finset.sum_ite_eq']

/-- The real coordinates `Re wⱼ, Im wⱼ` are the inner products with the real orthonormal frame
`eⱼ, i eⱼ`. -/
theorem sum_inner_coordinate_sq (w : ComplexModel n) :
    ∑ j, (inner ℝ w (coordinateVector j) ^ 2 +
      inner ℝ w (Complex.I • coordinateVector j) ^ 2) = ‖w‖ ^ 2 := by
  simp only [inner_coordinateVector, inner_I_coordinateVector]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_coordinateVector (j : Fin n) : ‖coordinateVector (n := n) j‖ = 1 := by
  simp [coordinateVector]

theorem norm_I_coordinateVector (j : Fin n) :
    ‖Complex.I • coordinateVector (n := n) j‖ = 1 := by
  simp [coordinateVector, norm_smul]

/-- The trace of a real bilinear form in the real frame `eⱼ, i eⱼ`. -/
def stdTrace (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) : ℝ :=
  ∑ j, (M (coordinateVector j) (coordinateVector j) +
    M (Complex.I • coordinateVector j) (Complex.I • coordinateVector j))

theorem stdTrace_add (M N : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    stdTrace (M + N) = stdTrace M + stdTrace N := by
  simp only [stdTrace, ContinuousLinearMap.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem stdTrace_smul (c : ℝ) (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    stdTrace (c • M) = c * stdTrace M := by
  simp only [stdTrace, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem stdTrace_innerSL : stdTrace (innerSL ℝ : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) =
    2 * n := by
  unfold stdTrace
  have h : ∀ v : ComplexModel n,
      (innerSL ℝ : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) v v = ‖v‖ ^ 2 := fun v => by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  simp only [h, norm_coordinateVector, norm_I_coordinateVector]
  simp
  ring

/-! ### The kernel and its derivatives -/

/-- The heat kernel `t^{-n} exp(-‖w‖²/t)`. -/
def heatKernel (n : ℕ) (t : ℝ) (w : ComplexModel n) : ℝ :=
  Real.exp (-(‖w‖ ^ 2 / t)) / t ^ n

/-- The derivative of `heatKernel` in the direction `h`. -/
def heatKernelD (t : ℝ) (w h : ComplexModel n) : ℝ :=
  -(2 / t) * inner ℝ w h * heatKernel n t w

/-- The second derivative of `heatKernel` in the directions `h, k`. -/
def heatKernelDD (t : ℝ) (w h k : ComplexModel n) : ℝ :=
  heatKernel n t w * (4 / t ^ 2 * inner ℝ w h * inner ℝ w k - 2 / t * inner ℝ h k)

/-- The third derivative of `heatKernel` in the direction `h`. -/
def heatKernelDDD (t : ℝ) (w h : ComplexModel n) : ℝ :=
  heatKernel n t w * (-(8 / t ^ 3) * inner ℝ w h ^ 3 + 12 / t ^ 2 * inner ℝ w h * ‖h‖ ^ 2)

/-- The time derivative of `heatKernel`. -/
def heatKernelT (t : ℝ) (w : ComplexModel n) : ℝ :=
  heatKernel n t w * (‖w‖ ^ 2 / t ^ 2 - n / t)

theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (w : ComplexModel n) : 0 < heatKernel n t w :=
  div_pos (Real.exp_pos _) (pow_pos ht n)

theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (w : ComplexModel n) : 0 ≤ heatKernel n t w :=
  (heatKernel_pos ht w).le

theorem heatKernel_neg (t : ℝ) (w : ComplexModel n) : heatKernel n t (-w) = heatKernel n t w := by
  simp [heatKernel]

theorem heatKernel_smul_of_norm_eq_one (t : ℝ) {c : ℂ} (hc : ‖c‖ = 1) (w : ComplexModel n) :
    heatKernel n t (c • w) = heatKernel n t w := by
  simp [heatKernel, norm_smul, hc]

theorem heatKernel_sub_comm (t : ℝ) (x y : ComplexModel n) :
    heatKernel n t (x - y) = heatKernel n t (y - x) := by
  rw [← neg_sub, heatKernel_neg]

theorem continuous_heatKernel {t : ℝ} (ht : t ≠ 0) :
    Continuous (heatKernel n t) := by
  unfold heatKernel
  fun_prop (disch := exact ht)

theorem hasDerivAt_line (w h : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => w + s • h) h s := by
  simpa using ((hasDerivAt_id s).smul_const h).const_add w

theorem hasDerivAt_inner_line (w h k : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℝ (w + s • h) k) (inner ℝ h k) s := by
  have := (hasDerivAt_line w h s).inner ℝ (hasDerivAt_const s k)
  simpa using this

theorem hasDerivAt_heatKernel_line {t : ℝ} (ht : t ≠ 0) (w h : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel n t (w + s • h)) (heatKernelD t (w + s • h) h) s := by
  have hn : HasDerivAt (fun s : ℝ => ‖w + s • h‖ ^ 2) (2 * inner ℝ (w + s • h) h) s :=
    (hasDerivAt_line w h s).norm_sq
  have he := (((hn.div_const t).neg).exp).div_const (t ^ n)
  refine he.congr_deriv ?_
  simp only [heatKernelD, heatKernel, Pi.neg_apply]
  field_simp

theorem hasDerivAt_heatKernelD_line {t : ℝ} (ht : t ≠ 0) (w h : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernelD t (w + s • h) h) (heatKernelDD t (w + s • h) h h) s := by
  have hK := hasDerivAt_heatKernel_line ht w h s
  have hi := hasDerivAt_inner_line w h h s
  refine ((hi.const_mul (-(2 / t))).mul hK).congr_deriv ?_
  simp only [heatKernelDD, heatKernelD, real_inner_self_eq_norm_sq, Pi.mul_apply]
  ring

theorem hasDerivAt_heatKernelDD_line {t : ℝ} (ht : t ≠ 0) (w h : ComplexModel n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernelDD t (w + s • h) h h) (heatKernelDDD t (w + s • h) h) s := by
  have hK := hasDerivAt_heatKernel_line ht w h s
  have hi := hasDerivAt_inner_line w h h s
  have hq := ((hi.const_mul (4 / t ^ 2)).mul hi).sub_const (2 / t * inner ℝ h h)
  refine (hK.mul hq).congr_deriv ?_
  simp only [heatKernelDDD, heatKernelD, real_inner_self_eq_norm_sq, Pi.mul_apply]
  ring

theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (w : ComplexModel n) :
    HasDerivAt (fun t : ℝ => heatKernel n t w) (heatKernelT t w) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have h1 : HasDerivAt (fun t : ℝ => -(‖w‖ ^ 2 / t)) (‖w‖ ^ 2 / t ^ 2) t := by
    have := ((hasDerivAt_inv ht0).const_mul (‖w‖ ^ 2)).neg
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    filter_upwards with t
    simp [div_eq_mul_inv]
  have h3 : HasDerivAt (fun t : ℝ => t ^ n) (n * t ^ (n - 1)) t := hasDerivAt_pow n t
  refine (h1.exp.div h3 (pow_ne_zero n ht0)).congr_deriv ?_
  simp only [heatKernelT, heatKernel]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : t ^ n = t * t ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    field_simp

/-- **The heat equation** `∂ₜ K = (1/4) ∑ⱼ (∂²_{eⱼ} + ∂²_{i eⱼ}) K`. -/
theorem sum_heatKernelDD_coordinate (t : ℝ) (w : ComplexModel n) :
    ∑ j, (heatKernelDD t w (coordinateVector j) (coordinateVector j) +
      heatKernelDD t w (Complex.I • coordinateVector j) (Complex.I • coordinateVector j)) =
      4 * heatKernelT t w := by
  have hsum := sum_inner_coordinate_sq w
  have hterm : ∀ j, heatKernelDD t w (coordinateVector j) (coordinateVector j) +
      heatKernelDD t w (Complex.I • coordinateVector j) (Complex.I • coordinateVector j) =
      heatKernel n t w * (4 / t ^ 2) * (inner ℝ w (coordinateVector j) ^ 2 +
        inner ℝ w (Complex.I • coordinateVector j) ^ 2) - heatKernel n t w * (4 / t) := by
    intro j
    simp only [heatKernelDD, real_inner_self_eq_norm_sq, norm_coordinateVector,
      norm_I_coordinateVector]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, heatKernelT]
  ring

/-! ### Mass and Gaussian bounds -/

theorem finrank_complexModel : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex]
  simp [ComplexModel]

theorem integral_exp_neg_mul_sq_norm {a : ℝ} (ha : 0 < a) :
    ∫ w : ComplexModel n, Real.exp (-a * ‖w‖ ^ 2) = (Real.pi / a) ^ n := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_complexModel]
  rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem integrable_exp_neg_mul_sq_norm {a : ℝ} (ha : 0 < a) :
    Integrable (fun w : ComplexModel n => Real.exp (-a * ‖w‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_neg_mul_sq_norm ha]
  exact pow_ne_zero _ (div_pos Real.pi_pos ha).ne'

theorem integrable_exp_neg_sq_norm_div {b : ℝ} (hb : 0 < b) (x : ComplexModel n) :
    Integrable (fun y : ComplexModel n => Real.exp (-(‖x - y‖ ^ 2 / b))) := by
  have h := (integrable_exp_neg_mul_sq_norm (n := n) (inv_pos.mpr hb)).comp_sub_left x
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp_apply]
  congr 1
  field_simp

/-- **Total mass**: `∫ K(t, ·) = πⁿ` for every `t > 0`. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ w : ComplexModel n, heatKernel n t w = Real.pi ^ n := by
  have h := integral_exp_neg_mul_sq_norm (n := n) (inv_pos.mpr ht)
  unfold heatKernel
  rw [integral_div]
  have h' : ∫ w : ComplexModel n, Real.exp (-(‖w‖ ^ 2 / t)) = (Real.pi * t) ^ n := by
    rw [← div_inv_eq_mul, ← h]
    congr 1
    funext w
    congr 1
    field_simp
  rw [h', mul_pow]
  field_simp

theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel n t) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_heatKernel ht]
  exact pow_ne_zero _ Real.pi_pos.ne'

/-- Polynomial factors are absorbed by halving the Gaussian exponent. -/
theorem one_add_sq_pow_mul_exp_le {b : ℝ} (hb : 0 < b) (k : ℕ) (r : ℝ) :
    (1 + r ^ 2) ^ k * Real.exp (-(r ^ 2 / b)) ≤
      (2 * b) ^ k * k.factorial * Real.exp (1 / (2 * b)) * Real.exp (-(r ^ 2 / (2 * b))) := by
  set y : ℝ := (1 + r ^ 2) / (2 * b) with hy
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hyk : y ^ k ≤ k.factorial * Real.exp y := by
    rw [div_le_iff₀ hk] at hfac; linarith
  have hpow : (1 + r ^ 2) ^ k = (2 * b) ^ k * y ^ k := by
    rw [← mul_pow, hy]; congr 1; field_simp
  have hexp : Real.exp y * Real.exp (-(r ^ 2 / b)) =
      Real.exp (1 / (2 * b)) * Real.exp (-(r ^ 2 / (2 * b))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hy]; field_simp; ring
  calc (1 + r ^ 2) ^ k * Real.exp (-(r ^ 2 / b))
      = (2 * b) ^ k * y ^ k * Real.exp (-(r ^ 2 / b)) := by rw [hpow]
    _ ≤ (2 * b) ^ k * (k.factorial * Real.exp y) * Real.exp (-(r ^ 2 / b)) := by
        gcongr
    _ = (2 * b) ^ k * k.factorial * (Real.exp y * Real.exp (-(r ^ 2 / b))) := by ring
    _ = _ := by rw [hexp]; ring

/-- Moving the centre of a Gaussian by at most `r` costs a constant and half the exponent. -/
theorem exp_neg_sq_norm_sub_le {b r : ℝ} (hb : 0 < b) {x x' y : ComplexModel n}
    (hx : ‖x - x'‖ ≤ r) :
    Real.exp (-(‖x - y‖ ^ 2 / b)) ≤
      Real.exp (r ^ 2 / b) * Real.exp (-(‖x' - y‖ ^ 2 / (2 * b))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : ‖x' - y‖ ≤ ‖x - x'‖ + ‖x - y‖ := by
    calc ‖x' - y‖ = ‖(x - y) - (x - x')‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖x - x'‖ := norm_sub_le _ _
      _ = _ := by ring
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  have h1 : ‖x' - y‖ ^ 2 ≤ 2 * r ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    have h2 : ‖x' - y‖ ≤ r + ‖x - y‖ := htri.trans (by linarith)
    have h3 : ‖x' - y‖ ^ 2 ≤ (r + ‖x - y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (r - ‖x - y‖)]
  have hb2 : 0 < 2 * b := by positivity
  rw [show -(‖x - y‖ ^ 2 / b) = -(2 * ‖x - y‖ ^ 2) / (2 * b) by field_simp,
    show r ^ 2 / b + -(‖x' - y‖ ^ 2 / (2 * b)) = (2 * r ^ 2 - ‖x' - y‖ ^ 2) / (2 * b) by
      field_simp; ring]
  apply div_le_div_of_nonneg_right _ hb2.le
  linarith

theorem one_add_sq_le_mul (x y : ComplexModel n) :
    1 + ‖y‖ ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) * (1 + ‖x - y‖ ^ 2) := by
  have h : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
  have h2 : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖x‖ - ‖x - y‖)]
  nlinarith [sq_nonneg (‖x‖), sq_nonneg (‖x - y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖x - y‖)]

/-- The kernel is dominated by a fixed Gaussian for `t` in a compact subinterval of `(0, ∞)`. -/
theorem heatKernel_le_of_mem_Icc {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b)
    (w : ComplexModel n) :
    heatKernel n t w ≤ Real.exp (-(‖w‖ ^ 2 / b)) / a ^ n := by
  have ht : 0 < t := ha.trans_le hat
  unfold heatKernel
  apply div_le_div₀ (Real.exp_pos _).le _ (pow_pos ha n) (pow_le_pow_left₀ ha.le hat n)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact div_le_div_of_nonneg_left (by positivity) ht htb

/-! ### Second-order Taylor remainder along segments -/

theorem abs_heatKernelDDD_le {t : ℝ} (ht : 0 < t) (v h : ComplexModel n) :
    |heatKernelDDD t v h| ≤
      heatKernel n t v * ((8 / t ^ 3 + 12 / t ^ 2) * (1 + ‖v‖ ^ 2) ^ 2) * ‖h‖ ^ 3 := by
  unfold heatKernelDDD
  rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht v),
    mul_assoc (heatKernel n t v) ((8 / t ^ 3 + 12 / t ^ 2) * (1 + ‖v‖ ^ 2) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg ht v)
  have hi : |inner ℝ v h| ≤ ‖v‖ * ‖h‖ := abs_real_inner_le_norm v h
  have hv3 : ‖v‖ ^ 3 ≤ (1 + ‖v‖ ^ 2) ^ 2 := by
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1), sq_nonneg (‖v‖),
      mul_nonneg (norm_nonneg v) (sq_nonneg (‖v‖ - 1))]
  have hv1 : ‖v‖ ≤ (1 + ‖v‖ ^ 2) ^ 2 := by
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1), sq_nonneg (‖v‖), sq_nonneg (‖v‖ ^ 2)]
  calc abs (-(8 / t ^ 3) * inner ℝ v h ^ 3 + 12 / t ^ 2 * inner ℝ v h * ‖h‖ ^ 2)
      ≤ 8 / t ^ 3 * |inner ℝ v h| ^ 3 + 12 / t ^ 2 * |inner ℝ v h| * ‖h‖ ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_of_pos (by positivity : 0 < 8 / t ^ 3),
          abs_of_pos (by positivity : 0 < 12 / t ^ 2), abs_of_nonneg (by positivity : 0 ≤ ‖h‖ ^ 2)]
    _ ≤ 8 / t ^ 3 * (‖v‖ * ‖h‖) ^ 3 + 12 / t ^ 2 * (‖v‖ * ‖h‖) * ‖h‖ ^ 2 := by
        gcongr
    _ = (8 / t ^ 3 * ‖v‖ ^ 3 + 12 / t ^ 2 * ‖v‖) * ‖h‖ ^ 3 := by ring
    _ ≤ ((8 / t ^ 3 + 12 / t ^ 2) * (1 + ‖v‖ ^ 2) ^ 2) * ‖h‖ ^ 3 := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_left hv3 (by positivity : (0 : ℝ) ≤ 8 / t ^ 3),
          mul_le_mul_of_nonneg_left hv1 (by positivity : (0 : ℝ) ≤ 12 / t ^ 2)]

/-- A uniform bound for the third derivative along a unit segment. -/
theorem abs_heatKernelDDD_line_le {t : ℝ} (ht : 0 < t) (w h : ComplexModel n) (hh : ‖h‖ ≤ 1)
    {s : ℝ} (hs : |s| ≤ 1) :
    |heatKernelDDD t (w + s • h) h| ≤
      ((8 / t ^ 3 + 12 / t ^ 2) * ((2 * t) ^ 2 * 2 * Real.exp (1 / (2 * t))) *
        Real.exp (1 / (2 * t)) / t ^ n) * ‖h‖ ^ 3 * Real.exp (-(‖w‖ ^ 2 / (4 * t))) := by
  set v := w + s • h with hv
  have hb := one_add_sq_pow_mul_exp_le ht 2 ‖v‖
  have hshift : Real.exp (-(‖v‖ ^ 2 / (2 * t))) ≤
      Real.exp (1 / (2 * t)) * Real.exp (-(‖w‖ ^ 2 / (4 * t))) := by
    have hvw : ‖v - w‖ ≤ 1 := by
      rw [hv, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |s| * ‖h‖ ≤ 1 * 1 := mul_le_mul hs hh (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have := exp_neg_sq_norm_sub_le (n := n) (by positivity : 0 < 2 * t) (y := 0) hvw
    simp only [sub_zero, one_pow] at this
    convert this using 3 <;> ring
  refine (abs_heatKernelDDD_le ht v h).trans ?_
  unfold heatKernel
  have hfact : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [hfact] at hb
  have hpos : 0 ≤ (8 / t ^ 3 + 12 / t ^ 2) := by positivity
  calc Real.exp (-(‖v‖ ^ 2 / t)) / t ^ n * ((8 / t ^ 3 + 12 / t ^ 2) * (1 + ‖v‖ ^ 2) ^ 2) *
        ‖h‖ ^ 3
      = (8 / t ^ 3 + 12 / t ^ 2) / t ^ n * ((1 + ‖v‖ ^ 2) ^ 2 * Real.exp (-(‖v‖ ^ 2 / t))) *
        ‖h‖ ^ 3 := by ring
    _ ≤ (8 / t ^ 3 + 12 / t ^ 2) / t ^ n *
        ((2 * t) ^ 2 * 2 * Real.exp (1 / (2 * t)) * Real.exp (-(‖v‖ ^ 2 / (2 * t)))) *
        ‖h‖ ^ 3 := by gcongr
    _ ≤ (8 / t ^ 3 + 12 / t ^ 2) / t ^ n *
        ((2 * t) ^ 2 * 2 * Real.exp (1 / (2 * t)) *
          (Real.exp (1 / (2 * t)) * Real.exp (-(‖w‖ ^ 2 / (4 * t))))) * ‖h‖ ^ 3 := by gcongr
    _ = _ := by ring

/-- **Second-order Taylor expansion of the kernel**, with a remainder that is cubic in the
increment and Gaussian in the base point. -/
theorem abs_heatKernel_taylor_le {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w h : ComplexModel n, ‖h‖ ≤ 1 →
      |heatKernel n t (w + h) - heatKernel n t w - heatKernelD t w h -
          heatKernelDD t w h h / 2| ≤ C * ‖h‖ ^ 3 * Real.exp (-(‖w‖ ^ 2 / (4 * t))) := by
  set C : ℝ := (8 / t ^ 3 + 12 / t ^ 2) * ((2 * t) ^ 2 * 2 * Real.exp (1 / (2 * t))) *
        Real.exp (1 / (2 * t)) / t ^ n with hC
  refine ⟨C, by positivity, fun w h hh => ?_⟩
  set D : ℝ := C * ‖h‖ ^ 3 * Real.exp (-(‖w‖ ^ 2 / (4 * t))) with hD
  have ht0 : t ≠ 0 := ht.ne'
  have hD3 : ∀ s ∈ Icc (0 : ℝ) 1, |heatKernelDDD t (w + s • h) h| ≤ D := fun s hs =>
    abs_heatKernelDDD_line_le ht w h hh (by rw [abs_of_nonneg hs.1]; exact hs.2)
  -- the three remainders
  set φ2 : ℝ → ℝ := fun s => heatKernelDD t (w + s • h) h h with hφ2
  set φ1 : ℝ → ℝ := fun s => heatKernelD t (w + s • h) h with hφ1
  set φ0 : ℝ → ℝ := fun s => heatKernel n t (w + s • h) with hφ0
  have hR2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ2 s - φ2 0‖ ≤ D * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s _ => (hasDerivAt_heatKernelDD_line ht0 w h s).hasDerivWithinAt)
      (fun s hs => by rw [Real.norm_eq_abs]; exact hD3 s (Ico_subset_Icc_self hs))
  have hR2' : ∀ s ∈ Icc (0 : ℝ) 1, |φ2 s - φ2 0| ≤ D := fun s hs => by
    have := hR2 s hs
    rw [Real.norm_eq_abs, sub_zero] at this
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD3 0 ⟨le_rfl, zero_le_one⟩)
    nlinarith [hs.2, hs.1]
  have hR1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖(φ1 s - s * φ2 0) - (φ1 0 - 0 * φ2 0)‖ ≤ D * (s - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun s => φ2 s - φ2 0)
      (fun s _ => ?_) (fun s hs => by rw [Real.norm_eq_abs]; exact hR2' s (Ico_subset_Icc_self hs))
    have := (hasDerivAt_heatKernelD_line ht0 w h s).sub ((hasDerivAt_id s).mul_const (φ2 0))
    exact (this.congr_deriv (by simp [hφ2])).hasDerivWithinAt
  have hR1' : ∀ s ∈ Icc (0 : ℝ) 1, |φ1 s - φ1 0 - s * φ2 0| ≤ D := fun s hs => by
    have := hR1 s hs
    rw [Real.norm_eq_abs, sub_zero] at this
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD3 0 ⟨le_rfl, zero_le_one⟩)
    have h' : |φ1 s - φ1 0 - s * φ2 0| ≤ D * s := by
      convert this using 2; ring
    nlinarith [hs.2, hs.1]
  have hR0 : ∀ s ∈ Icc (0 : ℝ) 1, ‖(φ0 s - s * φ1 0 - s ^ 2 / 2 * φ2 0) -
      (φ0 0 - 0 * φ1 0 - 0 ^ 2 / 2 * φ2 0)‖ ≤ D * (s - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun s => φ1 s - φ1 0 - s * φ2 0)
      (fun s _ => ?_) (fun s hs => by rw [Real.norm_eq_abs]; exact hR1' s (Ico_subset_Icc_self hs))
    have h1 := hasDerivAt_heatKernel_line ht0 w h s
    have h2 := (hasDerivAt_id s).mul_const (φ1 0)
    have h3 := ((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0)
    have := (h1.sub h2).sub h3
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp
    ring
  have := hR0 1 ⟨zero_le_one, le_rfl⟩
  simp only [hφ0, hφ1, hφ2, one_smul, zero_smul, add_zero, one_mul, one_pow, zero_mul, sub_zero,
    Real.norm_eq_abs, mul_one] at this
  convert this using 2
  ring

end SGPT.NPP.LogConcavityDinew
