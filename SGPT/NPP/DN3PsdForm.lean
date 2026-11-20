import SGPT.Envelopes.LapClass3Hessian

/-!
# Cauchy–Schwarz for positive semidefinite Hermitian forms with a trace bound

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 5: "for a nonnegative Hermitian
matrix `P` and any vectors, `|P(y, ȳ')| ≤ |y||y'| tr P`").

For a Hermitian matrix `H` with nonnegative quadratic form (`hermQuad H v ≥ 0`) and the
sesquilinear form `B_H(a, b) = ∑ a_p H_{pq} b̄_q` (`DNTC11.sesqForm`):

* `two_mul_abs_re_sesqForm_le` : `2 |Re B_H(a, b)| ≤ Q_H(a) + Q_H(b)`;
* `abs_re_sesqForm_le` : `|Re B_H(a, b)| ≤ tr H · ‖a‖ ‖b‖`;
* `hermQuad_add_two_re_sesqForm_ge` : `Q_H(a) + 2 Re B_H(a, b) ≥ -Q_H(b) ≥ -tr H ‖b‖²`
  (completing the square, used for FPT's `P[Y]² + 2r² Re P(Y, ·) ≥ -r⁴ P[·]²`).
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexOrder

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Envelopes.DNTC11 SGPT.Envelopes.LapClass3

variable {n : ℕ}

theorem sesqForm_smul_left (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v w : ComplexModel n) :
    sesqForm A (t • v) w = t * sesqForm A v w := by
  simp only [sesqForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem sesqForm_smul_right (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v w : ComplexModel n) :
    sesqForm A v (t • w) = t * sesqForm A v w := by
  simp only [sesqForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem hermQuad_smul_vec (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : ComplexModel n) :
    hermQuad A (t • v) = t ^ 2 * hermQuad A v := by
  simp only [hermQuad, sesqForm_smul_left, sesqForm_smul_right]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- `Q(a ± b) = Q(a) + Q(b) ± 2 Re B(a, b)`. -/
theorem hermQuad_add_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v w : ComplexModel n) :
    hermQuad A (v + w) = hermQuad A v + hermQuad A w + 2 * (sesqForm A v w).re := by
  have hswap := sesqForm_swap hA v w
  simp only [hermQuad, sesqForm_add_left, sesqForm_add_right, Complex.add_re, hswap,
    Complex.star_def, Complex.conj_re]
  ring

theorem hermQuad_sub_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v w : ComplexModel n) :
    hermQuad A (v - w) = hermQuad A v + hermQuad A w - 2 * (sesqForm A v w).re := by
  have hswap := sesqForm_swap hA v w
  simp only [hermQuad, sub_eq_add_neg, sesqForm_add_left, sesqForm_add_right, sesqForm_neg_left,
    sesqForm_neg_right, Complex.add_re, Complex.neg_re, hswap, Complex.star_def, Complex.conj_re]
  ring

/-- `2 |Re B(a, b)| ≤ Q(a) + Q(b)` for a positive semidefinite Hermitian form. -/
theorem two_mul_abs_re_sesqForm_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hP : ∀ v, 0 ≤ hermQuad A v) (v w : ComplexModel n) :
    2 * |(sesqForm A v w).re| ≤ hermQuad A v + hermQuad A w := by
  have h1 := hP (v + w)
  have h2 := hP (v - w)
  rw [hermQuad_add_eq hA] at h1
  rw [hermQuad_sub_eq hA] at h2
  rcases abs_cases (sesqForm A v w).re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- **Cauchy–Schwarz with a trace bound:** `|Re B(a, b)| ≤ tr A · ‖a‖ ‖b‖`. -/
theorem abs_re_sesqForm_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hP : ∀ v, 0 ≤ hermQuad A v) (v w : ComplexModel n) :
    |(sesqForm A v w).re| ≤ A.trace.re * ‖v‖ * ‖w‖ := by
  have htr : 0 ≤ A.trace.re := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Matrix.trace]
    · have := hermQuad_le_trace_mul hA hP (EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1)
      have h0 := hP (EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1)
      simp only [PiLp.norm_single, norm_one, one_pow, mul_one] at this
      linarith
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · have hv0 : v = 0 := norm_eq_zero.mp hv.symm
    subst hv0
    simp [sesqForm]
  rcases eq_or_lt_of_le (norm_nonneg w) with hw | hw
  · have hw0 : w = 0 := norm_eq_zero.mp hw.symm
    subst hw0
    simp [sesqForm]
  -- rescale: `t = √(‖w‖/‖v‖)`
  set t := Real.sqrt (‖w‖ / ‖v‖) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr (div_pos hw hv)
  have ht2 : t ^ 2 = ‖w‖ / ‖v‖ := Real.sq_sqrt (div_pos hw hv).le
  have h := two_mul_abs_re_sesqForm_le hA hP (t • v) (t⁻¹ • w)
  rw [sesqForm_smul_left, sesqForm_smul_right, hermQuad_smul_vec, hermQuad_smul_vec] at h
  have hcancel : ((t : ℂ) * ((t⁻¹ : ℝ) * sesqForm A v w)) = sesqForm A v w := by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht0.ne', Complex.ofReal_one, one_mul]
  rw [hcancel] at h
  have hv2 := hermQuad_le_trace_mul hA hP v
  have hw2 := hermQuad_le_trace_mul hA hP w
  have hinv2 : (t⁻¹) ^ 2 = ‖v‖ / ‖w‖ := by rw [inv_pow, ht2, inv_div]
  have e1 : t ^ 2 * hermQuad A v ≤ ‖w‖ / ‖v‖ * (A.trace.re * ‖v‖ ^ 2) := by
    rw [ht2]; exact mul_le_mul_of_nonneg_left hv2 (div_pos hw hv).le
  have e2 : (t⁻¹) ^ 2 * hermQuad A w ≤ ‖v‖ / ‖w‖ * (A.trace.re * ‖w‖ ^ 2) := by
    rw [hinv2]; exact mul_le_mul_of_nonneg_left hw2 (div_pos hv hw).le
  have e3 : ‖w‖ / ‖v‖ * (A.trace.re * ‖v‖ ^ 2) = A.trace.re * ‖v‖ * ‖w‖ := by
    field_simp
  have e4 : ‖v‖ / ‖w‖ * (A.trace.re * ‖w‖ ^ 2) = A.trace.re * ‖v‖ * ‖w‖ := by
    field_simp
  linarith

/-- **Completing the square:** `Q(a) + 2 Re B(a, b) ≥ -Q(b) ≥ -tr A ‖b‖²`. -/
theorem hermQuad_add_two_re_sesqForm_ge {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hP : ∀ v, 0 ≤ hermQuad A v) (v w : ComplexModel n) :
    -(A.trace.re * ‖w‖ ^ 2) ≤ hermQuad A v + 2 * (sesqForm A v w).re := by
  have h1 := hP (v + w)
  rw [hermQuad_add_eq hA] at h1
  have h2 := hermQuad_le_trace_mul hA hP w
  linarith

end SGPT.NPP.DN3
