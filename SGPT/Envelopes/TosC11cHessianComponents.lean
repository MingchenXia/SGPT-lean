import SGPT.Foundations.Analysis.FirstPass.ComplexManifold

/-!
# The real Hessian from its complex components

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:components`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, end of Step 4: "By the lower bound for `η'` …
and `r_i⁻¹ ≥ c`, this bounds every `a_{ip}` and `a_{i p̄}` at `x₀`, and hence every real second
derivative of `a` there", for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

For a real bilinear form `H` on `ℂⁿ` (the real Hessian `D²a`), with `∂_u = ½(D_u - i D_{iu})`:

* `hessHol H u v = ∂_u ∂_v a` and `hessMixed H u v = ∂_u ∂̄_v a` (as complex numbers, from `H`);
* `abs_apply_le_hess` — the four real components `H(u, v)`, `H(iu, v)`, `H(u, iv)`, `H(iu, iv)` are
  bounded by `2(|∂_u∂_v a| + |∂_u∂̄_v a|)`;
* `abs_apply_le_sum_hess` — `|H(v, w)| ≤ 8 (Σ_{j,p} |a_{jp}| + |a_{j p̄}|) ‖v‖ ‖w‖` (standard basis);
* `norm_le_of_eta_K_le` — **FPT end of Step 4**: if `0 < r_i ≤ R`, `η' ≥ η₀ > 0`, `T ≥ 0` and
  `η' K + T ≤ A n` with `K = Σ_{i,p} (|a_{ip}|² + |a_{i p̄}|²)/r_i`, then
  `‖H‖ ≤ 8 (2n² + R A n / η₀)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- The standard complex basis vector `e_j` of `ℂⁿ`. -/
abbrev stdVec (j : Fin n) : ComplexModel n := EuclideanSpace.single j (1 : ℂ)

/-- `∂_u ∂_v a` from the real Hessian `H = D²a`, with `∂_u = ½(D_u - i D_{iu})`. -/
def hessHol (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (u v : ComplexModel n) : ℂ :=
  ⟨(H u v - H (Complex.I • u) (Complex.I • v)) / 4,
    -(H u (Complex.I • v) + H (Complex.I • u) v) / 4⟩

/-- `∂_u ∂̄_v a` from the real Hessian `H = D²a`, with `∂̄_v = ½(D_v + i D_{iv})`. -/
def hessMixed (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (u v : ComplexModel n) : ℂ :=
  ⟨(H u v + H (Complex.I • u) (Complex.I • v)) / 4,
    (H u (Complex.I • v) - H (Complex.I • u) v) / 4⟩

/-- **The real components from the complex ones**: `H(u, v)`, `H(iu, v)`, `H(u, iv)` and `H(iu, iv)`
are all bounded by `2(|∂_u∂_v a| + |∂_u∂̄_v a|)`. -/
theorem abs_apply_le_hess (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (u v : ComplexModel n) :
    |H u v| ≤ 2 * (‖hessHol H u v‖ + ‖hessMixed H u v‖) ∧
    |H (Complex.I • u) v| ≤ 2 * (‖hessHol H u v‖ + ‖hessMixed H u v‖) ∧
    |H u (Complex.I • v)| ≤ 2 * (‖hessHol H u v‖ + ‖hessMixed H u v‖) ∧
    |H (Complex.I • u) (Complex.I • v)| ≤ 2 * (‖hessHol H u v‖ + ‖hessMixed H u v‖) := by
  have hre1 := Complex.abs_re_le_norm (hessHol H u v)
  have hre2 := Complex.abs_re_le_norm (hessMixed H u v)
  have him1 := Complex.abs_im_le_norm (hessHol H u v)
  have him2 := Complex.abs_im_le_norm (hessMixed H u v)
  have e1 : (hessHol H u v).re = (H u v - H (Complex.I • u) (Complex.I • v)) / 4 := rfl
  have e2 : (hessMixed H u v).re = (H u v + H (Complex.I • u) (Complex.I • v)) / 4 := rfl
  have e3 : (hessHol H u v).im = -(H u (Complex.I • v) + H (Complex.I • u) v) / 4 := rfl
  have e4 : (hessMixed H u v).im = (H u (Complex.I • v) - H (Complex.I • u) v) / 4 := rfl
  rw [e1] at hre1
  rw [e2] at hre2
  rw [e3] at him1
  rw [e4] at him2
  rw [abs_le] at hre1 hre2 him1 him2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
    linarith [hre1.1, hre1.2, hre2.1, hre2.2, him1.1, him1.2, him2.1, him2.2]

/-- Real coordinates in `ℂⁿ`: `v = Σ_j (Re v_j) e_j + (Im v_j) (i e_j)`. -/
theorem eq_sum_re_im (v : ComplexModel n) :
    v = ∑ j, ((v j).re • stdVec j + (v j).im • (Complex.I • stdVec j)) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply, mul_comm Complex.I, Finset.sum_add_distrib,
    Finset.sum_ite_eq]

/-- **Real Hessian bound from the complex components**:
`|H(v, w)| ≤ 8 (Σ_{j,p} |a_{jp}| + |a_{j p̄}|) ‖v‖ ‖w‖`, with `a_{jp} = ∂_j∂_p a`, `a_{j p̄} = ∂_j∂̄_p a`
for the standard basis. -/
theorem abs_apply_le_sum_hess (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (v w : ComplexModel n) :
    |H v w| ≤ 8 * (∑ j, ∑ p, (‖hessHol H (stdVec j) (stdVec p)‖ +
      ‖hessMixed H (stdVec j) (stdVec p)‖)) * ‖v‖ * ‖w‖ := by
  set S : Fin n → Fin n → ℝ := fun j p =>
    ‖hessHol H (stdVec j) (stdVec p)‖ + ‖hessMixed H (stdVec j) (stdVec p)‖ with hS
  have hterm : ∀ j p, |H ((v j).re • stdVec j + (v j).im • (Complex.I • stdVec j))
      ((w p).re • stdVec p + (w p).im • (Complex.I • stdVec p))| ≤ 8 * S j p * ‖v‖ * ‖w‖ := by
    intro j p
    obtain ⟨h1, h2, h3, h4⟩ := abs_apply_le_hess H (stdVec j) (stdVec p)
    have hx : |(v j).re| ≤ ‖v‖ := (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le v j)
    have hy : |(v j).im| ≤ ‖v‖ := (Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le v j)
    have hx' : |(w p).re| ≤ ‖w‖ := (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le w p)
    have hy' : |(w p).im| ≤ ‖w‖ := (Complex.abs_im_le_norm _).trans (PiLp.norm_apply_le w p)
    have hexp : H ((v j).re • stdVec j + (v j).im • (Complex.I • stdVec j))
        ((w p).re • stdVec p + (w p).im • (Complex.I • stdVec p)) =
        (v j).re * (w p).re * H (stdVec j) (stdVec p) +
        (v j).re * (w p).im * H (stdVec j) (Complex.I • stdVec p) +
        (v j).im * (w p).re * H (Complex.I • stdVec j) (stdVec p) +
        (v j).im * (w p).im * H (Complex.I • stdVec j) (Complex.I • stdVec p) := by
      simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hexp]
    have hS0 : 0 ≤ 2 * S j p := by simp only [hS]; positivity
    have key : ∀ (x y t : ℝ), |x| ≤ ‖v‖ → |y| ≤ ‖w‖ → |t| ≤ 2 * S j p →
        |x * y * t| ≤ ‖v‖ * ‖w‖ * (2 * S j p) := fun x y t hx hy ht => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _)) ht (abs_nonneg _)
        (by positivity)
    have b1 := key _ _ _ hx hx' h1
    have b2 := key _ _ _ hx hy' h3
    have b3 := key _ _ _ hy hx' h2
    have b4 := key _ _ _ hy hy' h4
    have t1 := abs_add_le ((v j).re * (w p).re * H (stdVec j) (stdVec p) +
        (v j).re * (w p).im * H (stdVec j) (Complex.I • stdVec p) +
        (v j).im * (w p).re * H (Complex.I • stdVec j) (stdVec p))
      ((v j).im * (w p).im * H (Complex.I • stdVec j) (Complex.I • stdVec p))
    have t2 := abs_add_le ((v j).re * (w p).re * H (stdVec j) (stdVec p) +
        (v j).re * (w p).im * H (stdVec j) (Complex.I • stdVec p))
      ((v j).im * (w p).re * H (Complex.I • stdVec j) (stdVec p))
    have t3 := abs_add_le ((v j).re * (w p).re * H (stdVec j) (stdVec p))
      ((v j).re * (w p).im * H (stdVec j) (Complex.I • stdVec p))
    have e : 8 * S j p * ‖v‖ * ‖w‖ = 4 * (‖v‖ * ‖w‖ * (2 * S j p)) := by ring
    rw [e]
    linarith
  have hexp : H v w = ∑ j, ∑ p, H ((v j).re • stdVec j + (v j).im • (Complex.I • stdVec j))
      ((w p).re • stdVec p + (w p).im • (Complex.I • stdVec p)) := by
    conv_lhs => rw [eq_sum_re_im v, eq_sum_re_im w]
    simp only [map_sum, sum_apply]
    exact Finset.sum_comm
  rw [hexp]
  calc _ ≤ ∑ j, |∑ p, H ((v j).re • stdVec j + (v j).im • (Complex.I • stdVec j))
          ((w p).re • stdVec p + (w p).im • (Complex.I • stdVec p))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ p, 8 * S j p * ‖v‖ * ‖w‖ :=
        Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p _ => hterm j p)
    _ = 8 * (∑ j, ∑ p, S j p) * ‖v‖ * ‖w‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]

/-- **From `η'K + T ≤ An` to a bound for the real Hessian** (FPT `lem:penalized-real-hessian`, end of
Step 4): if `0 < r_i ≤ R`, `0 < η₀ ≤ η'`, `T ≥ 0` and `η' K + T ≤ A n` with
`K = Σ_{i,p} (|a_{ip}|² + |a_{i p̄}|²)/r_i`, then `‖H‖ ≤ 8 (2n² + R (A n / η₀))`. -/
theorem norm_le_of_eta_K_le (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) {r : Fin n → ℝ}
    {R A η₀ η' T : ℝ} (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i ≤ R) (hR : 0 ≤ R) (hη₀ : 0 < η₀)
    (hη' : η₀ ≤ η') (hT : 0 ≤ T)
    (h : η' * (∑ i, ∑ p, (‖hessHol H (stdVec i) (stdVec p)‖ ^ 2 +
      ‖hessMixed H (stdVec i) (stdVec p)‖ ^ 2) / r i) + T ≤ A * n) :
    ‖H‖ ≤ 8 * (2 * n ^ 2 + R * (A * n / η₀)) := by
  set K := ∑ i, ∑ p, (‖hessHol H (stdVec i) (stdVec p)‖ ^ 2 +
    ‖hessMixed H (stdVec i) (stdVec p)‖ ^ 2) / r i with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ =>
    div_nonneg (by positivity) (hr i).le
  have hK : K ≤ A * n / η₀ := by
    rw [le_div_iff₀ hη₀]
    have := mul_le_mul_of_nonneg_right hη' hK0
    linarith
  have hpt : ∀ i p, ‖hessHol H (stdVec i) (stdVec p)‖ + ‖hessMixed H (stdVec i) (stdVec p)‖ ≤
      2 + R * ((‖hessHol H (stdVec i) (stdVec p)‖ ^ 2 +
        ‖hessMixed H (stdVec i) (stdVec p)‖ ^ 2) / r i) := by
    intro i p
    set x := ‖hessHol H (stdVec i) (stdVec p)‖
    set y := ‖hessMixed H (stdVec i) (stdVec p)‖
    have h1 : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have h2 : y ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
    have h3 : x ^ 2 + y ^ 2 ≤ R * ((x ^ 2 + y ^ 2) / r i) := by
      rw [mul_div_assoc', le_div_iff₀ (hr i)]
      have hxy : 0 ≤ x ^ 2 + y ^ 2 := by positivity
      nlinarith [hrR i]
    linarith
  have hS : ∑ i, ∑ p, (‖hessHol H (stdVec i) (stdVec p)‖ + ‖hessMixed H (stdVec i) (stdVec p)‖) ≤
      2 * n ^ 2 + R * K := by
    calc _ ≤ ∑ i : Fin n, ∑ p : Fin n, (2 + R * ((‖hessHol H (stdVec i) (stdVec p)‖ ^ 2 +
          ‖hessMixed H (stdVec i) (stdVec p)‖ ^ 2) / r i)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ => hpt i p
      _ = 2 * n ^ 2 + R * K := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hKdef, Finset.mul_sum]
          ring
  have hbound : 0 ≤ 8 * (2 * n ^ 2 + R * (A * n / η₀)) := by
    have : 0 ≤ A * n / η₀ := hK0.trans hK
    positivity
  refine ContinuousLinearMap.opNorm_le_bound₂ H hbound fun v w => ?_
  rw [Real.norm_eq_abs]
  have hS' : ∑ i, ∑ p, (‖hessHol H (stdVec i) (stdVec p)‖ + ‖hessMixed H (stdVec i) (stdVec p)‖) ≤
      2 * n ^ 2 + R * (A * n / η₀) := hS.trans (by gcongr)
  calc |H v w| ≤ 8 * (∑ j, ∑ p, (‖hessHol H (stdVec j) (stdVec p)‖ +
        ‖hessMixed H (stdVec j) (stdVec p)‖)) * ‖v‖ * ‖w‖ := abs_apply_le_sum_hess H v w
    _ ≤ 8 * (2 * n ^ 2 + R * (A * n / η₀)) * ‖v‖ * ‖w‖ := by gcongr

end SGPT.Envelopes.TosC11c
