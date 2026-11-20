import SGPT.Envelopes.TosC11dJets

/-!
# Algebra at the maximum point: complex components, the splitting identity, eigen-expansions

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:algebra`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 3–4, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

* `cz x y = ½(x - i y)`, the complex number `∂ᵢ f = ½(∂_{xᵢ} f - i ∂_{yᵢ} f)` built from the two
  real derivatives; `‖cz x y‖² = ¼(x² + y²)`.
* `cz_split` — **the splitting identity** behind `eq:real-hessian-third-splitting`: for real covectors
  `L₁, L₂` and `b ∈ ℂⁿ`, with `L = ½(L₁ - i L₂)` (complex-valued, real linear),
  `L(b) = Σ_q b̄_q (L(e_q) + i L(i e_q)) - i L(i b)` (in FPT's notation `V₁ = √2 W̄ - i JV₁`).
* `apply_self_eq_sum_eigen` — `B(Y, Y) = Σᵢ μᵢ ⟪bᵢ, Y⟫²` in an orthonormal eigenbasis.
* `abs_apply_le_of_quad` — polarization: a symmetric form with `|B(Y, Y)| ≤ c ‖Y‖²` satisfies
  `|B(Y, Z)| ≤ c ‖Y‖ ‖Z‖`.
* `norm_apply_le_of_frame'` — a linear map bounded by `C` on the real frame `eⱼ, i eⱼ` has norm
  at most `2 n C`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Complex components -/

/-- The complex number `½(x - i y)`. -/
def cz (x y : ℝ) : ℂ := ⟨x / 2, -y / 2⟩

@[simp] theorem cz_re (x y : ℝ) : (cz x y).re = x / 2 := rfl
@[simp] theorem cz_im (x y : ℝ) : (cz x y).im = -y / 2 := rfl

theorem norm_cz_sq (x y : ℝ) : ‖cz x y‖ ^ 2 = (x ^ 2 + y ^ 2) / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, cz_re, cz_im]; ring

theorem norm_cz_le (x y : ℝ) : ‖cz x y‖ ≤ (|x| + |y|) / 2 := by
  have h : cz x y = ((x / 2 : ℝ) : ℂ) + ((-y / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h]
  calc ‖((x / 2 : ℝ) : ℂ) + ((-y / 2 : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((x / 2 : ℝ) : ℂ)‖ + ‖((-y / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (|x| + |y|) / 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, abs_neg, abs_two]
        ring

theorem cz_sub (x y x' y' : ℝ) : cz (x - x') (y - y') = cz x y - cz x' y' := by
  apply Complex.ext <;> simp <;> ring

theorem cz_add (x y x' y' : ℝ) : cz (x + x') (y + y') = cz x y + cz x' y' := by
  apply Complex.ext <;> simp <;> ring

theorem cz_smul (c x y : ℝ) : cz (c * x) (c * y) = (c : ℂ) * cz x y := by
  apply Complex.ext <;> simp <;> ring

theorem cz_sum {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    cz (∑ i ∈ s, x i) (∑ i ∈ s, y i) = ∑ i ∈ s, cz (x i) (y i) := by
  apply Complex.ext
  · simp only [cz_re, Complex.re_sum, Finset.sum_div]
  · simp only [cz_im, Complex.im_sum, Finset.sum_div, neg_div, Finset.sum_neg_distrib]

/-- **The splitting identity** (`eq:real-hessian-third-splitting`, algebraic part): for real
covectors `L₁, L₂` and `b ∈ ℂⁿ`,
`cz(L₁ b, L₂ b) = Σ_q b̄_q (cz(L₁ e_q, L₂ e_q) + i cz(L₁ (i e_q), L₂ (i e_q))) - i cz(L₁ (i b), L₂ (i b))`. -/
theorem cz_split (L₁ L₂ : ComplexModel n →L[ℝ] ℝ) (b : ComplexModel n) :
    cz (L₁ b) (L₂ b) = ∑ q, conj (b q) * (cz (L₁ (TosC11c.stdVec q)) (L₂ (TosC11c.stdVec q)) +
      Complex.I * cz (L₁ (Complex.I • TosC11c.stdVec q)) (L₂ (Complex.I • TosC11c.stdVec q))) -
      Complex.I * cz (L₁ (Complex.I • b)) (L₂ (Complex.I • b)) := by
  have hb := TosC11c.eq_sum_re_im b
  have hIb : Complex.I • b = ∑ q, ((b q).re • (Complex.I • TosC11c.stdVec q) -
      (b q).im • TosC11c.stdVec q) := by
    conv_lhs => rw [hb]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_add, smul_comm Complex.I ((b q).re), smul_comm Complex.I ((b q).im), smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_neg, sub_eq_add_neg]
  have e1 : ∀ L : ComplexModel n →L[ℝ] ℝ, L b = ∑ q, ((b q).re * L (TosC11c.stdVec q) +
      (b q).im * L (Complex.I • TosC11c.stdVec q)) := fun L => by
    conv_lhs => rw [hb]
    simp [map_sum, map_add, map_smul, smul_eq_mul]
  have e2 : ∀ L : ComplexModel n →L[ℝ] ℝ, L (Complex.I • b) =
      ∑ q, ((b q).re * L (Complex.I • TosC11c.stdVec q) - (b q).im * L (TosC11c.stdVec q)) :=
    fun L => by
      rw [hIb]
      simp [map_sum, map_sub, map_smul, smul_eq_mul]
  rw [e1, e1, e2, e2, cz_sum, cz_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  apply Complex.ext <;>
    simp only [cz_re, cz_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im] <;> ring

/-! ### Eigen-expansions and polarization -/

/-- `B(Y, Y) = Σᵢ μᵢ ⟪bᵢ, Y⟫²` in an orthonormal eigenbasis of the operator of `B`. -/
theorem apply_self_eq_sum_eigen {ι : Type*} [Fintype ι]
    (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (μ : ι → ℝ)
    (hb : ∀ i, bilinOpL B (b i) = μ i • b i) (Y : ComplexModel n) :
    B Y Y = ∑ i, μ i * ⟪b i, Y⟫ ^ 2 := by
  have hY : Y = ∑ i, ⟪b i, Y⟫ • b i := (b.sum_repr' Y).symm
  have hBY : bilinOpL B Y = ∑ i, (⟪b i, Y⟫ * μ i) • b i := by
    conv_lhs => rw [hY]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, smul_smul]
  rw [← inner_bilinOpL, hBY, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, real_inner_comm]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- Parseval: `Σᵢ ⟪bᵢ, Y⟫² = ‖Y‖²`. -/
theorem sum_inner_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (ComplexModel n))
    (Y : ComplexModel n) : ∑ i, ⟪b i, Y⟫ ^ 2 = ‖Y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner Y Y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm Y]; ring

/-- `⟪Y, i Y⟫ = 0` for the real inner product of `ℂⁿ`. -/
theorem inner_I_smul_self (Y : ComplexModel n) : ⟪Y, Complex.I • Y⟫ = 0 := by
  rw [Pending.ComplexHessianDeterminant.real_inner_eq_re, inner_smul_right,
    inner_self_eq_norm_sq_to_K, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, neg_eq_zero]
  norm_cast

theorem norm_I_smul (Y : ComplexModel n) : ‖Complex.I • Y‖ = ‖Y‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]

/-- **Polarization**: a symmetric form with `|B(Y, Y)| ≤ c ‖Y‖²` satisfies `|B(Y, Z)| ≤ c ‖Y‖ ‖Z‖`. -/
theorem abs_apply_le_of_quad {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = B y x) {c : ℝ} (hc : ∀ Y, |B Y Y| ≤ c * ‖Y‖ ^ 2) (Y Z : ComplexModel n) :
    |B Y Z| ≤ c * ‖Y‖ * ‖Z‖ := by
  have hpol : ∀ Y Z, |B Y Z| ≤ c * (‖Y‖ ^ 2 + ‖Z‖ ^ 2) / 2 := by
    intro Y Z
    have e : B Y Z = (B (Y + Z) (Y + Z) - B (Y - Z) (Y - Z)) / 4 := by
      simp only [map_add, map_sub, add_apply, sub_apply, hB Z Y]; ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have h1 := hc (Y + Z)
    have h2 := hc (Y - Z)
    have hp : ‖Y + Z‖ ^ 2 + ‖Y - Z‖ ^ 2 = 2 * (‖Y‖ ^ 2 + ‖Z‖ ^ 2) := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
      ring
    have := abs_sub (B (Y + Z) (Y + Z)) (B (Y - Z) (Y - Z))
    have : |B (Y + Z) (Y + Z) - B (Y - Z) (Y - Z)| ≤ c * (2 * (‖Y‖ ^ 2 + ‖Z‖ ^ 2)) := by
      rw [← hp]; linarith
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  rcases eq_or_ne Y 0 with rfl | hY
  · simp
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hYn : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hZn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have h := hpol (‖Y‖⁻¹ • Y) (‖Z‖⁻¹ • Z)
  have hu : ‖‖Y‖⁻¹ • Y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hYn.ne']
  have hv : ‖‖Z‖⁻¹ • Z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hZn.ne']
  rw [hu, hv, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul,
    abs_mul, abs_mul, abs_inv, abs_inv, abs_norm, abs_norm] at h
  have e : |B Y Z| = ‖Y‖ * ‖Z‖ * (‖Z‖⁻¹ * (‖Y‖⁻¹ * |B Y Z|)) := by field_simp
  rw [e]
  have : ‖Z‖⁻¹ * (‖Y‖⁻¹ * |B Y Z|) ≤ c := by linarith
  calc ‖Y‖ * ‖Z‖ * (‖Z‖⁻¹ * (‖Y‖⁻¹ * |B Y Z|)) ≤ ‖Y‖ * ‖Z‖ * c :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = c * ‖Y‖ * ‖Z‖ := by ring

/-- A linear map bounded by `C` on the real frame `eⱼ, i eⱼ` is bounded by `2 n C ‖v‖`. -/
theorem norm_apply_le_of_frame' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ComplexModel n →L[ℝ] F) {C : ℝ}
    (hL : ∀ j, ‖L (TosC11c.stdVec j)‖ ≤ C ∧ ‖L (Complex.I • TosC11c.stdVec j)‖ ≤ C)
    (v : ComplexModel n) : ‖L v‖ ≤ 2 * n * C * ‖v‖ := by
  have hexp : L v = ∑ j, ((v j).re • L (TosC11c.stdVec j) +
      (v j).im • L (Complex.I • TosC11c.stdVec j)) := by
    conv_lhs => rw [TosC11c.eq_sum_re_im v]
    simp [map_sum, map_add, map_smul]
  rw [hexp]
  have hterm : ∀ j, ‖(v j).re • L (TosC11c.stdVec j) +
      (v j).im • L (Complex.I • TosC11c.stdVec j)‖ ≤ 2 * C * ‖v‖ := by
    intro j
    calc _ ≤ ‖(v j).re • L (TosC11c.stdVec j)‖ + ‖(v j).im • L (Complex.I • TosC11c.stdVec j)‖ :=
          norm_add_le _ _
      _ ≤ ‖v‖ * C + ‖v‖ * C := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul (abs_re_le v j) (hL j).1 (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul (abs_im_le v j) (hL j).2 (norm_nonneg _) (norm_nonneg _))
      _ = 2 * C * ‖v‖ := by ring
  calc _ ≤ ∑ j, ‖(v j).re • L (TosC11c.stdVec j) + (v j).im • L (Complex.I • TosC11c.stdVec j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, 2 * C * ‖v‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * n * C * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end SGPT.Envelopes.TosC11d
