import SGPT.NPP.DN3RadialConvex

/-!
# Trace masses controlled by the logarithmic slope

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 5, and the trace-mass bound
`m_u ≤ M/r` used for `eq:chern-improved-joint-bound`).

In the kernel-square identity all error terms are integrals of the trace of the complex Hessian
against the weights `χ` or `-χ₁` at scale `r`.  Here they are controlled by the logarithmic slope
`λ_g = r Φ_g'` of the radial mean (`DN3RadialConvex`), so that no Jensen–Lelong formula is needed:

* `integral_mul_chi_le` : for continuous `T ≥ 0`,
  `∫ T(ρζ) χ(‖ζ‖²) dζ ≤ A_n ∫ T(2ρζ) (-χ₁(‖ζ‖²)) dζ` with `A_n = 2^{2n+1} e^{4/3}`
  (the weight `χ(4t)` is supported in `t < 1/4`, where `-χ₁ ≥ C_n e^{-4/3}`, and `χ ≤ 2 C_n`);
* `sq_mul_integral_levTr_le_radialSlope` : for plurisubharmonic `C²` functions,
  `ρ² ∫ (∑ₘ g_{m m̄})(ρζ) χ(‖ζ‖²) dζ ≤ (A_n/8) λ_g(2ρ)`;
* `radialSlope_le_of_lt` : `λ_g(r) log(R/r) ≤ Φ_g(R) - Φ_g(r)` (convexity in `log r`), and
  `radialMean_ge` : `Φ_g(r) ≥ g(0)`; hence a linear bound `Φ_g(t) ≤ g(0) + L t` gives
  `λ_g(r) ≤ e L r` (`radialSlope_le_of_linear`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.LapClass

variable {n : ℕ}

/-! ### Comparison of the two weights -/

theorem weightCore_le_two (t : ℝ) : weightCore t ≤ 2 := by
  rcases lt_or_ge t 1 with ht | ht
  · rw [weightCore_eq_of_lt ht]
    set x := (1 - t)⁻¹ with hx
    have hx0 : 0 ≤ x := inv_nonneg.mpr (by linarith)
    have h1 : ((1 - t) ^ 2)⁻¹ = x ^ 2 := by rw [hx, inv_pow]
    rw [h1]
    have h2 : x ^ 2 / 2 ≤ Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx0 2
      simpa using this
    have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith
  · rw [weightCore_eq_zero_of_le ht]; norm_num

theorem chi_le (t : ℝ) : chi n t ≤ 2 * (weightMass n)⁻¹ := by
  rw [chi, mul_comm]
  exact mul_le_mul_of_nonneg_right (weightCore_le_two t) (inv_nonneg.mpr (weightMass_pos n).le)

/-- `-χ₁ ≥ C_n e^{-4/3}` on `t ≤ 1/4`. -/
theorem neg_chiOne_ge {t : ℝ} (ht : t ≤ 1 / 4) :
    (weightMass n)⁻¹ * Real.exp (-(4 / 3)) ≤ -chiOne n t := by
  rw [chiOne, neg_neg, weightGlue_eq_of_lt (by linarith)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr (weightMass_pos n).le)
  have h1 : (3 / 4 : ℝ) ≤ 1 - t := by linarith
  have h2 : (1 - t)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- `χ(4t) ≤ 2 e^{4/3} (-χ₁(t))` for `t ≥ 0`. -/
theorem chi_four_mul_le {t : ℝ} :
    chi n (4 * t) ≤ 2 * Real.exp (4 / 3) * -chiOne n t := by
  rcases lt_or_ge t (1 / 4) with ht | ht
  · have h1 := neg_chiOne_ge (n := n) ht.le
    have h2 := chi_le (n := n) (4 * t)
    have h3 : Real.exp (4 / 3) * Real.exp (-(4 / 3)) = 1 := by rw [← Real.exp_add]; simp
    calc chi n (4 * t) ≤ 2 * (weightMass n)⁻¹ := h2
      _ = 2 * Real.exp (4 / 3) * ((weightMass n)⁻¹ * Real.exp (-(4 / 3))) := by
          have e : 2 * Real.exp (4 / 3) * ((weightMass n)⁻¹ * Real.exp (-(4 / 3))) =
              2 * (weightMass n)⁻¹ * (Real.exp (4 / 3) * Real.exp (-(4 / 3))) := by ring
          rw [e, h3, mul_one]
      _ ≤ 2 * Real.exp (4 / 3) * -chiOne n t :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [chi_eq_zero_of_le n (by linarith)]
    exact mul_nonneg (by positivity) (neg_nonneg.mpr (chiOne_nonpos n t))

/-- The constant `A_n = 2^{2n+1} e^{4/3}`. -/
def weightConst (n : ℕ) : ℝ := 2 ^ (2 * n) * (2 * Real.exp (4 / 3))

theorem weightConst_pos : 0 < weightConst n := by unfold weightConst; positivity

theorem continuous_neg_chiOne_normSq :
    Continuous fun ζ : ComplexModel n => -chiOne n (‖ζ‖ ^ 2) :=
  ((contDiff_chiOne n).continuous.comp (continuous_norm.pow 2)).neg

/-- **Comparison of the weights.**  For continuous `T ≥ 0` and `ρ ∈ ℝ`,
`∫ T(ρζ) χ(‖ζ‖²) dζ ≤ A_n ∫ T(2ρζ) (-χ₁(‖ζ‖²)) dζ`. -/
theorem integral_mul_chi_le {T : ComplexModel n → ℝ} (hT : Continuous T) (hT0 : ∀ y, 0 ≤ T y)
    (ρ : ℝ) :
    ∫ ζ, T (ρ • ζ) * kernel n ζ ≤
      weightConst n * ∫ ζ, T ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2) := by
  have hscale := Measure.integral_comp_smul (μ := (volume : Measure (ComplexModel n)))
    (fun ζ => T (ρ • ζ) * kernel n ζ) 2
  rw [PshRadialRegularization.finrank_complexModel] at hscale
  have hpow : |((2 : ℝ) ^ (2 * n))⁻¹| = ((2 : ℝ) ^ (2 * n))⁻¹ := abs_of_pos (by positivity)
  rw [hpow, smul_eq_mul] at hscale
  have h2n : (0 : ℝ) < 2 ^ (2 * n) := by positivity
  have heq : ∫ ζ, T (ρ • ζ) * kernel n ζ =
      2 ^ (2 * n) * ∫ ζ, T (ρ • ((2 : ℝ) • ζ)) * kernel n ((2 : ℝ) • ζ) := by
    rw [hscale, ← mul_assoc, mul_inv_cancel₀ h2n.ne', one_mul]
  rw [heq, weightConst, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h2n.le
  rw [← integral_const_mul]
  have hKs : HasCompactSupport fun ξ : ComplexModel n => -chiOne n (‖ξ‖ ^ 2) :=
    hasCompactSupport_chiOne_normSq.neg
  refine integral_mono_of_nonneg (Eventually.of_forall fun ζ => ?_) ?_
    (Eventually.of_forall fun ζ => ?_)
  · exact mul_nonneg (hT0 _) (kernel_nonneg _)
  · exact (continuous_const.mul ((hT.comp (continuous_const_smul (2 * ρ))).mul
      continuous_neg_chiOne_normSq)).integrable_of_hasCompactSupport hKs.mul_left.mul_left
  · simp only
    rw [smul_smul, mul_comm ρ 2]
    have hk : kernel n ((2 : ℝ) • ζ) = chi n (4 * ‖ζ‖ ^ 2) := by
      rw [kernel, norm_smul, Real.norm_two, mul_pow]; norm_num
    rw [hk]
    have := chi_four_mul_le (n := n) (t := ‖ζ‖ ^ 2)
    have hT0' := hT0 ((2 * ρ) • ζ)
    nlinarith

/-- **Trace masses at scale `ρ` are controlled by the slope at scale `2ρ`.**  For a
plurisubharmonic `C²` function `g`,
`ρ² ∫ (∑ₘ g_{m m̄})(ρζ) χ(‖ζ‖²) dζ ≤ (A_n / 8) λ_g(2ρ)`. -/
theorem sq_mul_integral_levTr_le_radialSlope {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) (ρ : ℝ) :
    ρ ^ 2 * ∫ ζ, levTr g (ρ • ζ) * kernel n ζ ≤ weightConst n / 8 * radialSlope g (2 * ρ) := by
  have hTc : Continuous (levTr g) := by
    have : levTr g = fun y => ∑ p, leviForm g y (coordinateVector p) := rfl
    rw [this]
    refine continuous_finsetSum _ fun p _ => ?_
    simp only [leviForm, realHessian_eq_fderiv]
    have hD2c : Continuous (fderiv ℝ (fderiv ℝ g)) :=
      (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    exact (((hD2c.clm_apply continuous_const).clm_apply continuous_const).add
      ((hD2c.clm_apply continuous_const).clm_apply continuous_const)).div_const 4
  have hT0 : ∀ y, 0 ≤ levTr g y := fun y => Finset.sum_nonneg fun p _ => hpsh _ _
  have h := integral_mul_chi_le hTc hT0 ρ
  rw [radialSlope_eq hg]
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  calc ρ ^ 2 * ∫ ζ, levTr g (ρ • ζ) * kernel n ζ
      ≤ ρ ^ 2 * (weightConst n * ∫ ζ, levTr g ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hρ2
    _ = weightConst n / 8 * (2 * (2 * ρ) ^ 2 *
          ∫ ζ, levTr g ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2)) := by ring

/-! ### Slopes bounded by increments -/

theorem radialMean_zero (g : ComplexModel n → ℝ) : radialMean g 0 = g 0 := by
  simp only [radialMean, zero_smul]
  rw [integral_const_mul, integral_kernel, mul_one]

/-- For plurisubharmonic `C²` functions, `r ↦ Φ_g(r)` is nondecreasing on `[0, ∞)`. -/
theorem radialMean_mono {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) : MonotoneOn (radialMean g) (Ici 0) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun r _ => (hasDerivAt_radialMean hg1 r).continuousAt.continuousWithinAt)
    (fun r _ => (hasDerivAt_radialMean hg1 r).differentiableAt.differentiableWithinAt)
    fun r hr => ?_
  rw [interior_Ici] at hr
  have hr0 : 0 < r := hr
  have h := radialSlope_nonneg hg hpsh r
  rw [radialSlope_eq_mul_deriv hg1] at h
  exact (mul_nonneg_iff_of_pos_left hr0).mp h

/-- `Φ_g(r) ≥ g(0)` for plurisubharmonic `C²` functions and `r ≥ 0`. -/
theorem radialMean_ge {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) {r : ℝ} (hr : 0 ≤ r) : g 0 ≤ radialMean g r := by
  rw [← radialMean_zero g]
  exact radialMean_mono hg hpsh (le_refl (0 : ℝ)) hr hr

/-- **Convexity in `log r`:** `λ_g(r) log(R/r) ≤ Φ_g(R) - Φ_g(r)` for `0 < r ≤ R`. -/
theorem radialSlope_mul_log_le {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    radialSlope g r * Real.log (R / r) ≤ radialMean g R - radialMean g r := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  set f : ℝ → ℝ := fun s => radialMean g (Real.exp s)
  set f' : ℝ → ℝ := fun s => radialSlope g (Real.exp s)
  have hf : ∀ s, HasDerivAt f (f' s) s := hasDerivAt_radialMean_exp hg1
  have hf' : ∀ s, HasDerivAt f' (radialLevi g (Real.exp s)) s := hasDerivAt_radialSlope_exp hg
  have hmono : Monotone f' :=
    monotone_of_deriv_nonneg (fun s => (hf' s).differentiableAt)
      fun s => by rw [(hf' s).deriv]; exact radialLevi_nonneg hpsh _
  have hR : 0 < R := hr.trans_le hrR
  have hlog : Real.log (R / r) = Real.log R - Real.log r := Real.log_div hR.ne' hr.ne'
  rcases eq_or_lt_of_le hrR with h | h
  · subst h; simp
  have hlt : Real.log r < Real.log R := Real.log_lt_log hr h
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => hf s)
  have hfr : f (Real.log r) = radialMean g r := by simp [f, Real.exp_log hr]
  have hfR : f (Real.log R) = radialMean g R := by simp [f, Real.exp_log hR]
  have h1 : f' (Real.log r) ≤ f' c := hmono hc.1.le
  have h2 : f' (Real.log r) = radialSlope g r := by simp [f', Real.exp_log hr]
  rw [hcs, hfr, hfR] at h1
  rw [h2] at h1
  rw [hlog]
  have hpos : 0 < Real.log R - Real.log r := by linarith
  rwa [le_div_iff₀ hpos] at h1

/-- **A linear bound for the radial mean bounds the slope:** if `Φ_g(e r) ≤ g(0) + L e r`
then `λ_g(r) ≤ e L r`. -/
theorem radialSlope_le_of_linear {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) {r L : ℝ} (hr : 0 < r)
    (hlin : radialMean g (Real.exp 1 * r) ≤ g 0 + L * (Real.exp 1 * r)) :
    radialSlope g r ≤ L * (Real.exp 1 * r) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hrR : r ≤ Real.exp 1 * r := le_mul_of_one_le_left hr.le he
  have h := radialSlope_mul_log_le hg hpsh hr hrR
  rw [mul_div_assoc, div_self hr.ne', mul_one, Real.log_exp, mul_one] at h
  have h0 := radialMean_ge hg hpsh hr.le
  linarith

end SGPT.NPP.DN3
