import SGPT.NPP.DN3RadialWeight
import SGPT.Envelopes.LapClassFlat
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

/-!
# The logarithmic slope of the radial mean

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`,
`chapters/inputs/q10-big-envelope-regularity.tex`, eq. `eq:chern-radial-derivative`).

For a function `g` on `ℂⁿ` let `Φ_g(r) = ∫ g(r ζ) χ(‖ζ‖²) dζ` be its radial mean with the weight
of `DN3RadialWeight` (`radialMean`).  For `C²` functions FPT's identity

  `r ∂_r Φ_g(r) = -2 r² ∫ χ₁(‖ζ‖²) ∑ₘ g_{m m̄}(r ζ) dζ`

holds (`radialMean_slope`): differentiate under the integral sign
(`hasDerivAt_radialMean`), write `χ(‖ζ‖²) ζ = ½ ∇(χ₁(‖ζ‖²))` and integrate by parts once in each
real direction of an orthonormal basis; the trace of the real Hessian is `4 ∑ₘ g_{m m̄}`
(`sum_hessian_orthonormalBasis`).  Since `-χ₁ ≥ 0`, the slope is nonnegative for
plurisubharmonic `g` (`radialMean_slope_nonneg`).

In the joint smoothing this is the formula `λ_p = r ∂_r Ψ_p = 2r² ∫ (-χ₁) tr G(rs) ds` at the centre,
through which all error terms of the kernel-square identity are controlled.
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

/-- The radial mean `Φ_g(r) = ∫ g(r ζ) χ(‖ζ‖²) dζ`. -/
def radialMean (g : ComplexModel n → ℝ) (r : ℝ) : ℝ := ∫ ζ, g (r • ζ) * kernel n ζ

theorem kernel_nonneg (ζ : ComplexModel n) : 0 ≤ kernel n ζ := chi_nonneg n _

theorem hasCompactSupport_kernel : HasCompactSupport (kernel n) :=
  (isRadialKernel_kernel n).hasCompactSupport

theorem norm_le_one_of_kernel_ne_zero {ζ : ComplexModel n} (h : kernel n ζ ≠ 0) : ‖ζ‖ ≤ 1 := by
  by_contra h'
  exact h (kernel_eq_zero n (not_le.mp h').le)

/-- **Differentiation of the radial mean.**  For `C¹` functions,
`Φ_g'(r) = ∫ Dg(r ζ)(ζ) χ(‖ζ‖²) dζ`. -/
theorem hasDerivAt_radialMean {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 1 g) (r : ℝ) :
    HasDerivAt (radialMean g) (∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ) r := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hKc : Continuous (kernel n) := (contDiff_kernel n).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ComplexModel n) (|r| + 1)).exists_bound_of_continuousOn
    hDc.continuousOn
  have hcontF : ∀ x : ℝ, Continuous fun ζ : ComplexModel n => g (x • ζ) * kernel n ζ :=
    fun x => (hg.continuous.comp (continuous_const_smul x)).mul hKc
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball r 1)
    (F := fun x ζ => g (x • ζ) * kernel n ζ)
    (F' := fun x ζ => fderiv ℝ g (x • ζ) ζ * kernel n ζ)
    (bound := fun ζ => M * kernel n ζ) (ball_mem_nhds r one_pos)
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable)
    ((hcontF r).integrable_of_hasCompactSupport (hasCompactSupport_kernel.mul_left))
    ?_ ?_ ((isRadialKernel_kernel n).integrable.const_mul M) ?_).2
  · exact (((hDc.comp (continuous_const_smul r)).clm_apply continuous_id).mul
      hKc).aestronglyMeasurable
  · refine Eventually.of_forall fun ζ x hx => ?_
    rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg ζ)]
    by_cases hK : kernel n ζ = 0
    · rw [hK, mul_zero, mul_zero]
    refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg ζ)
    have hζ := norm_le_one_of_kernel_ne_zero hK
    have hx' : |x| ≤ |r| + 1 := by
      have := mem_ball.mp hx
      rw [Real.dist_eq] at this
      have h1 : |x| ≤ |r| + |x - r| := by
        calc |x| = |r + (x - r)| := by ring_nf
          _ ≤ |r| + |x - r| := abs_add_le _ _
      linarith
    have hmem : x • ζ ∈ closedBall (0 : ComplexModel n) (|r| + 1) := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
      calc |x| * ‖ζ‖ ≤ (|r| + 1) * 1 :=
            mul_le_mul hx' hζ (norm_nonneg _) (by positivity)
        _ = |r| + 1 := mul_one _
    calc ‖fderiv ℝ g (x • ζ) ζ‖ ≤ ‖fderiv ℝ g (x • ζ)‖ * ‖ζ‖ := (fderiv ℝ g (x • ζ)).le_opNorm ζ
      _ ≤ M * 1 := mul_le_mul (hM _ hmem) hζ (norm_nonneg _) ((norm_nonneg _).trans (hM _ hmem))
      _ = M := mul_one M
  · refine Eventually.of_forall fun ζ x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => y • ζ) ζ x := by
      simpa using (hasDerivAt_id x).smul_const ζ
    have h2 : HasDerivAt (fun y : ℝ => g (y • ζ)) (fderiv ℝ g (x • ζ) ζ) x :=
      (hgd (x • ζ)).hasFDerivAt.comp_hasDerivAt x h1
    exact h2.mul_const (kernel n ζ)

/-- **The trace of the real Hessian** in any real orthonormal basis of `ℂⁿ` is `4 ∑ₘ g_{m m̄}`. -/
theorem sum_hessian_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) {g : ComplexModel n → ℝ} {y : ComplexModel n}
    (hg : ContDiffAt ℝ 2 g y) :
    ∑ i, fderiv ℝ (fderiv ℝ g) y (b i) (b i) = 4 * levTr g y := by
  have h := KahlerLaplacianChart.re_trace_mul_complexHessian b 1 g y
  rw [one_mul, re_trace_complexHessian hg, Matrix.map_one _ (map_zero _) (map_one _),
    KahlerLaplacianChart.matCLM_one] at h
  rw [h, EllipticMeanValue.hessTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The gradient of `ζ ↦ χ₁(‖ζ‖²)` is `2 χ(‖ζ‖²) ζ`. -/
theorem hasFDerivAt_chiOne_normSq (ζ : ComplexModel n) :
    HasFDerivAt (fun ξ : ComplexModel n => chiOne n (‖ξ‖ ^ 2))
      (chi n (‖ζ‖ ^ 2) • (2 • innerSL ℝ ζ)) ζ :=
  (hasDerivAt_chiOne n _).comp_hasFDerivAt ζ (hasStrictFDerivAt_norm_sq ζ).hasFDerivAt

theorem fderiv_chiOne_normSq (ζ v : ComplexModel n) :
    fderiv ℝ (fun ξ : ComplexModel n => chiOne n (‖ξ‖ ^ 2)) ζ v =
      2 * chi n (‖ζ‖ ^ 2) * ⟪ζ, v⟫_ℝ := by
  rw [(hasFDerivAt_chiOne_normSq ζ).fderiv]
  simp
  ring

theorem hasCompactSupport_chiOne_normSq :
    HasCompactSupport fun ξ : ComplexModel n => chiOne n (‖ξ‖ ^ 2) := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) 1) fun ζ hζ => ?_
  simp only [mem_closedBall, dist_zero_right, not_le] at hζ
  exact chiOne_eq_zero_of_le n (by nlinarith)

/-- **The radial slope formula** (FPT `eq:chern-radial-derivative`): for a `C²` function `g`,
`r · ∫ Dg(rζ)(ζ) χ(‖ζ‖²) dζ = 2 r² ∫ (∑ₘ g_{m m̄})(r ζ) (-χ₁(‖ζ‖²)) dζ`. -/
theorem slope_integral_eq {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    r * ∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ =
      2 * r ^ 2 * ∫ ζ, levTr g (r • ζ) * -chiOne n (‖ζ‖ ^ 2) := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  set Φ : ComplexModel n → ℝ := fun ξ => chiOne n (‖ξ‖ ^ 2) with hΦ
  have hΦd : Differentiable ℝ Φ := fun ζ => (hasFDerivAt_chiOne_normSq ζ).differentiableAt
  have hΦc : Continuous Φ := hΦd.continuous
  have hΦs : HasCompactSupport Φ := hasCompactSupport_chiOne_normSq
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  set b := stdOrthonormalBasis ℝ (ComplexModel n) with hb
  have hΦ1 : ContDiff ℝ 1 Φ :=
    (contDiff_chiOne n).of_le (by norm_num) |>.comp (contDiff_norm_sq ℝ)
  have hΦ'c : Continuous (fderiv ℝ Φ) := hΦ1.continuous_fderiv (by norm_num)
  have hΦ's : ∀ v, HasCompactSupport fun ζ => fderiv ℝ Φ ζ v := fun v =>
    hΦs.fderiv (𝕜 := ℝ) |>.comp_left (g := fun L : ComplexModel n →L[ℝ] ℝ => L v) (by simp)
  -- the factors `fᵢ(ζ) = r Dg(rζ)(bᵢ) = D(g(r·))(ζ)(bᵢ)` and their derivatives
  have hfi : ∀ v ζ : ComplexModel n, ∃ L : ComplexModel n →L[ℝ] ℝ,
      HasFDerivAt (fun ξ => r * fderiv ℝ g (r • ξ) v) L ζ ∧
        L v = r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) v v := by
    intro v ζ
    have h1 : HasFDerivAt (fun ξ : ComplexModel n => r • ξ)
        (r • ContinuousLinearMap.id ℝ (ComplexModel n)) ζ := (hasFDerivAt_id ζ).const_smul r
    have h2 := ((hDd (r • ζ)).hasFDerivAt.comp ζ h1).clm_apply (hasFDerivAt_const v ζ)
    refine ⟨_, h2.const_mul r, ?_⟩
    simp
    ring
  have hfi_val : ∀ (v ζ : ComplexModel n),
      fderiv ℝ (fun ξ => r * fderiv ℝ g (r • ξ) v) ζ v =
        r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) v v := by
    intro v ζ
    obtain ⟨L, hL, hLv⟩ := hfi v ζ
    rw [hL.fderiv, hLv]
  have hfc : ∀ v : ComplexModel n, Continuous fun ξ => r * fderiv ℝ g (r • ξ) v := fun v =>
    continuous_const.mul ((hDc.comp (continuous_const_smul r)).clm_apply continuous_const)
  have hf'c : ∀ v : ComplexModel n,
      Continuous fun ζ => fderiv ℝ (fun ξ => r * fderiv ℝ g (r • ξ) v) ζ v := by
    intro v
    simp_rw [hfi_val v]
    exact continuous_const.mul
      (((hD2c.comp (continuous_const_smul r)).clm_apply continuous_const).clm_apply
        continuous_const)
  -- integration by parts in the direction `bᵢ`
  have hibp : ∀ v : ComplexModel n,
      ∫ ζ, (r * fderiv ℝ g (r • ζ) v) * fderiv ℝ Φ ζ v =
        -∫ ζ, r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) v v * Φ ζ := by
    intro v
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun ξ => r * fderiv ℝ g (r • ξ) v)
      (g := Φ) (v := v)]
    · simp_rw [hfi_val v]
    · exact ((hf'c v).mul hΦc).integrable_of_hasCompactSupport hΦs.mul_left
    · exact ((hfc v).mul (hΦ'c.clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hΦ's v).mul_left
    · exact ((hfc v).mul hΦc).integrable_of_hasCompactSupport hΦs.mul_left
    · exact fun x _ => (hfi v x).choose_spec.1.differentiableAt
    · exact fun x _ => hΦd x
  -- the pointwise identity `r Dg(rζ)(ζ) χ(‖ζ‖²) = ½ ∑ᵢ fᵢ(ζ) ∂_{bᵢ}χ₁(‖ζ‖²)`
  have hpt : ∀ ζ : ComplexModel n, r * (fderiv ℝ g (r • ζ) ζ * kernel n ζ) =
      (1 / 2 : ℝ) * ∑ i, (r * fderiv ℝ g (r • ζ) (b i)) * fderiv ℝ Φ ζ (b i) := by
    intro ζ
    have hrep : fderiv ℝ g (r • ζ) ζ = ∑ i, ⟪b i, ζ⟫_ℝ * fderiv ℝ g (r • ζ) (b i) := by
      have h := congrArg (fderiv ℝ g (r • ζ)) (b.sum_repr' ζ)
      rw [map_sum] at h
      simp only [map_smul, smul_eq_mul] at h
      exact h.symm
    simp only [hΦ, fderiv_chiOne_normSq, kernel, hrep, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
    ring
  have hint : ∀ i, Integrable fun ζ => (r * fderiv ℝ g (r • ζ) (b i)) * fderiv ℝ Φ ζ (b i) :=
    fun i => ((hfc (b i)).mul (hΦ'c.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hΦ's (b i)).mul_left
  have hint2 : ∀ i, Integrable fun ζ => r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) (b i) (b i) * Φ ζ :=
    fun i => ((continuous_const.mul
      (((hD2c.comp (continuous_const_smul r)).clm_apply continuous_const).clm_apply
        continuous_const)).mul hΦc).integrable_of_hasCompactSupport hΦs.mul_left
  calc r * ∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ
      = ∫ ζ, r * (fderiv ℝ g (r • ζ) ζ * kernel n ζ) := (integral_const_mul _ _).symm
    _ = ∫ ζ, (1 / 2 : ℝ) * ∑ i, (r * fderiv ℝ g (r • ζ) (b i)) * fderiv ℝ Φ ζ (b i) := by
        simp_rw [hpt]
    _ = (1 / 2 : ℝ) * ∑ i, ∫ ζ, (r * fderiv ℝ g (r • ζ) (b i)) * fderiv ℝ Φ ζ (b i) := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    _ = (1 / 2 : ℝ) * ∑ i, -∫ ζ, r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) (b i) (b i) * Φ ζ := by
        simp_rw [hibp]
    _ = -(1 / 2 : ℝ) * r ^ 2 * ∫ ζ, (∑ i, fderiv ℝ (fderiv ℝ g) (r • ζ) (b i) (b i)) * Φ ζ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i]
        rw [show (-(1 / 2 : ℝ)) * r ^ 2 = (1 / 2 : ℝ) * (-(r ^ 2)) by ring, mul_assoc,
          ← integral_const_mul]
        congr 1
        rw [← integral_neg]
        congr 1
        funext ζ
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 2 * r ^ 2 * ∫ ζ, levTr g (r • ζ) * -chiOne n (‖ζ‖ ^ 2) := by
        have h4 : ∀ ζ : ComplexModel n, (∑ i, fderiv ℝ (fderiv ℝ g) (r • ζ) (b i) (b i)) * Φ ζ =
            -4 * (levTr g (r • ζ) * -chiOne n (‖ζ‖ ^ 2)) := by
          intro ζ
          rw [sum_hessian_orthonormalBasis b (hg.contDiffAt)]
          simp only [hΦ]
          ring
        simp_rw [h4]
        rw [integral_const_mul]
        ring

/-- **The radial slope** (FPT `eq:chern-radial-derivative`):
`r Φ_g'(r) = 2 r² ∫ (∑ₘ g_{m m̄})(r ζ) (-χ₁(‖ζ‖²)) dζ` for `C²` functions `g`. -/
theorem radialMean_slope {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    r * deriv (radialMean g) r = 2 * r ^ 2 * ∫ ζ, levTr g (r • ζ) * -chiOne n (‖ζ‖ ^ 2) := by
  rw [(hasDerivAt_radialMean (hg.of_le (by norm_num)) r).deriv]
  exact slope_integral_eq hg r

end SGPT.NPP.DN3
