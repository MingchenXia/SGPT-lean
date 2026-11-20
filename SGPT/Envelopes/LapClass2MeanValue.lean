import SGPT.Analysis.CZContact

/-!
# A mean-value estimate for nearly flat elliptic operators

Lane LAP-CLASS2 (`claude-lap-class2`, node `lap-class2:mean-value`).  The analytic core of the
variable-coefficient second-order contact theorem (book `lma:DNTroof`, first assertion, for
obstacles with bounded metric Laplacian; FPT `prop:metric-laplacian-regular-contact-density`
replaced by mean-value inequalities, no Calderón–Zygmund theory).

In Kähler normal coordinates `ζ` centred at a point, the metric Laplacian of a Kähler form is
`Re tr(G(ζ) ∂∂̄)` with `G(ζ) = 1 + O(|ζ|²)`, and the volume density is a positive continuous `s`.
Here: let `w ≥ 0`, `s` be continuous on `B(0, r₀) ⊆ ℂⁿ` with `w ≤ B`, `s ≤ s₊`, let `G` satisfy
`|G(ζ) - 1|_{jk} ≤ C_G |ζ|²`, and assume the distributional bound

  `|∫ w s Re tr(G ∂∂̄ψ)| ≤ M ∫ s |ψ|` for smooth `ψ` with compact support in `B(0, r₀)`.

Then (`abs_integral_scaledKernel_sub_le`) for `0 < R < r₀`

  `|∫ w s k_R - w(0) s(0)| ≤ C₃ R²`,

with `k_R(ζ) = R^{-2n} K(ζ/R)` the dilates of TN's explicit radial probability kernel `K` and
`C₃` depending only on `n, B, s₊, C_G, M`.

## Proof

`Φ₁` (TN's `explicitRadialPoissonPotential 1 _ 0 1`) is smooth, nonnegative, supported in the unit
ball and `4 ∑ⱼ ∂ⱼ∂̄ⱼ Φ₁ = K - K₂`, `K₂(ζ) = 2^{2n} K(2ζ)`.  Its dilates
`Φ_R(ζ) = R^{2 - 2n} Φ₁(ζ/R)` satisfy `4 ∑ⱼ ∂ⱼ∂̄ⱼ Φ_R = k_R - k_{R/2}`, `Φ_R = O(R^{2-2n})` and
`∂∂̄Φ_R = O(R^{-2n})`, all supported in `B̄(0, R)`.  Testing the hypothesis against `Φ_R` and
splitting `G = 1 + (G - 1)`, the error term is `O(B s₊ C_G R² · R^{-2n} · R^{2n})`, so
`|∫ w s k_R - ∫ w s k_{R/2}| ≤ C₄ R²`.  Summing over the dyadic scales `R 2^{-j}` and letting
`j → ∞` (the kernels concentrate at `0` and `w s` is continuous) gives the estimate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.RadialLeviPreimage

variable {n : ℕ}

/-! ### Scaling of second derivatives -/

/-- Second derivatives of `ζ ↦ c u(R⁻¹ ζ)`. -/
theorem realHessian_scale {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u) (c R : ℝ)
    (z a b : ComplexModel n) :
    realHessian (fun ζ => c * u (R⁻¹ • ζ)) z a b = c * (R⁻¹ * R⁻¹) * realHessian u (R⁻¹ • z) a b := by
  set A : ComplexModel n →L[ℝ] ComplexModel n := R⁻¹ • ContinuousLinearMap.id ℝ _ with hA
  have hfun : (fun ζ => c * u (R⁻¹ • ζ)) = c • fun ζ => u (0 + A ζ) := by
    funext ζ
    simp [hA]
  have hcd : ContDiff ℝ 2 (fun ζ : ComplexModel n => u (0 + A ζ)) :=
    hu.comp (contDiff_const.add A.contDiff)
  rw [hfun, realHessian_smul hcd.contDiffAt, realHessian_comp_affine hu A 0 z a b]
  simp only [hA, smul_apply, ContinuousLinearMap.id_apply, zero_add,
    realHessian_smul_left, realHessian_smul_right]
  ring

/-- Entries of the complex Hessian of `ζ ↦ c u(R⁻¹ ζ)`. -/
theorem complexHessian_scale {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u) (c R : ℝ)
    (z : ComplexModel n) (j k : Fin n) :
    complexHessian (fun ζ => c * u (R⁻¹ • ζ)) z j k =
      ((c * (R⁻¹ * R⁻¹) : ℝ) : ℂ) * complexHessian u (R⁻¹ • z) j k := by
  simp only [complexHessian, realHessian_scale hu]
  push_cast
  ring

/-- The coordinate Levi trace of `ζ ↦ c u(R⁻¹ ζ)`. -/
theorem coordinateLeviTrace_scale {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u) (c R : ℝ)
    (z : ComplexModel n) :
    coordinateLeviTrace (fun ζ => c * u (R⁻¹ • ζ)) z =
      c * (R⁻¹ * R⁻¹) * coordinateLeviTrace u (R⁻¹ • z) := by
  simp only [coordinateLeviTrace, leviForm, realHessian_scale hu, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The real part of the trace of the complex Hessian is the coordinate Levi trace. -/
theorem re_trace_complexHessian_eq_coordinateLeviTrace (u : ComplexModel n → ℝ) (z : ComplexModel n) :
    (complexHessian u z).trace.re = coordinateLeviTrace u z := by
  simp only [Matrix.trace, Matrix.diag, complexHessian, coordinateLeviTrace, leviForm,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.add_re, Complex.mul_re]

/-! ### The dilated kernels and potentials -/

/-- The dilate `k_R(ζ) = R^{-d} K(R⁻¹ ζ)` of TN's explicit radial probability kernel
`K = explicitRadialKernel 1 _ 0` (supported in the unit ball, `d = 2n` the real dimension). -/
def scaledKernel (n : ℕ) (R : ℝ) (ζ : ComplexModel n) : ℝ :=
  (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * explicitRadialKernel 1 one_pos 0 (R⁻¹ • ζ)

/-- The dilate `Φ_R(ζ) = R^{2-d} Φ₁(R⁻¹ ζ)` of TN's radial Poisson potential
`Φ₁ = explicitRadialPoissonPotential 1 _ 0 1`. -/
def scaledPotential (n : ℕ) (R : ℝ) (ζ : ComplexModel n) : ℝ :=
  R ^ 2 * (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
    explicitRadialPoissonPotential 1 one_pos 0 1 (R⁻¹ • ζ)

theorem scaledKernel_nonneg (R : ℝ) (hR : 0 < R) (ζ : ComplexModel n) :
    0 ≤ scaledKernel n R ζ :=
  mul_nonneg (by positivity) (explicitRadialKernel_nonneg _ _ _ _)

theorem continuous_scaledKernel (R : ℝ) : Continuous (scaledKernel n R) :=
  continuous_const.mul ((explicitRadialKernel_contDiff 1 one_pos 0).continuous.comp
    (continuous_const_smul _))

theorem integral_scaledKernel (R : ℝ) (hR : 0 < R) :
    ∫ ζ, scaledKernel n R ζ = 1 := by
  simp only [scaledKernel]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ hR.le,
    explicitRadialKernel_integral_one, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by positivity)

theorem scaledKernel_eq_zero_of_lt (R : ℝ) (hR : 0 < R) {ζ : ComplexModel n} (hζ : R < ‖ζ‖) :
    scaledKernel n R ζ = 0 := by
  have h : R⁻¹ • ζ ∉ tsupport (explicitRadialKernel (n := n) 1 one_pos 0) := by
    rw [explicitRadialKernel_tsupport, mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    push Not
    rw [Nat.cast_zero, zero_add, div_one, lt_inv_mul_iff₀ hR, mul_one]
    exact hζ
  rw [scaledKernel, image_eq_zero_of_notMem_tsupport h, mul_zero]

/-- The volume of the unit ball. -/
abbrev unitBallVol (n : ℕ) : ℝ := volume.real (closedBall (0 : ComplexModel n) 1)

theorem unitBallVol_pos : 0 < unitBallVol n := by
  simp only [unitBallVol, measureReal_def]
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne'
    measure_closedBall_lt_top.ne

/-- `k_R ≤ 2^d R^{-d} / vol B̄(0,1)`. -/
theorem scaledKernel_le (R : ℝ) (hR : 0 < R) (ζ : ComplexModel n) :
    scaledKernel n R ζ ≤
      (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
        (2 ^ Module.finrank ℝ (ComplexModel n) / unitBallVol n) := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := explicitRadialKernel_le_div_measure_closedBall (n := n) 1 one_pos 0 (R⁻¹ • ζ)
  have hr : (shrinkingBump (E := ComplexModel n) 1 one_pos 0).rOut = 1 := by
    simp [shrinkingBump]
  rwa [hr] at h

/-- `k_R ≥ R^{-d} / vol B̄(0,1)` on `B̄(0, R/2)`. -/
theorem le_scaledKernel (R : ℝ) (hR : 0 < R) {ζ : ComplexModel n} (hζ : ‖ζ‖ ≤ R / 2) :
    (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * (unitBallVol n)⁻¹ ≤ scaledKernel n R ζ := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hrIn : (shrinkingBump (E := ComplexModel n) 1 one_pos 0).rIn = 1 / 2 := by
    simp [shrinkingBump]
  have hmem : R⁻¹ • ζ ∈ closedBall (0 : ComplexModel n)
      (shrinkingBump (E := ComplexModel n) 1 one_pos 0).rIn := by
    rw [hrIn, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR, inv_mul_le_iff₀ hR]
    linarith
  rw [explicitRadialKernel, explicitRadialRaw_eq_one_of_mem_closedBall 1 one_pos 0 _ hmem,
    one_div]
  refine inv_anti₀ (explicitRadialRaw_integral_pos 1 one_pos 0) ?_
  calc ∫ y : ComplexModel n, explicitRadialRaw 1 one_pos 0 y
      = ∫ y in closedBall (0 : ComplexModel n) 1, explicitRadialRaw 1 one_pos 0 y := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
        have : y ∉ Function.support (explicitRadialRaw (n := n) 1 one_pos 0) := by
          rw [explicitRadialRaw_support]
          intro hy'
          exact hy (ball_subset_closedBall (by simpa using hy'))
        simpa using this
    _ ≤ ∫ _y in closedBall (0 : ComplexModel n) 1, (1 : ℝ) :=
        setIntegral_mono_on (explicitRadialRaw_integrable 1 one_pos 0).integrableOn
          (integrableOn_const measure_closedBall_lt_top.ne) measurableSet_closedBall
          fun y _ => explicitRadialRaw_le_one 1 one_pos 0 y
    _ = unitBallVol n := by simp [unitBallVol]

/-- The half-scale kernel is TN's second kernel, dilated. -/
theorem scaledKernel_half (R : ℝ) (hR : 0 < R) (ζ : ComplexModel n) :
    scaledKernel n (R / 2) ζ =
      (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * explicitRadialKernel 1 one_pos 1 (R⁻¹ • ζ) := by
  rw [explicitRadialKernel_scale 1 one_pos 0 1, scaledKernel]
  norm_num
  rw [smul_smul, div_pow, inv_div]
  have h2 : (2 : ℝ) * R⁻¹ = (R / 2)⁻¹ := by rw [inv_div]; field_simp
  rw [h2]
  field_simp

variable (hn : 0 < n)
include hn

theorem contDiff_scaledPotential (R : ℝ) : ContDiff ℝ ∞ (scaledPotential n R) :=
  contDiff_const.mul ((explicitRadialPoissonPotential_contDiff hn 1 one_pos 0 1).comp
    (contDiff_const_smul _))

theorem scaledPotential_nonneg (R : ℝ) (hR : 0 < R) (ζ : ComplexModel n) :
    0 ≤ scaledPotential n R ζ :=
  mul_nonneg (mul_nonneg (sq_nonneg R) (by positivity))
    (explicitRadialPoissonPotential_nonneg hn 1 one_pos (Nat.zero_le 1) _)

theorem scaledPotential_eq_zero_of_le (R : ℝ) (hR : 0 < R) {ζ : ComplexModel n}
    (hζ : R ≤ ‖ζ‖) : scaledPotential n R ζ = 0 := by
  rw [scaledPotential, explicitRadialPoissonPotential_eq_zero_of_outer hn 1 one_pos
    (Nat.zero_le 1), mul_zero]
  rw [Nat.cast_zero, zero_add, div_one, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
    le_inv_mul_iff₀ hR, mul_one]
  exact hζ

theorem tsupport_scaledPotential_subset (R : ℝ) (hR : 0 < R) :
    tsupport (scaledPotential n R) ⊆ closedBall 0 R :=
  closure_minimal (fun ζ hζ => by
    by_contra h
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact hζ (scaledPotential_eq_zero_of_le hn R hR h.le)) isClosed_closedBall

theorem hasCompactSupport_scaledPotential (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (scaledPotential n R) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_scaledPotential_subset hn R hR)

/-- **`4 ∑ⱼ ∂ⱼ∂̄ⱼ Φ_R = k_R - k_{R/2}`.** -/
theorem four_mul_coordinateLeviTrace_scaledPotential (R : ℝ) (hR : 0 < R) (ζ : ComplexModel n) :
    4 * coordinateLeviTrace (scaledPotential n R) ζ =
      scaledKernel n R ζ - scaledKernel n (R / 2) ζ := by
  have hu : ContDiff ℝ 2 (explicitRadialPoissonPotential (n := n) 1 one_pos 0 1) :=
    (explicitRadialPoissonPotential_contDiff hn 1 one_pos 0 1).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h := four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_eq_kernel_sub hn 1
    one_pos 0 1 (R⁻¹ • ζ)
  have hfun : scaledPotential n R = fun ζ => (R ^ 2 * (R ^ Module.finrank ℝ (ComplexModel n))⁻¹) *
      explicitRadialPoissonPotential 1 one_pos 0 1 (R⁻¹ • ζ) := rfl
  rw [hfun, coordinateLeviTrace_scale hu, scaledKernel_half R hR, scaledKernel]
  have hRR : R ^ 2 * (R⁻¹ * R⁻¹) = 1 := by field_simp
  calc 4 * (R ^ 2 * (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * (R⁻¹ * R⁻¹) *
        coordinateLeviTrace (explicitRadialPoissonPotential 1 one_pos 0 1) (R⁻¹ • ζ))
      = (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * (R ^ 2 * (R⁻¹ * R⁻¹)) *
          (4 * coordinateLeviTrace (explicitRadialPoissonPotential 1 one_pos 0 1) (R⁻¹ • ζ)) := by
        ring
    _ = _ := by rw [hRR, h]; ring

/-- Uniform bounds for `Φ₁` and its complex Hessian. -/
theorem exists_potential_bounds :
    ∃ P₁ H₁ : ℝ, 0 ≤ P₁ ∧ 0 ≤ H₁ ∧
      (∀ x, explicitRadialPoissonPotential (n := n) 1 one_pos 0 1 x ≤ P₁) ∧
      ∀ x j k, ‖complexHessian (explicitRadialPoissonPotential (n := n) 1 one_pos 0 1) x j k‖ ≤
        H₁ := by
  set Φ₁ := explicitRadialPoissonPotential (n := n) 1 one_pos 0 1 with hΦ₁
  have hΦ : ContDiff ℝ ∞ Φ₁ := explicitRadialPoissonPotential_contDiff hn 1 one_pos 0 1
  have hΦ2 : ContDiff ℝ 2 Φ₁ := hΦ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hc : HasCompactSupport Φ₁ :=
    explicitRadialPoissonPotential_hasCompactSupport hn 1 one_pos (Nat.zero_le 1)
  obtain ⟨P₁, hP₁⟩ := hc.exists_bound_of_continuous hΦ.continuous
  have hent : ∀ j k : Fin n, ∃ C, ∀ x, ‖complexHessian Φ₁ x j k‖ ≤ C := by
    intro j k
    refine HasCompactSupport.exists_bound_of_continuous ?_ ?_
    · refine hc.mono' fun x hx => ?_
      by_contra h
      have h0 := MixedHessian.complexHessian_eq_zero_of_notMem_tsupport h
      exact hx (by simp [h0])
    · simp only [complexHessian]
      have h1 := continuous_realHessian hΦ2 (coordinateVector j) (coordinateVector k)
      have h2 := continuous_realHessian hΦ2 (Complex.I • coordinateVector j)
        (Complex.I • coordinateVector k)
      have h3 := continuous_realHessian hΦ2 (coordinateVector j) (Complex.I • coordinateVector k)
      have h4 := continuous_realHessian hΦ2 (Complex.I • coordinateVector j) (coordinateVector k)
      exact ((Complex.continuous_ofReal.comp (h1.add h2)).div_const 4).add
        ((continuous_const.mul (Complex.continuous_ofReal.comp (h3.sub h4))).div_const 4)
  choose C hC using hent
  refine ⟨max P₁ 0, ∑ j, ∑ k, |C j k|, le_max_right _ _, by positivity, fun x => ?_,
    fun x j k => ?_⟩
  · exact (le_abs_self _).trans ((hP₁ x).trans (le_max_left _ _))
  · refine (hC j k x).trans ((le_abs_self _).trans ?_)
    refine (Finset.single_le_sum (f := fun k => |C j k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ k, |C j k|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)

omit hn in
/-- A function continuous on `B(0, r₀)` and vanishing outside `B̄(0, R)`, `R < r₀`, is integrable. -/
theorem integrable_of_continuousOn_ball {f : ComplexModel n → ℝ} {r₀ R : ℝ}
    (hf : ContinuousOn f (ball 0 r₀)) (hR : R < r₀) (h0 : ∀ ζ, R < ‖ζ‖ → f ζ = 0) :
    Integrable f := by
  refine ((hf.mono (closedBall_subset_ball hR)).integrableOn_compact
    (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero fun ζ hζ => h0 ζ ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hζ
  exact hζ

omit hn in
/-- `|Re tr(A K)| ≤ ∑ⱼₖ |A_{jk}| |K_{kj}|`. -/
theorem abs_re_trace_mul_le (A K : Matrix (Fin n) (Fin n) ℂ) :
    |(A * K).trace.re| ≤ ∑ j, ∑ k, ‖A j k‖ * ‖K k j‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_)
  exact Finset.sum_le_sum fun k _ => (norm_mul _ _).le

/-- **The mean-value estimate for nearly flat operators.**  Let `w ≥ 0` and `s ≥ 0` be continuous
on `B(0, r₀)` with `w ≤ B`, `s ≤ s₊`, let `G` be continuous on `B(0, r₀)` with
`|(G(ζ) - 1)_{jk}| ≤ C_G |ζ|²`, and assume `|∫ w s Re tr(G ∂∂̄ψ)| ≤ M ∫ s |ψ|` for all smooth `ψ`
with compact support in `B(0, r₀)`.  Then `|∫ w s k_R - w(0) s(0)| ≤ C₃ R²` for `0 < R < r₀`. -/
theorem abs_integral_scaledKernel_sub_le {M B sp CG : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hsp0 : 0 ≤ sp) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ {r₀ : ℝ} {w s : ComplexModel n → ℝ}
      {G : ComplexModel n → Matrix (Fin n) (Fin n) ℂ},
      ContinuousOn w (ball 0 r₀) → ContinuousOn s (ball 0 r₀) → ContinuousOn G (ball 0 r₀) →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₀, 0 ≤ w ζ) →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₀, w ζ ≤ B) →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₀, 0 ≤ s ζ) →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₀, s ζ ≤ sp) →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₀, ∀ j k, ‖(G ζ - 1) j k‖ ≤ CG * ‖ζ‖ ^ 2) →
      (∀ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball 0 r₀ →
        |∫ ζ, w ζ * s ζ * (G ζ * complexHessian ψ ζ).trace.re| ≤ M * ∫ ζ, s ζ * |ψ ζ|) →
      ∀ R : ℝ, 0 < R → R < r₀ →
        |(∫ ζ, w ζ * s ζ * scaledKernel n R ζ) - w 0 * s 0| ≤ C₃ * R ^ 2 := by
  obtain ⟨P₁, H₁, hP₁0, hH₁0, hP₁, hH₁⟩ := exists_potential_bounds (n := n) hn
  set d := Module.finrank ℝ (ComplexModel n) with hd
  set vb : ℝ := volume.real (ball (0 : ComplexModel n) 1) with hvb
  have hvb0 : 0 ≤ vb := measureReal_nonneg
  set CG' : ℝ := max CG 0 with hCG'
  have hCG'0 : 0 ≤ CG' := le_max_right _ _
  set C₄ : ℝ := 4 * (M * sp * P₁ * vb + B * sp * ((n : ℝ) * n * CG') * H₁ * vb) with hC₄
  have hC₄0 : 0 ≤ C₄ := by positivity
  refine ⟨4 / 3 * C₄, by positivity, fun {r₀ w s G} hw hs hGc hw0 hwB hs0 hsp hG hP => ?_⟩
  have hvol : ∀ R : ℝ, 0 ≤ R → volume.real (closedBall (0 : ComplexModel n) R) = R ^ d * vb :=
    fun R hR => SGPT.Analysis.CZ.volume_real_closedBall_eq 0 hR
  set F : ComplexModel n → ℝ := fun ζ => w ζ * s ζ with hFdef
  have hF : ContinuousOn F (ball 0 r₀) := hw.mul hs
  -- trivial case: the ball is empty
  rcases le_or_gt r₀ 0 with hr₀ | hr₀
  · exact fun R hR hRr => absurd (hR.trans hRr) (not_lt.mpr hr₀)
  have h0ball : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) r₀ := mem_ball_self hr₀
  -- integrals of functions bounded by a constant on `B̄(0, R)`
  have hbound : ∀ (f : ComplexModel n → ℝ) (R c : ℝ), 0 ≤ R → 0 ≤ c → Integrable f →
      (∀ ζ, R < ‖ζ‖ → f ζ = 0) → (∀ ζ, ‖ζ‖ ≤ R → |f ζ| ≤ c) → |∫ ζ, f ζ| ≤ c * (R ^ d * vb) := by
    intro f R c hR hc hfi hf0 hfc
    have hle : ∀ ζ, |f ζ| ≤ (closedBall (0 : ComplexModel n) R).indicator (fun _ => c) ζ := by
      intro ζ
      by_cases hζ : ‖ζ‖ ≤ R
      · rw [indicator_of_mem (by simpa using hζ)]
        exact hfc ζ hζ
      · rw [indicator_of_notMem (by simpa using hζ), hf0 ζ (lt_of_not_ge hζ), abs_zero]
    calc |∫ ζ, f ζ| ≤ ∫ ζ, |f ζ| := abs_integral_le_integral_abs
      _ ≤ ∫ ζ, (closedBall (0 : ComplexModel n) R).indicator (fun _ => c) ζ :=
          integral_mono hfi.abs ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
            measurableSet_closedBall) hle
      _ = c * (R ^ d * vb) := by
          rw [integral_indicator_const _ measurableSet_closedBall, hvol R hR, smul_eq_mul]
          ring
  -- Step 1: one dyadic step
  have hstep : ∀ R : ℝ, 0 < R → R < r₀ →
      |(∫ ζ, F ζ * scaledKernel n R ζ) - ∫ ζ, F ζ * scaledKernel n (R / 2) ζ| ≤ C₄ * R ^ 2 := by
    intro R hR hRr
    set Φ := scaledPotential n R with hΦdef
    have hΦs : ContDiff ℝ ∞ Φ := contDiff_scaledPotential hn R
    have hΦ2 : ContDiff ℝ 2 Φ := hΦs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hΦc : HasCompactSupport Φ := hasCompactSupport_scaledPotential hn R hR
    have hΦt : tsupport Φ ⊆ closedBall 0 R := tsupport_scaledPotential_subset hn R hR
    have hΦ0 : ∀ ζ, R ≤ ‖ζ‖ → Φ ζ = 0 := fun ζ hζ => scaledPotential_eq_zero_of_le hn R hR hζ
    have hΦnn : ∀ ζ, 0 ≤ Φ ζ := fun ζ => scaledPotential_nonneg hn R hR ζ
    have hout : ∀ ζ : ComplexModel n, R < ‖ζ‖ → ζ ∉ tsupport Φ := fun ζ hζ h => by
      have := hΦt h
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have hI := hP Φ hΦs hΦc (hΦt.trans (closedBall_subset_ball hRr))
    -- the right side
    have hrhs : M * ∫ ζ, s ζ * |Φ ζ| ≤ M * (sp * (R ^ 2 * (R ^ d)⁻¹ * P₁) * (R ^ d * vb)) := by
      refine mul_le_mul_of_nonneg_left ?_ hM
      have hint : Integrable fun ζ => s ζ * |Φ ζ| :=
        integrable_of_continuousOn_ball (hs.mul hΦs.continuous.abs.continuousOn) hRr
          fun ζ hζ => by rw [hΦ0 ζ hζ.le, abs_zero, mul_zero]
      refine (le_abs_self _).trans (hbound _ R _ hR.le (by positivity) hint
        (fun ζ hζ => by rw [hΦ0 ζ hζ.le, abs_zero, mul_zero])
        fun ζ hζ => ?_)
      have hζb : ζ ∈ ball (0 : ComplexModel n) r₀ := by
        rw [mem_ball, dist_zero_right]; linarith
      rw [abs_mul, abs_abs, abs_of_nonneg (hs0 ζ hζb)]
      refine mul_le_mul (hsp ζ hζb) ?_ (abs_nonneg _) hsp0
      rw [abs_of_nonneg (hΦnn ζ), hΦdef, scaledPotential]
      exact mul_le_mul_of_nonneg_left (hP₁ _) (by positivity)
    -- entries of the complex Hessian of `Φ`
    have hHess : ∀ ζ j k, ‖complexHessian Φ ζ j k‖ ≤ (R ^ d)⁻¹ * H₁ := by
      intro ζ j k
      have hfun : Φ = fun ζ => (R ^ 2 * (R ^ d)⁻¹) *
          explicitRadialPoissonPotential 1 one_pos 0 1 (R⁻¹ • ζ) := rfl
      have hu : ContDiff ℝ 2 (explicitRadialPoissonPotential (n := n) 1 one_pos 0 1) :=
        (explicitRadialPoissonPotential_contDiff hn 1 one_pos 0 1).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      rw [hfun, complexHessian_scale hu, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc : R ^ 2 * (R ^ d)⁻¹ * (R⁻¹ * R⁻¹) = (R ^ d)⁻¹ := by field_simp
      rw [hc, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hH₁ _ j k) (by positivity)
    -- decomposition of the left side
    set E : ComplexModel n → ℝ := fun ζ => F ζ * ((G ζ - 1) * complexHessian Φ ζ).trace.re
      with hEdef
    have hsplit : ∀ ζ, F ζ * (G ζ * complexHessian Φ ζ).trace.re =
        (F ζ * scaledKernel n R ζ - F ζ * scaledKernel n (R / 2) ζ) / 4 + E ζ := by
      intro ζ
      have h1 : G ζ * complexHessian Φ ζ =
          complexHessian Φ ζ + (G ζ - 1) * complexHessian Φ ζ := by
        rw [sub_mul, one_mul, add_sub_cancel]
      have h4 : 4 * coordinateLeviTrace Φ ζ = scaledKernel n R ζ - scaledKernel n (R / 2) ζ :=
        four_mul_coordinateLeviTrace_scaledPotential hn R hR ζ
      rw [h1, Matrix.trace_add, Complex.add_re, re_trace_complexHessian_eq_coordinateLeviTrace, hEdef]
      simp only
      rw [← mul_sub, ← h4]
      ring
    have hcontHess : ∀ j k, Continuous fun ζ => complexHessian Φ ζ j k := by
      intro j k
      simp only [complexHessian]
      have h1 := continuous_realHessian hΦ2 (coordinateVector j) (coordinateVector k)
      have h2 := continuous_realHessian hΦ2 (Complex.I • coordinateVector j)
        (Complex.I • coordinateVector k)
      have h3 := continuous_realHessian hΦ2 (coordinateVector j) (Complex.I • coordinateVector k)
      have h4 := continuous_realHessian hΦ2 (Complex.I • coordinateVector j) (coordinateVector k)
      exact ((Complex.continuous_ofReal.comp (h1.add h2)).div_const 4).add
        ((continuous_const.mul (Complex.continuous_ofReal.comp (h3.sub h4))).div_const 4)
    have hcontH : Continuous fun ζ => complexHessian Φ ζ :=
      continuous_pi fun j => continuous_pi fun k => hcontHess j k
    have hHess0 : ∀ ζ : ComplexModel n, R < ‖ζ‖ → complexHessian Φ ζ = 0 := fun ζ hζ =>
      MixedHessian.complexHessian_eq_zero_of_notMem_tsupport (hout ζ hζ)
    have hEint : Integrable E := by
      refine integrable_of_continuousOn_ball (hF.mul ?_) hRr fun ζ hζ => ?_
      · refine Complex.continuous_re.comp_continuousOn ?_
        refine (continuous_id.matrix_trace).comp_continuousOn ?_
        exact (hGc.sub continuousOn_const).mul hcontH.continuousOn
      · simp only [hEdef, hHess0 ζ hζ, Matrix.trace_zero, Complex.zero_re, mul_zero]
    have hk : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → Integrable fun ζ => F ζ * scaledKernel n ρ ζ := by
      intro ρ hρ hρR
      refine integrable_of_continuousOn_ball (hF.mul (continuous_scaledKernel ρ).continuousOn) hRr
        fun ζ hζ => ?_
      rw [scaledKernel_eq_zero_of_lt ρ hρ (by linarith), mul_zero]
    have hR2 : 0 < R / 2 := by positivity
    have hk1 := hk R hR le_rfl
    have hk2 := hk (R / 2) hR2 (by linarith)
    have hLeft : ∫ ζ, F ζ * (G ζ * complexHessian Φ ζ).trace.re =
        ((∫ ζ, F ζ * scaledKernel n R ζ) - ∫ ζ, F ζ * scaledKernel n (R / 2) ζ) / 4 +
          ∫ ζ, E ζ := by
      simp_rw [hsplit]
      rw [integral_add, integral_div, integral_sub hk1 hk2]
      · exact (hk1.sub hk2).div_const 4
      · exact hEint
    -- the error term
    have hEb : |∫ ζ, E ζ| ≤ B * sp * ((n : ℝ) * n * CG') * H₁ * R ^ 2 * vb := by
      have h := hbound E R ((B * sp) * ((n : ℝ) * n * CG' * R ^ 2 * ((R ^ d)⁻¹ * H₁))) hR.le
        (by positivity) hEint
        (fun ζ hζ => by simp only [hEdef, hHess0 ζ hζ, Matrix.trace_zero, Complex.zero_re,
          mul_zero])
        (fun ζ hζ => by
          have hζb : ζ ∈ ball (0 : ComplexModel n) r₀ := by
            rw [mem_ball, dist_zero_right]; linarith
          rw [hEdef, abs_mul]
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
          · rw [hFdef, abs_mul, abs_of_nonneg (hw0 ζ hζb), abs_of_nonneg (hs0 ζ hζb)]
            exact mul_le_mul (hwB ζ hζb) (hsp ζ hζb) (hs0 ζ hζb) hB
          · refine (abs_re_trace_mul_le _ _).trans ?_
            have hentry : ∀ j k, ‖(G ζ - 1) j k‖ * ‖complexHessian Φ ζ k j‖ ≤
                CG' * R ^ 2 * ((R ^ d)⁻¹ * H₁) := by
              intro j k
              refine mul_le_mul ?_ (hHess ζ k j) (norm_nonneg _) (by positivity)
              refine (hG ζ hζb j k).trans ?_
              exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (norm_nonneg _) hζ 2)
                (sq_nonneg _) hCG'0
            calc ∑ j, ∑ k, ‖(G ζ - 1) j k‖ * ‖complexHessian Φ ζ k j‖
                ≤ ∑ _j : Fin n, ∑ _k : Fin n, CG' * R ^ 2 * ((R ^ d)⁻¹ * H₁) :=
                  Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
              _ = (n : ℝ) * n * CG' * R ^ 2 * ((R ^ d)⁻¹ * H₁) := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  ring)
      have hc : (B * sp) * ((n : ℝ) * n * CG' * R ^ 2 * ((R ^ d)⁻¹ * H₁)) * (R ^ d * vb) =
          B * sp * ((n : ℝ) * n * CG') * H₁ * R ^ 2 * vb := by
        field_simp
      rwa [hc] at h
    have hrhs' : M * (sp * (R ^ 2 * (R ^ d)⁻¹ * P₁) * (R ^ d * vb)) = M * sp * P₁ * vb * R ^ 2 := by
      field_simp
    rw [hLeft] at hI
    rw [hrhs'] at hrhs
    have habs := abs_le.mp hI
    have hEabs := abs_le.mp hEb
    rw [abs_le]
    constructor <;> nlinarith [hrhs]
  -- Step 2: telescoping over the dyadic scales
  set ε : ℝ → ℕ → ℝ := fun R J => R * (1 / 2) ^ J with hεdef
  have hε0 : ∀ R, 0 < R → ∀ J, 0 < ε R J := fun R hR J => by positivity
  have hεle : ∀ R, 0 < R → ∀ J, ε R J ≤ R := fun R hR J => by
    simp only [hεdef]
    exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hεsucc : ∀ R J, ε R (J + 1) = ε R J / 2 := fun R J => by
    simp only [hεdef, pow_succ]; ring
  have htele : ∀ R : ℝ, 0 < R → R < r₀ → ∀ J : ℕ,
      |(∫ ζ, F ζ * scaledKernel n R ζ) - ∫ ζ, F ζ * scaledKernel n (ε R J) ζ| ≤
        4 / 3 * C₄ * R ^ 2 * (1 - (1 / 4) ^ J) := by
    intro R hR hRr J
    induction J with
    | zero => simp only [hεdef, pow_zero, mul_one, sub_self, abs_zero, mul_zero, le_refl]
    | succ J ih =>
      have h1 := hstep (ε R J) (hε0 R hR J) ((hεle R hR J).trans_lt hRr)
      rw [← hεsucc] at h1
      have hεsq : ε R J ^ 2 = R ^ 2 * (1 / 4) ^ J := by
        simp only [hεdef, mul_pow, ← pow_mul]
        rw [show (1 / 2 : ℝ) ^ (J * 2) = (1 / 4) ^ J by
          rw [mul_comm, pow_mul]; norm_num]
      rw [hεsq] at h1
      calc |(∫ ζ, F ζ * scaledKernel n R ζ) - ∫ ζ, F ζ * scaledKernel n (ε R (J + 1)) ζ|
          ≤ |(∫ ζ, F ζ * scaledKernel n R ζ) - ∫ ζ, F ζ * scaledKernel n (ε R J) ζ| +
            |(∫ ζ, F ζ * scaledKernel n (ε R J) ζ) -
              ∫ ζ, F ζ * scaledKernel n (ε R (J + 1)) ζ| := abs_sub_le _ _ _
        _ ≤ 4 / 3 * C₄ * R ^ 2 * (1 - (1 / 4) ^ J) + C₄ * (R ^ 2 * (1 / 4) ^ J) :=
            add_le_add ih h1
        _ = 4 / 3 * C₄ * R ^ 2 * (1 - (1 / 4) ^ (J + 1)) := by rw [pow_succ]; ring
  -- Step 3: the kernels concentrate at `0`
  have hlim : ∀ R : ℝ, 0 < R → R < r₀ →
      Tendsto (fun J => ∫ ζ, F ζ * scaledKernel n (ε R J) ζ) atTop (𝓝 (F 0)) := by
    intro R hR hRr
    rw [Metric.tendsto_atTop]
    intro η hη
    have hFc : ContinuousAt F 0 := hF.continuousAt (ball_mem_nhds 0 hr₀)
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hFc (η / 2) (half_pos hη)
    have hεt : Tendsto (ε R) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
      simpa [hεdef] using this
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hεt) δ hδ
    refine ⟨N, fun J hJ => ?_⟩
    have hεJ := hN J hJ
    rw [Real.dist_eq, sub_zero, abs_of_pos (hε0 R hR J)] at hεJ
    set ρ := ε R J with hρ
    have hρ0 : 0 < ρ := hε0 R hR J
    have hρr : ρ < r₀ := (hεle R hR J).trans_lt hRr
    have hkint : Integrable fun ζ => F ζ * scaledKernel n ρ ζ :=
      integrable_of_continuousOn_ball (hF.mul (continuous_scaledKernel ρ).continuousOn) hρr
        fun ζ hζ => by rw [scaledKernel_eq_zero_of_lt ρ hρ0 hζ, mul_zero]
    have hk1int : Integrable fun ζ => F 0 * scaledKernel n ρ ζ :=
      ((continuous_scaledKernel ρ).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) ρ) fun ζ hζ =>
          scaledKernel_eq_zero_of_lt ρ hρ0 (by simpa using hζ))).const_mul _
    have heq : (∫ ζ, F ζ * scaledKernel n ρ ζ) - F 0 =
        ∫ ζ, (F ζ - F 0) * scaledKernel n ρ ζ := by
      rw [show (fun ζ => (F ζ - F 0) * scaledKernel n ρ ζ) =
          fun ζ => F ζ * scaledKernel n ρ ζ - F 0 * scaledKernel n ρ ζ by funext ζ; ring,
        integral_sub hkint hk1int, integral_const_mul, integral_scaledKernel ρ hρ0, mul_one]
    rw [Real.dist_eq, heq]
    calc |∫ ζ, (F ζ - F 0) * scaledKernel n ρ ζ| ≤ ∫ ζ, η / 2 * scaledKernel n ρ ζ := by
          refine (abs_integral_le_integral_abs).trans (integral_mono (hkint.sub hk1int |>.congr
            (Eventually.of_forall fun ζ => by simp only [Pi.sub_apply]; ring)).abs
            ((continuous_scaledKernel ρ).integrable_of_hasCompactSupport
              (HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) ρ) fun ζ hζ =>
                scaledKernel_eq_zero_of_lt ρ hρ0 (by simpa using hζ)) |>.const_mul _)
            fun ζ => ?_)
          rw [abs_mul, abs_of_nonneg (scaledKernel_nonneg ρ hρ0 ζ)]
          by_cases hζ : ‖ζ‖ ≤ ρ
          · refine mul_le_mul_of_nonneg_right ?_ (scaledKernel_nonneg ρ hρ0 ζ)
            have := hδF (show dist ζ 0 < δ by rw [dist_zero_right]; linarith)
            rw [Real.dist_eq] at this
            exact this.le
          · rw [scaledKernel_eq_zero_of_lt ρ hρ0 (lt_of_not_ge hζ), mul_zero, mul_zero]
      _ = η / 2 := by rw [integral_const_mul, integral_scaledKernel ρ hρ0, mul_one]
      _ < η := half_lt_self hη
  intro R hR hRr
  have hlim' := (tendsto_const_nhds (x := ∫ ζ, F ζ * scaledKernel n R ζ)).sub (hlim R hR hRr)
  have habs := hlim'.abs
  refine le_of_tendsto' habs fun J => (htele R hR hRr J).trans ?_
  have h1 : 0 ≤ 4 / 3 * C₄ * R ^ 2 * (1 / 4 : ℝ) ^ J := by positivity
  linarith

end SGPT.Envelopes.LapClass
