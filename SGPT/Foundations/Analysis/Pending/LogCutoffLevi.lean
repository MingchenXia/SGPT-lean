import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

/-!
# Plurisubharmonic log cut-offs along a linear subspace

For a `ℂ`-linear map `Y : ℂᴺ → ℂᶜ` (in the application `Y(u, u') = u' - u`, whose kernel is the
diagonal in a product chart) the functions

`Vᵢ(z) = ρ(log ‖Y z‖² / (i + 1) + 1)`   (`Vᵢ = 0` where `Y z = 0`)    (`logCutoff`)

are smooth, vanish near `{Y = 0}`, take values in `[0, 1]` on `{‖Y z‖² < 1}`, tend to `1` off
`{Y = 0}`, and are plurisubharmonic on `{‖Y z‖² < 1}` (`smoothDDC_logCutoff_nonneg`).  Here
`ρ(t) = e² exp(-2/t)` for `t > 0` and `ρ = 0` on `(-∞, 0]` (`cutoffProfile`, from
`expNegInvGlue`): smooth, nondecreasing and convex on `(-∞, 1]`, `ρ(1) = 1`.  Plurisubharmonicity
is the chain rule for the Levi form (`leviForm_comp`:
`L(ρ ∘ u)(v) = ρ''(u) (du(v)² + du(iv)²)/4 + ρ'(u) L(u)(v)`) and `L(log ‖Y‖²) ≥ 0` off
`{Y = 0}` (`leviForm_log_normSq_nonneg`, the `s = 0`, `cⱼ = 1` case of Demailly--Păun's
estimate `ConcentrationPotentialLevi.le_leviForm_log_sum_of_pos`).

These are the cut-offs `v_k = χ(log |y|² / k)` of the Skoda--El Mir argument
(`demailly-cadg:III.2.3`, with `E = {y = 0}` complete pluripolar via `log |y|²`), TN.4 step B4.3,
the Skoda–El Mir extension argument.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.LogCutoffLevi

open FirstPass ConcentrationPotentialLevi

/-! ### The profile `ρ` -/

section Profile

/-- `ρ(t) = e² exp(-2/t)` for `t > 0`, `ρ(t) = 0` for `t ≤ 0`. -/
def cutoffProfile (t : ℝ) : ℝ := Real.exp 2 * expNegInvGlue (t / 2)

theorem contDiff_cutoffProfile : ContDiff ℝ ∞ cutoffProfile :=
  contDiff_const.mul ((expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_id.div_const 2))

theorem continuous_cutoffProfile : Continuous cutoffProfile := contDiff_cutoffProfile.continuous

theorem cutoffProfile_of_nonpos {t : ℝ} (ht : t ≤ 0) : cutoffProfile t = 0 := by
  rw [cutoffProfile, expNegInvGlue.zero_of_nonpos (by linarith), mul_zero]

theorem cutoffProfile_of_pos {t : ℝ} (ht : 0 < t) :
    cutoffProfile t = Real.exp (2 - 2 * t⁻¹) := by
  have h2 : ¬ t / 2 ≤ 0 := by linarith
  rw [cutoffProfile, expNegInvGlue, if_neg h2, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t :=
  mul_nonneg (Real.exp_pos 2).le (expNegInvGlue.nonneg _)

theorem cutoffProfile_one : cutoffProfile 1 = 1 := by
  rw [cutoffProfile_of_pos one_pos]
  norm_num

theorem cutoffProfile_le_one {t : ℝ} (ht : t ≤ 1) : cutoffProfile t ≤ 1 := by
  rcases le_or_gt t 0 with h0 | h0
  · rw [cutoffProfile_of_nonpos h0]; norm_num
  · rw [cutoffProfile_of_pos h0, Real.exp_le_one_iff]
    have : 1 ≤ t⁻¹ := (one_le_inv₀ h0).mpr ht
    linarith

/-- The derivative of `exp(2 - 2/t)`. -/
theorem hasDerivAt_profileExp {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s => Real.exp (2 - 2 * s⁻¹)) (Real.exp (2 - 2 * t⁻¹) * (2 * (t ^ 2)⁻¹)) t := by
  have h := ((hasDerivAt_inv ht).const_mul 2).const_sub 2
  exact ((Real.hasDerivAt_exp _).comp t h).congr_deriv (by ring)

theorem deriv_cutoffProfile_of_pos {t : ℝ} (ht : 0 < t) :
    deriv cutoffProfile t = Real.exp (2 - 2 * t⁻¹) * (2 * (t ^ 2)⁻¹) := by
  have heq : cutoffProfile =ᶠ[𝓝 t] fun s => Real.exp (2 - 2 * s⁻¹) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact cutoffProfile_of_pos hs
  rw [heq.deriv_eq]
  exact (hasDerivAt_profileExp ht.ne').deriv

theorem deriv_cutoffProfile_of_neg {t : ℝ} (ht : t < 0) : deriv cutoffProfile t = 0 := by
  have heq : cutoffProfile =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact cutoffProfile_of_nonpos hs.le
  rw [heq.deriv_eq, deriv_const]

theorem contDiff_deriv_cutoffProfile : ContDiff ℝ ∞ (deriv cutoffProfile) :=
  (contDiff_infty_iff_deriv.mp contDiff_cutoffProfile).2

theorem contDiff_deriv2_cutoffProfile : ContDiff ℝ ∞ (deriv (deriv cutoffProfile)) :=
  (contDiff_infty_iff_deriv.mp contDiff_deriv_cutoffProfile).2

theorem deriv2_cutoffProfile_of_pos {t : ℝ} (ht : 0 < t) :
    deriv (deriv cutoffProfile) t =
      Real.exp (2 - 2 * t⁻¹) * (4 * (1 - t) / t ^ 4) := by
  have heq : deriv cutoffProfile =ᶠ[𝓝 t] fun s => Real.exp (2 - 2 * s⁻¹) * (2 * (s ^ 2)⁻¹) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact deriv_cutoffProfile_of_pos hs
  rw [heq.deriv_eq]
  have h1 := hasDerivAt_profileExp ht.ne'
  have h2 : HasDerivAt (fun s : ℝ => 2 * (s ^ 2)⁻¹) (2 * (-((t ^ 2) ^ 2)⁻¹ * (2 * t))) t := by
    have := (HasDerivAt.comp t (h := fun s : ℝ => s ^ 2) (hasDerivAt_inv (pow_ne_zero 2 ht.ne'))
      (hasDerivAt_pow 2 t)).const_mul 2
    exact this.congr_deriv (by simp)
  have h4 : HasDerivAt (fun s => Real.exp (2 - 2 * s⁻¹) * (2 * (s ^ 2)⁻¹)) _ t := h1.mul h2
  rw [h4.deriv]
  field_simp
  ring

theorem deriv_cutoffProfile_of_neg' {t : ℝ} (ht : t < 0) : deriv (deriv cutoffProfile) t = 0 := by
  have heq : deriv cutoffProfile =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact deriv_cutoffProfile_of_neg hs
  rw [heq.deriv_eq, deriv_const]

/-- A continuous function vanishing on `(-∞, 0)` vanishes at `0`. -/
theorem eq_zero_at_zero {F : ℝ → ℝ} (hF : Continuous F) (h : ∀ t < 0, F t = 0) : F 0 = 0 := by
  have hcl : IsClosed {t : ℝ | F t = 0} := isClosed_eq hF continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {t | F t = 0} := fun t ht => h t ht
  have : closure (Iio (0 : ℝ)) ⊆ {t | F t = 0} := hcl.closure_subset_iff.mpr hsub
  rw [closure_Iio] at this
  exact this (Set.mem_Iic.mpr le_rfl)

theorem deriv_cutoffProfile_nonneg (t : ℝ) : 0 ≤ deriv cutoffProfile t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [deriv_cutoffProfile_of_neg h]
  · rw [eq_zero_at_zero contDiff_deriv_cutoffProfile.continuous
      fun s hs => deriv_cutoffProfile_of_neg hs]
  · rw [deriv_cutoffProfile_of_pos h]
    positivity

/-- **`ρ` is convex on `(-∞, 1]`.** -/
theorem deriv2_cutoffProfile_nonneg {t : ℝ} (ht : t ≤ 1) : 0 ≤ deriv (deriv cutoffProfile) t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [deriv_cutoffProfile_of_neg' h]
  · rw [eq_zero_at_zero contDiff_deriv2_cutoffProfile.continuous
      fun s hs => deriv_cutoffProfile_of_neg' hs]
  · rw [deriv2_cutoffProfile_of_pos h]
    have : 0 ≤ 1 - t := by linarith
    positivity

end Profile

/-! ### The chain rule for the Levi form -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second-order chain rule `D²(ρ ∘ L) = ρ''(L) dL ⊗ dL + ρ'(L) D²L`. -/
theorem realHessian_comp {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {L : E → ℝ} {z : E}
    (hL : ContDiffAt ℝ 2 L z) (a b : E) :
    realHessian (fun y => ρ (L y)) z a b =
      deriv (deriv ρ) (L z) * fderiv ℝ L z a * fderiv ℝ L z b +
        deriv ρ (L z) * realHessian L z a b := by
  have hDL : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ L y :=
    (hL.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDDL : DifferentiableAt ℝ (fderiv ℝ L) z :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hρ'd : Differentiable ℝ (deriv ρ) :=
    (contDiff_infty_iff_deriv.mp hρ).2.differentiable (by simp)
  have hev : fderiv ℝ (fun y => ρ (L y)) =ᶠ[𝓝 z] fun y => deriv ρ (L y) • fderiv ℝ L y := by
    filter_upwards [hDL] with y hy
    exact ((hρd (L y)).hasDerivAt.comp_hasFDerivAt y hy.hasFDerivAt).fderiv
  have hsm : HasFDerivAt (fun y => deriv ρ (L y) • fderiv ℝ L y) _ z :=
    ((hρ'd (L z)).hasDerivAt.comp_hasFDerivAt z
      (hL.differentiableAt (by simp)).hasFDerivAt).smul hDDL.hasFDerivAt
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hsm.fderiv, realHessian_eq_fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    Function.comp_apply]
  ring

end Chain

section Levi

variable {n : ℕ}

theorem leviForm_comp {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {L : ComplexModel n → ℝ}
    {z : ComplexModel n} (hL : ContDiffAt ℝ 2 L z) (v : ComplexModel n) :
    leviForm (fun y => ρ (L y)) z v =
      deriv (deriv ρ) (L z) * (fderiv ℝ L z v ^ 2 + fderiv ℝ L z (Complex.I • v) ^ 2) / 4 +
        deriv ρ (L z) * leviForm L z v := by
  simp only [leviForm, realHessian_comp hρ hL]
  ring

theorem leviForm_affine {L : ComplexModel n → ℝ} {z : ComplexModel n} (hL : ContDiffAt ℝ 2 L z)
    (c d : ℝ) (v : ComplexModel n) :
    leviForm (fun y => L y / c + d) z v = leviForm L z v / c := by
  have hfun : (fun y => L y / c + d) = c⁻¹ • L + fun _ => d := by
    funext y
    simp [div_eq_inv_mul]
  rw [hfun, leviForm_add (u := c⁻¹ • L) (v := fun _ => d) (hL.const_smul c⁻¹) contDiffAt_const,
    leviForm_smul hL, leviForm_const]
  ring

variable {c : ℕ} (Y : ComplexModel n →L[ℂ] ComplexModel c)

theorem contDiff_normSq_comp : ContDiff ℝ ∞ (fun y => ‖Y y‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (Y.restrictScalars ℝ).contDiff

theorem contDiffAt_log_normSq {z : ComplexModel n} (hz : Y z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (‖Y y‖ ^ 2)) z :=
  ((contDiff_normSq_comp Y).contDiffAt).log (by positivity)

/-- **`log ‖Y‖²` is plurisubharmonic off `{Y = 0}`** (the `s = 0` case of Demailly--Păun's
estimate with `cⱼ = 1`, `Gⱼ = (Y ·)ⱼ`). -/
theorem leviForm_log_normSq_nonneg {z : ComplexModel n} (hz : Y z ≠ 0) (v : ComplexModel n) :
    0 ≤ leviForm (fun y => Real.log (‖Y y‖ ^ 2)) z v := by
  set G : Fin c → ComplexModel n → ℂ := fun j y => Y y j
  have hnorm : ∀ y, ∑ j, (fun _ : ComplexModel n => (1 : ℝ)) y ^ 2 * Complex.normSq (G j y) + 0 =
      ‖Y y‖ ^ 2 := fun y => by
    simp [G, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ∑ j, (fun _ : ComplexModel n => (1 : ℝ)) z ^ 2 * Complex.normSq (G j z) + 0 := by
    rw [hnorm]; positivity
  have hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y := fun j =>
    Eventually.of_forall fun y =>
      ((EuclideanSpace.proj (𝕜 := ℂ) j).comp Y).differentiableAt
  have h := le_leviForm_log_sum_of_pos (c := fun _ _ => (1 : ℝ)) (G := G) hpos
    (fun _ => contDiffAt_const) hG v
  have hfun : (fun y => Real.log (∑ j, (fun _ : ComplexModel n => (1 : ℝ)) y ^ 2 *
      Complex.normSq (G j y) + 0)) = fun y => Real.log (‖Y y‖ ^ 2) := funext fun y => by rw [hnorm]
  rw [hfun] at h
  refine le_trans (le_of_eq ?_) h
  have hdel : Complex.normSq (delC (fun _ : ComplexModel n => (1 : ℝ)) z v) = 0 := by
    rw [normSq_delC]; simp
  simp [hdel, leviForm_const]

/-- **The log cut-off** `Vᵢ(z) = ρ(log ‖Yz‖²/(i+1) + 1)`, `0` where `Yz = 0`. -/
def logCutoff (i : ℕ) (z : ComplexModel n) : ℝ :=
  if Y z = 0 then 0 else cutoffProfile (Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1)

theorem logCutoff_of_eq_zero (i : ℕ) {z : ComplexModel n} (hz : Y z = 0) : logCutoff Y i z = 0 :=
  if_pos hz

theorem logCutoff_eventuallyEq_zero (i : ℕ) {z : ComplexModel n} (hz : Y z = 0) :
    logCutoff Y i =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {y : ComplexModel n | ‖Y y‖ ^ 2 < Real.exp (-((i : ℝ) + 1))} :=
    isOpen_lt (contDiff_normSq_comp Y).continuous continuous_const
  have hmem : z ∈ {y : ComplexModel n | ‖Y y‖ ^ 2 < Real.exp (-((i : ℝ) + 1))} := by
    show ‖Y z‖ ^ 2 < _
    rw [hz, norm_zero]
    norm_num
    exact Real.exp_pos _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  by_cases hy0 : Y y = 0
  · exact if_pos hy0
  · rw [logCutoff, if_neg hy0]
    apply cutoffProfile_of_nonpos
    have hpos : 0 < ‖Y y‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y y‖ ^ 2) < -((i : ℝ) + 1) := by
      have := Real.log_lt_log hpos hy
      rwa [Real.log_exp] at this
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [div_add_one hi.ne', div_nonpos_iff]
    right
    exact ⟨by linarith, hi.le⟩

theorem logCutoff_eventuallyEq (i : ℕ) {z : ComplexModel n} (hz : Y z ≠ 0) :
    logCutoff Y i =ᶠ[𝓝 z]
      fun y => cutoffProfile (Real.log (‖Y y‖ ^ 2) / ((i : ℝ) + 1) + 1) := by
  have hopen : IsOpen {y : ComplexModel n | Y y ≠ 0} :=
    isOpen_ne_fun (Y.restrictScalars ℝ).continuous continuous_const
  filter_upwards [hopen.mem_nhds hz] with y hy
  exact if_neg hy

theorem contDiff_logCutoff (i : ℕ) : ContDiff ℝ ∞ (logCutoff Y i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : Y z = 0
  · exact contDiffAt_const.congr_of_eventuallyEq (logCutoff_eventuallyEq_zero Y i hz)
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (logCutoff_eventuallyEq Y i hz)
    exact contDiff_cutoffProfile.contDiffAt.comp z
      (((contDiffAt_log_normSq Y hz).div_const _).add contDiffAt_const)

theorem logCutoff_nonneg (i : ℕ) (z : ComplexModel n) : 0 ≤ logCutoff Y i z := by
  unfold logCutoff
  split_ifs
  · exact le_rfl
  · exact cutoffProfile_nonneg _

theorem logCutoff_le_one (i : ℕ) {z : ComplexModel n} (hz1 : ‖Y z‖ ^ 2 < 1) :
    logCutoff Y i z ≤ 1 := by
  unfold logCutoff
  split_ifs with hz
  · norm_num
  · apply cutoffProfile_le_one
    have hpos : 0 < ‖Y z‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y z‖ ^ 2) < 0 := Real.log_neg hpos hz1
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) < 0 := div_neg_of_neg_of_pos hlog hi
    linarith

/-- **`Vᵢ → 1` off `{Y = 0}`.** -/
theorem tendsto_logCutoff {z : ComplexModel n} (hz : Y z ≠ 0) :
    Tendsto (fun i : ℕ => logCutoff Y i z) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℕ => Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1) atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.log (‖Y z‖ ^ 2))
    rw [mul_zero] at this
    have h2 := this.add_const 1
    rw [zero_add] at h2
    refine h2.congr fun i => ?_
    ring
  have h3 := (continuous_cutoffProfile.tendsto 1).comp h1
  rw [cutoffProfile_one] at h3
  refine h3.congr fun i => ?_
  simp only [Function.comp_apply, logCutoff, if_neg hz]

/-- **`Vᵢ` is plurisubharmonic on `{‖Y‖² < 1}`.** -/
theorem smoothDDC_logCutoff_nonneg (i : ℕ) {z : ComplexModel n} (hz1 : ‖Y z‖ ^ 2 < 1)
    (u : ComplexModel n) : 0 ≤ smoothDDC (logCutoff Y i) z ![u, Complex.I • u] := by
  by_cases hz : Y z = 0
  · rw [smoothDDC_congr (logCutoff_eventuallyEq_zero Y i hz), smoothDDC_zero]
    simp
  · rw [smoothDDC_congr (logCutoff_eventuallyEq Y i hz)]
    set L : ComplexModel n → ℝ := fun y => Real.log (‖Y y‖ ^ 2) / ((i : ℝ) + 1) + 1 with hL
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hlogC : ContDiffAt ℝ 2 (fun y => Real.log (‖Y y‖ ^ 2)) z :=
      (contDiffAt_log_normSq Y hz).of_le h2
    have hLC : ContDiffAt ℝ 2 L z := (hlogC.div_const _).add contDiffAt_const
    have hcomp : ContDiffAt ℝ 2 (fun y => cutoffProfile (L y)) z :=
      (contDiff_cutoffProfile.contDiffAt.of_le h2).comp z hLC
    rw [smoothDDC_complexDiagonal_eq_leviForm hcomp, leviForm_comp contDiff_cutoffProfile hLC,
      hL, leviForm_affine hlogC]
    have hpos : 0 < ‖Y z‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y z‖ ^ 2) < 0 := Real.log_neg hpos hz1
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hLz : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1 ≤ 1 := by
      have : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) < 0 := div_neg_of_neg_of_pos hlog hi
      linarith
    have hd2 := deriv2_cutoffProfile_nonneg hLz
    have hd1 := deriv_cutoffProfile_nonneg (Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1)
    have hlev := leviForm_log_normSq_nonneg Y hz u
    have hπ := Real.pi_pos
    have : 0 ≤ leviForm (fun y => Real.log (‖Y y‖ ^ 2)) z u / ((i : ℝ) + 1) := by positivity
    positivity

end Levi

end SGPT.Foundations.Analysis.Pending.LogCutoffLevi
