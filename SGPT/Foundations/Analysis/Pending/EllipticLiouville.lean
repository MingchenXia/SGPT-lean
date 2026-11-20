import SGPT.Foundations.Analysis.Pending.EllipticMeanValue

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Liouville's theorem with Hölder growth, and the rigidity statement of Simon's blow-up

* `add_eq_of_meanValue_of_holder` (**Liouville**): a continuous `w : E → ℝ` with the mean value
  property `∫ w(x - r y) η(y) dy = (∫ η) w(x)` for one Lipschitz compactly supported kernel with
  `∫ η ≠ 0`, and with `|w x - w x'| ≤ K ‖x - x'‖^α`, `α < 1`, is constant.  Translating the kernel
  by `v / r` gives `(∫ η)(w(x + v) - w(x)) = ∫ (w(x - r y) - w(x)) (η(y + v/r) - η(y)) dy`, which is
  `O(r^{α - 1})`.
* `fderiv_fderiv_eq_of_hessTrace_eq_zero` (**rigidity**): if `G` is `C²`, `A : D²G ≡ 0` for a
  constant symmetric operator `A ≥ λ > 0`, and `D²G` is `α`-Hölder with `α < 1`, then `D²G` is
  constant.  The second differences `G(x+h+k) - G(x+h) - G(x+k) + G(x)` have the mean value property
  (`EllipticMeanValue`) and Hölder growth, hence are constant in `x`; differentiating twice gives the
  claim.

This is Székelyhidi's Corollary 2.4 (`szekelyhidi-extremal:page-0042`) in the form used at the end of
the proof of Theorem 2.8 (`page-0046`--`page-0047`: the blow-up limit `G` satisfies
`∑ A_{jk} ∂_j ∂_k G = 0` and `|∂²G(x)| ≤ 2^α |x|^α`, so `∂²G` is constant), with the linear change of
coordinates replaced by the `A`-adapted kernel of `EllipticMeanValue`.

Part L2.5 of the linear track for Yau's theorem (the linear elliptic estimates).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal RealInnerProductSpace ContDiff

namespace SGPT.Foundations.Analysis.Pending.EllipticLiouville

open EllipticMeanValue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Liouville's theorem with Hölder growth**, mean value form. -/
theorem add_eq_of_meanValue_of_holder {η : E → ℝ} (hηc : Continuous η)
    (hηs : HasCompactSupport η) {L : ℝ≥0} (hηL : LipschitzWith L η)
    (hη0 : ∫ y, η y ∂μ ≠ 0) {w : E → ℝ} (hw : Continuous w)
    (hmv : ∀ x (r : ℝ), 0 < r → ∫ y, w (x - r • y) * η y ∂μ = (∫ y, η y ∂μ) * w x)
    {K α : ℝ} (hK : 0 ≤ K) (hα0 : 0 ≤ α) (hα : α < 1)
    (hH : ∀ x x', |w x - w x'| ≤ K * ‖x - x'‖ ^ α) (x v : E) : w (x + v) = w x := by
  obtain ⟨R0, hR0⟩ := hηs.isCompact.isBounded.subset_closedBall 0
  set R1 := max R0 0 + 1 with hR1
  have hR1pos : 0 < R1 := by positivity
  have hη_out : ∀ z : E, R1 - 1 < ‖z‖ → η z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hzs => ?_
    have := hR0 hzs
    rw [mem_closedBall, dist_zero_right] at this
    have : R0 ≤ max R0 0 := le_max_left _ _
    linarith
  set c := ∫ y, η y ∂μ with hc
  set S := μ.real (closedBall (0 : E) R1) with hS
  set D := K * R1 ^ α * L * ‖v‖ * S with hD
  -- the estimate for every large `r`
  have hest : ∀ r : ℝ, max ‖v‖ 1 ≤ r →
      |c| * |w (x + v) - w x| ≤ D * r ^ (-(1 - α)) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hr)
    set h : E := r⁻¹ • v with hh
    have hhn : ‖h‖ ≤ 1 := by
      rw [hh, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      rw [inv_mul_le_iff₀ hr0, mul_one]
      exact (le_max_left _ _).trans hr
    have hrh : r • h = v := by rw [hh, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hcont : ∀ (z : E) (f : E → ℝ), Continuous f → HasCompactSupport f →
        Integrable (fun y => w (z - r • y) * f y) μ := fun z f hf hfs =>
      ((hw.comp (continuous_const.sub (continuous_const.smul continuous_id))).mul hf
        ).integrable_of_hasCompactSupport hfs.mul_left
    have hηh_s : HasCompactSupport fun y => η (y + h) := hηs.comp_homeomorph (Homeomorph.addRight h)
    have hηh_c : Continuous fun y => η (y + h) := hηc.comp (continuous_id.add continuous_const)
    -- translate the kernel
    have h1 : ∫ y, w (x + v - r • y) * η y ∂μ = ∫ y, w (x - r • y) * η (y + h) ∂μ := by
      rw [← integral_add_right_eq_self (μ := μ) (fun y => w (x + v - r • y) * η y) h]
      congr 1
      funext y
      congr 2
      rw [smul_add, hrh]
      abel
    have hηint : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
    have h2 : ∫ y, η (y + h) ∂μ = c := integral_add_right_eq_self (μ := μ) η h
    have hkey : c * (w (x + v) - w x) =
        ∫ y, (w (x - r • y) - w x) * (η (y + h) - η y) ∂μ := by
      have hA := hmv (x + v) r hr0
      have hB := hmv x r hr0
      rw [h1] at hA
      have hexp : (fun y => (w (x - r • y) - w x) * (η (y + h) - η y)) =
          fun y => (w (x - r • y) * η (y + h) - w (x - r • y) * η y) -
            w x * (η (y + h) - η y) := by
        funext y; ring
      have hdiff : Integrable (fun y => η (y + h) - η y) μ :=
        (hηh_c.sub hηc).integrable_of_hasCompactSupport (hηh_s.sub hηs)
      have hI1 : Integrable (fun y => w (x - r • y) * η (y + h) - w (x - r • y) * η y) μ :=
        (hcont x _ hηh_c hηh_s).sub (hcont x _ hηc hηs)
      have hI2 : Integrable (fun y => w x * (η (y + h) - η y)) μ := hdiff.const_mul (w x)
      rw [hexp, integral_sub hI1 hI2,
        integral_sub (hcont x _ hηh_c hηh_s) (hcont x _ hηc hηs), integral_const_mul,
        integral_sub (hηh_c.integrable_of_hasCompactSupport hηh_s) hηint, h2, hA, hB]
      ring
    -- bound the integrand
    set M := K * R1 ^ α * L * ‖v‖ * r ^ (α - 1) with hM
    have hbound : ∀ y, ‖(w (x - r • y) - w x) * (η (y + h) - η y)‖ ≤
        (closedBall (0 : E) R1).indicator (fun _ => M) y := by
      intro y
      by_cases hy : y ∈ closedBall (0 : E) R1
      · rw [indicator_of_mem hy]
        rw [mem_closedBall, dist_zero_right] at hy
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hw1 : |w (x - r • y) - w x| ≤ K * (r ^ α * R1 ^ α) := by
          refine (hH _ _).trans (mul_le_mul_of_nonneg_left ?_ hK)
          rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr0,
            ← Real.mul_rpow hr0.le hR1pos.le]
          exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hy hr0.le) hα0
        have hη1 : |η (y + h) - η y| ≤ L * (r⁻¹ * ‖v‖) := by
          have := hηL.dist_le_mul (y + h) y
          rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, hh, norm_smul, Real.norm_eq_abs,
            abs_inv, abs_of_pos hr0] at this
          exact this
        calc |w (x - r • y) - w x| * |η (y + h) - η y|
            ≤ (K * (r ^ α * R1 ^ α)) * (L * (r⁻¹ * ‖v‖)) :=
              mul_le_mul hw1 hη1 (abs_nonneg _) (by positivity)
          _ = M := by
              rw [hM, Real.rpow_sub_one hr0.ne']
              field_simp
      · rw [indicator_of_notMem hy]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        have hy1 : η y = 0 := hη_out y (by linarith)
        have hy2 : η (y + h) = 0 := by
          refine hη_out _ ?_
          have := norm_sub_norm_le y (-h)
          rw [sub_neg_eq_add, norm_neg] at this
          have := norm_add_le (y + h) (-h)
          rw [add_neg_cancel_right, norm_neg] at this
          linarith
        rw [hy1, hy2, sub_self, mul_zero, norm_zero]
    have hint_ind : Integrable ((closedBall (0 : E) R1).indicator fun _ => M) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (measure_closedBall_lt_top (μ := μ)).ne)
    have hnorm := norm_integral_le_of_norm_le hint_ind (Eventually.of_forall hbound)
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, ← hkey, norm_mul,
      Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    calc |c| * |w (x + v) - w x| ≤ S * M := hnorm
      _ = D * r ^ (-(1 - α)) := by rw [hM, hD, neg_sub]; ring
  -- let `r → ∞`
  have hlim : Tendsto (fun r : ℝ => D * r ^ (-(1 - α))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)).const_mul D
  have h0 : |c| * |w (x + v) - w x| ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨max ‖v‖ 1, hest⟩)
  have hcpos : 0 < |c| := abs_pos.2 hη0
  have : |w (x + v) - w x| = 0 :=
    le_antisymm (by nlinarith [abs_nonneg (w (x + v) - w x)]) (abs_nonneg _)
  linarith [abs_eq_zero.1 this]

/-! ### Second differences -/

/-- A shifted derivative: `t ↦ F(a + t)` has derivative `F'(a + t)`. -/
theorem hasFDerivAt_comp_const_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : E → V} {F' : E → E →L[ℝ] V} (hF : ∀ z, HasFDerivAt F (F' z) z) (a t : E) :
    HasFDerivAt (fun t => F (a + t)) (F' (a + t)) t := by
  have := (hF (a + t)).comp t ((hasFDerivAt_id t).const_add a)
  simpa [Function.comp_def] using this

/-- **Hölder growth of second differences**: if `D²G` is `(K, α)`-Hölder, then
`|Δ_{h,k}G(y) - Δ_{h,k}G(y')| ≤ K ‖y - y'‖^α ‖k‖ ‖h‖`, where
`Δ_{h,k}G(y) = G(y + h + k) - G(y + h) - G(y + k) + G(y)`. -/
theorem abs_secondDiff_sub_le {G : E → ℝ} (hG : ContDiff ℝ 2 G) {K α : ℝ}
    (hH : ∀ z z', ‖fderiv ℝ (fderiv ℝ G) z - fderiv ℝ (fderiv ℝ G) z'‖ ≤ K * ‖z - z'‖ ^ α)
    (h k y y' : E) :
    |(G (y + h + k) - G (y + h) - G (y + k) + G y) -
        (G (y' + h + k) - G (y' + h) - G (y' + k) + G y')| ≤
      K * ‖y - y'‖ ^ α * ‖k‖ * ‖h‖ := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDGd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hGd : ∀ z, HasFDerivAt G (fderiv ℝ G z) z := fun z => (hG1 z).hasFDerivAt
  have hDGh : ∀ z, HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) z) z :=
    fun z => (hDGd z).hasFDerivAt
  -- the inner difference `χ_t(s) = DG(y + t + s) - DG(y' + t + s)`
  have hχ : ∀ t : E, ‖(fderiv ℝ G (y + t + k) - fderiv ℝ G (y' + t + k)) -
      (fderiv ℝ G (y + t) - fderiv ℝ G (y' + t))‖ ≤ K * ‖y - y'‖ ^ α * ‖k‖ := by
    intro t
    have hd : ∀ s ∈ (univ : Set E), HasFDerivWithinAt
        (fun s => fderiv ℝ G (y + t + s) - fderiv ℝ G (y' + t + s))
        (fderiv ℝ (fderiv ℝ G) (y + t + s) - fderiv ℝ (fderiv ℝ G) (y' + t + s)) univ s :=
      fun s _ => ((hasFDerivAt_comp_const_add hDGh (y + t) s).sub
        (hasFDerivAt_comp_const_add hDGh (y' + t) s)).hasFDerivWithinAt
    have hb : ∀ s ∈ (univ : Set E),
        ‖fderiv ℝ (fderiv ℝ G) (y + t + s) - fderiv ℝ (fderiv ℝ G) (y' + t + s)‖ ≤
          K * ‖y - y'‖ ^ α := fun s _ => by
      have := hH (y + t + s) (y' + t + s)
      rwa [show y + t + s - (y' + t + s) = y - y' by abel] at this
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb convex_univ (mem_univ 0)
      (mem_univ k)
    simpa only [add_zero, sub_zero] using this
  -- the outer difference `ψ(t) = G(y + k + t) - G(y + t) - G(y' + k + t) + G(y' + t)`
  have hd : ∀ t ∈ (univ : Set E), HasFDerivWithinAt
      (fun t => G (y + k + t) - G (y + t) - G (y' + k + t) + G (y' + t))
      (fderiv ℝ G (y + k + t) - fderiv ℝ G (y + t) - fderiv ℝ G (y' + k + t) +
        fderiv ℝ G (y' + t)) univ t :=
    fun t _ => ((((hasFDerivAt_comp_const_add hGd (y + k) t).sub
      (hasFDerivAt_comp_const_add hGd y t)).sub (hasFDerivAt_comp_const_add hGd (y' + k) t)).add
        (hasFDerivAt_comp_const_add hGd y' t)).hasFDerivWithinAt
  have hb : ∀ t ∈ (univ : Set E), ‖fderiv ℝ G (y + k + t) - fderiv ℝ G (y + t) -
      fderiv ℝ G (y' + k + t) + fderiv ℝ G (y' + t)‖ ≤ K * ‖y - y'‖ ^ α * ‖k‖ := by
    intro t _
    have := hχ t
    rwa [show (fderiv ℝ G (y + t + k) - fderiv ℝ G (y' + t + k)) -
        (fderiv ℝ G (y + t) - fderiv ℝ G (y' + t)) = fderiv ℝ G (y + k + t) - fderiv ℝ G (y + t) -
          fderiv ℝ G (y' + k + t) + fderiv ℝ G (y' + t) by
        rw [add_right_comm y t k, add_right_comm y' t k]; abel] at this
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb convex_univ (mem_univ 0)
    (mem_univ h)
  simp only [add_zero, sub_zero, Real.norm_eq_abs] at this
  convert this using 2
  rw [add_right_comm y h k, add_right_comm y' h k, add_comm y h, add_comm y' h]
  ring_nf

/-! ### Rigidity -/

/-- **Rigidity** (the end of Simon's blow-up argument, Székelyhidi Thm 2.8, `page-0046`--`page-0047`):
if `G` is `C²`, `A : D²G ≡ 0` for a constant symmetric `A` with `⟪A v, v⟫ ≥ λ ‖v‖²` (`λ > 0`), and
`D²G` is `(K, α)`-Hölder with `α < 1`, then `D²G` is constant. -/
theorem fderiv_fderiv_eq_of_hessTrace_eq_zero {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {A : E →L[ℝ] E} (hAs : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) {lam : ℝ} (hlam : 0 < lam)
    (hAe : ∀ v, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫) {G : E → ℝ} (hG : ContDiff ℝ 2 G)
    (hL : ∀ z, hessTrace b A (fderiv ℝ (fderiv ℝ G) z) = 0) {K α : ℝ} (hK : 0 ≤ K)
    (hα0 : 0 ≤ α) (hα : α < 1)
    (hH : ∀ z z', ‖fderiv ℝ (fderiv ℝ G) z - fderiv ℝ (fderiv ℝ G) z'‖ ≤ K * ‖z - z'‖ ^ α)
    (x : E) : fderiv ℝ (fderiv ℝ G) x = fderiv ℝ (fderiv ℝ G) 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim x 0]
  -- the inverse `B = A⁻¹`
  have hinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 := hAe v
    rw [hv, inner_zero_left] at h1
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg v])
  set e := LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hinj with he
  set B : E →L[ℝ] E := LinearMap.toContinuousLinearMap (e.symm : E →ₗ[ℝ] E) with hBdef
  have hAB : ∀ y, A (B y) = y := fun y => e.apply_symm_apply y
  have hBs : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫ := by
    intro u v
    conv_lhs => rw [← hAB v]
    rw [← hAs, hAB]
  have hA0 : 0 < ‖A‖ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine norm_pos_iff.2 fun h0 => hv (hinj ?_)
    rw [h0, map_zero, zero_apply]
  have hBc : ∀ y, lam / ‖A‖ ^ 2 * ‖y‖ ^ 2 ≤ ⟪B y, y⟫ := by
    intro y
    have h1 : ‖y‖ ≤ ‖A‖ * ‖B y‖ := by
      conv_lhs => rw [← hAB y]
      exact A.le_opNorm _
    have h2 : ‖y‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B y‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : lam * ‖B y‖ ^ 2 ≤ ⟪B y, y⟫ := by
      have := hAe (B y)
      rwa [hAB, real_inner_comm] at this
    calc lam / ‖A‖ ^ 2 * ‖y‖ ^ 2 ≤ lam / ‖A‖ ^ 2 * (‖A‖ ^ 2 * ‖B y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = lam * ‖B y‖ ^ 2 := by field_simp
      _ ≤ ⟪B y, y⟫ := h3
  have hc : 0 < lam / ‖A‖ ^ 2 := by positivity
  -- the kernel
  let μ0 : Measure E := Measure.addHaar
  set η := meanValueKernel B with hηdef
  have hηc : Continuous η := (contDiff_meanValueKernel B).continuous
  have hηs : HasCompactSupport η := hasCompactSupport_meanValueKernel hc hBc
  obtain ⟨Lη, hηL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hηs (contDiff_meanValueKernel B)
    (by simp)
  have hη0 : ∫ y, η y ∂μ0 ≠ 0 := (integral_meanValueKernel_pos hc hBc).ne'
  have hmvG : ∀ z (r : ℝ), ∫ y, G (z - r • y) * η y ∂μ0 = (∫ y, η y ∂μ0) * G z :=
    fun z r => integral_comp_sub_smul_mul_meanValueKernel b hAB hBs hc hBc hG hL z r
  have hGi : ∀ (z : E) (r : ℝ), Integrable (fun y => G (z - r • y) * η y) μ0 := fun z r =>
    ((hG.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).mul
      hηc).integrable_of_hasCompactSupport hηs.mul_left
  -- second differences are constant
  have hconst : ∀ h k y : E, G (y + h + k) - G (y + h) - G (y + k) + G y =
      G (0 + h + k) - G (0 + h) - G (0 + k) + G 0 := by
    intro h k
    set w : E → ℝ := fun y => G (y + h + k) - G (y + h) - G (y + k) + G y with hw
    have hwc : Continuous w := by
      simp only [hw]
      fun_prop
    have hmv : ∀ z (r : ℝ), 0 < r → ∫ y, w (z - r • y) * η y ∂μ0 = (∫ y, η y ∂μ0) * w z := by
      intro z r _
      have hpt : ∀ y, w (z - r • y) * η y = G ((z + h + k) - r • y) * η y -
          G ((z + h) - r • y) * η y - G ((z + k) - r • y) * η y + G (z - r • y) * η y := by
        intro y
        simp only [hw]
        rw [show z - r • y + h + k = z + h + k - r • y by abel,
          show z - r • y + h = z + h - r • y by abel, show z - r • y + k = z + k - r • y by abel]
        ring
      have hI12 : Integrable (fun y => G ((z + h + k) - r • y) * η y -
          G ((z + h) - r • y) * η y) μ0 := (hGi _ r).sub (hGi _ r)
      have hI123 : Integrable (fun y => G ((z + h + k) - r • y) * η y -
          G ((z + h) - r • y) * η y - G ((z + k) - r • y) * η y) μ0 := hI12.sub (hGi _ r)
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hI123 (hGi _ r),
        integral_sub hI12 (hGi _ r), integral_sub (hGi _ r) (hGi _ r), hmvG, hmvG, hmvG, hmvG]
      simp only [hw]
      ring
    have hwH : ∀ y y', |w y - w y'| ≤ (K * ‖k‖ * ‖h‖) * ‖y - y'‖ ^ α := by
      intro y y'
      have := abs_secondDiff_sub_le hG hH h k y y'
      simp only [hw]
      calc _ ≤ K * ‖y - y'‖ ^ α * ‖k‖ * ‖h‖ := this
        _ = _ := by ring
    intro y
    have := add_eq_of_meanValue_of_holder hηc hηs hηL hη0 hwc hmv (by positivity) hα0 hα hwH 0 y
    simpa only [hw, zero_add] using this
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDGd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hGd : ∀ z, HasFDerivAt G (fderiv ℝ G z) z := fun z => (hG1 z).hasFDerivAt
  have hDGh : ∀ z, HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) z) z :=
    fun z => (hDGd z).hasFDerivAt
  -- differentiate in `y`: `DG(y + h + k) - DG(y + h) - DG(y + k) + DG(y) = 0`
  have hstepB : ∀ h k y : E, fderiv ℝ G (h + k + y) - fderiv ℝ G (h + y) - fderiv ℝ G (k + y) +
      fderiv ℝ G y = 0 := by
    intro h k y
    have h1 : HasFDerivAt (fun y => G (h + k + y) - G (h + y) - G (k + y) + G y)
        (fderiv ℝ G (h + k + y) - fderiv ℝ G (h + y) - fderiv ℝ G (k + y) + fderiv ℝ G y) y :=
      (((hasFDerivAt_comp_const_add hGd (h + k) y).sub (hasFDerivAt_comp_const_add hGd h y)).sub
        (hasFDerivAt_comp_const_add hGd k y)).add (hGd y)
    have h2 : HasFDerivAt (fun y => G (h + k + y) - G (h + y) - G (k + y) + G y)
        (0 : E →L[ℝ] ℝ) y := by
      have : (fun y => G (h + k + y) - G (h + y) - G (k + y) + G y) =
          fun _ => G (0 + h + k) - G (0 + h) - G (0 + k) + G 0 := by
        funext y
        rw [← hconst h k y, show h + k + y = y + h + k by abel, show h + y = y + h by abel,
          show k + y = y + k by abel]
      rw [this]
      exact hasFDerivAt_const _ _
    exact h1.unique h2
  -- differentiate in `k`: `D²G(y + h) = D²G(y)`
  have hstepC : ∀ y h : E, fderiv ℝ (fderiv ℝ G) (h + y) = fderiv ℝ (fderiv ℝ G) y := by
    intro y h
    have h1 : HasFDerivAt (fun k => fderiv ℝ G (h + y + k) - fderiv ℝ G (y + k))
        (fderiv ℝ (fderiv ℝ G) (h + y + 0) - fderiv ℝ (fderiv ℝ G) (y + 0)) 0 :=
      (hasFDerivAt_comp_const_add hDGh (h + y) 0).sub (hasFDerivAt_comp_const_add hDGh y 0)
    have h2 : HasFDerivAt (fun k => fderiv ℝ G (h + y + k) - fderiv ℝ G (y + k))
        (0 : E →L[ℝ] E →L[ℝ] ℝ) 0 := by
      have : (fun k => fderiv ℝ G (h + y + k) - fderiv ℝ G (y + k)) =
          fun _ => fderiv ℝ G (h + y) - fderiv ℝ G y := by
        funext k
        have := hstepB h k y
        rw [show h + k + y = h + y + k by abel, show k + y = y + k by abel] at this
        rw [← sub_eq_zero]
        rw [← this]
        abel
      rw [this]
      exact hasFDerivAt_const _ _
    have := h1.unique h2
    rwa [add_zero, add_zero, sub_eq_zero] at this
  simpa using hstepC 0 x

end SGPT.Foundations.Analysis.Pending.EllipticLiouville
