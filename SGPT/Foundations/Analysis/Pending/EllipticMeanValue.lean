import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The mean value identity for constant-coefficient elliptic operators

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, and let
`A` be a constant symmetric positive definite operator on `E`.  For a `C²` function `G : E → ℝ`
write `A : D²G (x) = ∑ᵢ D²G(x)(bᵢ, A bᵢ)` (`hessTrace`; for `A = 1` it is the Laplacian).

**Mean value identity** (`integral_comp_sub_smul_mul_meanValueKernel`): if `A : D²G ≡ 0`, then for
every `x` and every `r`,
`∫ G(x - r y) η(y) dy = (∫ η) G(x)`,
for the explicit kernel `η(y) = 2 ψ(1 - ⟪B y, y⟫)` (`meanValueKernel`), where `B = A⁻¹` and `ψ` is
the derivative of `Real.smoothTransition`.  `η` is smooth, nonnegative, compactly supported, and
`∫ η > 0` when `E ≠ 0` (`integral_meanValueKernel_pos`).

This is Corollary 2.2 of Székelyhidi (*An Introduction to Extremal Kähler Metrics*,
`szekelyhidi-extremal:page-0041`) for the operator `A : D²`, obtained without spheres: with
`H(y) = smoothTransition (1 - ⟪B y, y⟫)` one has `y η(y) = -A ∇H(y)`, so
`d/dr ∫ G(x - r y) η(y) dy = -∫ DG(x - r y)(y) η(y) dy = ∑ᵢ ∫ DG(x - r y)(A bᵢ) ∂ᵢH(y) dy
= r ∫ (A : D²G)(x - r y) H(y) dy = 0` (one integration by parts per basis vector,
`integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`).

Part L2.4 of the linear track for Yau's theorem (the linear elliptic estimates): it feeds Liouville's theorem
(Székelyhidi Cor. 2.4, `page-0042`) and Simon's blow-up proof of the Schauder estimates
(Thm 2.8, `page-0044`--`page-0047`).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal RealInnerProductSpace ContDiff

namespace SGPT.Foundations.Analysis.Pending.EllipticMeanValue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The operator -/

/-- The trace pairing `A : Q = ∑ᵢ Q(bᵢ)(A bᵢ)` of a bilinear form `Q` with an operator `A`, in an
orthonormal basis `b`; `A : D²G(x)` is `hessTrace b A (fderiv ℝ (fderiv ℝ G) x)`. -/
def hessTrace {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ∑ i, Q (b i) (A (b i))

/-! ### The kernel -/

/-- `ψ = smoothTransition'`. -/
theorem contDiff_deriv_smoothTransition : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.1 (Real.smoothTransition.contDiff (n := ⊤))).2

theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) : deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [h.deriv_eq, deriv_const]

theorem exists_deriv_smoothTransition_pos : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < deriv Real.smoothTransition t := by
  obtain ⟨t, ht, hd⟩ := exists_deriv_eq_slope Real.smoothTransition (zero_lt_one' ℝ)
    Real.smoothTransition.continuous.continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero).differentiableOn
  refine ⟨t, ht, ?_⟩
  rw [hd, Real.smoothTransition.one, Real.smoothTransition.zero]
  norm_num

/-- The potential `H(y) = smoothTransition (1 - ⟪B y, y⟫)`. -/
def kernelPotential (B : E →L[ℝ] E) (y : E) : ℝ :=
  Real.smoothTransition (1 - ⟪B y, y⟫)

/-- The mean value kernel `η(y) = 2 ψ(1 - ⟪B y, y⟫)`. -/
def meanValueKernel (B : E →L[ℝ] E) (y : E) : ℝ :=
  2 * deriv Real.smoothTransition (1 - ⟪B y, y⟫)

theorem meanValueKernel_nonneg (B : E →L[ℝ] E) (y : E) : 0 ≤ meanValueKernel B y :=
  mul_nonneg zero_le_two (deriv_smoothTransition_nonneg _)

theorem contDiff_quadForm (B : E →L[ℝ] E) : ContDiff ℝ ∞ fun y : E => ⟪B y, y⟫ :=
  B.contDiff.inner ℝ contDiff_id

theorem contDiff_meanValueKernel (B : E →L[ℝ] E) : ContDiff ℝ ∞ (meanValueKernel B) :=
  contDiff_const.mul (contDiff_deriv_smoothTransition.comp (contDiff_const.sub (contDiff_quadForm B)))

theorem contDiff_kernelPotential (B : E →L[ℝ] E) : ContDiff ℝ ∞ (kernelPotential B) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_quadForm B))

/-- The derivative of `y ↦ ⟪B y, y⟫` for symmetric `B` is `v ↦ 2 ⟪B y, v⟫`. -/
theorem hasFDerivAt_quadForm {B : E →L[ℝ] E} (hBs : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (y : E) :
    HasFDerivAt (fun y : E => ⟪B y, y⟫) ((2 : ℝ) • innerSL ℝ (B y)) y := by
  have h := (B.hasFDerivAt (x := y)).inner ℝ (hasFDerivAt_id y)
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.coe_id', id_eq, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  have h1 := hBs v y
  have h2 := real_inner_comm v (B y)
  have h3 := real_inner_comm (B v) y
  linarith

/-- `DH(y) = -η(y) ⟪B y, ·⟫`, i.e. `y η(y) = -A ∇H(y)` when `A B = 1`. -/
theorem hasFDerivAt_kernelPotential {B : E →L[ℝ] E} (hBs : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (y : E) :
    HasFDerivAt (kernelPotential B) (-(meanValueKernel B y) • innerSL ℝ (B y)) y := by
  have hst : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - ⟪B y, y⟫))
      (1 - ⟪B y, y⟫) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h := hst.comp_hasFDerivAt y ((hasFDerivAt_const (1 : ℝ) y).sub (hasFDerivAt_quadForm hBs y))
  refine h.congr_fderiv ?_
  ext v
  simp only [meanValueKernel, zero_sub, smul_apply,
    neg_apply, innerSL_apply_apply, smul_eq_mul, neg_mul]
  ring

/-- `η` vanishes where `⟪B y, y⟫ > 1`. -/
theorem meanValueKernel_eq_zero {B : E →L[ℝ] E} {y : E} (hy : 1 < ⟪B y, y⟫) :
    meanValueKernel B y = 0 := by
  rw [meanValueKernel, deriv_smoothTransition_of_neg (by linarith), mul_zero]

theorem kernelPotential_eq_zero {B : E →L[ℝ] E} {y : E} (hy : 1 ≤ ⟪B y, y⟫) :
    kernelPotential B y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The radius `max 1 c⁻¹` of a ball containing `{⟪B y, y⟫ ≤ 1}` when `⟪B y, y⟫ ≥ c ‖y‖²`. -/
theorem norm_le_of_quadForm_le_one {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) {y : E} (hy : ⟪B y, y⟫ ≤ 1) : ‖y‖ ≤ max 1 c⁻¹ := by
  by_contra h
  push Not at h
  have h1 : 1 < ‖y‖ := (le_max_left _ _).trans_lt h
  have h2 : c⁻¹ < ‖y‖ := (le_max_right _ _).trans_lt h
  have h3 : 1 < c * ‖y‖ := by rwa [inv_lt_iff_one_lt_mul₀' hc] at h2
  have h4 : c * ‖y‖ ≤ c * ‖y‖ ^ 2 := by
    rw [sq]; nlinarith
  linarith [hBc y]

theorem meanValueKernel_eq_zero_of_norm {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) {y : E} (hy : max 1 c⁻¹ < ‖y‖) :
    meanValueKernel B y = 0 :=
  meanValueKernel_eq_zero (not_le.1 fun h => not_lt.2 (norm_le_of_quadForm_le_one hc hBc h) hy)

theorem kernelPotential_eq_zero_of_norm {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) {y : E} (hy : max 1 c⁻¹ < ‖y‖) :
    kernelPotential B y = 0 :=
  kernelPotential_eq_zero (not_lt.1 fun h => not_lt.2 (norm_le_of_quadForm_le_one hc hBc h.le) hy)

theorem hasCompactSupport_meanValueKernel {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) : HasCompactSupport (meanValueKernel B) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (max 1 c⁻¹)) fun y hy =>
    meanValueKernel_eq_zero_of_norm hc hBc (by simpa using hy)

theorem hasCompactSupport_kernelPotential {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) : HasCompactSupport (kernelPotential B) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (max 1 c⁻¹)) fun y hy =>
    kernelPotential_eq_zero_of_norm hc hBc (by simpa using hy)

/-! ### The mean value identity -/

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `∫ η > 0` when `E ≠ 0`. -/
theorem integral_meanValueKernel_pos [Nontrivial E] {B : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫) : 0 < ∫ y, meanValueKernel B y ∂μ := by
  obtain ⟨t, ⟨ht0, ht1⟩, htpos⟩ := exists_deriv_smoothTransition_pos
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hq : 0 < ⟪B e, e⟫ := lt_of_lt_of_le (by positivity) (hBc e)
  set s := Real.sqrt ((1 - t) / ⟪B e, e⟫) with hs
  have hy : ⟪B (s • e), s • e⟫ = 1 - t := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq, hs,
      Real.sq_sqrt (div_nonneg (by linarith) hq.le), div_mul_cancel₀ _ hq.ne']
  have hpos : meanValueKernel B (s • e) ≠ 0 := by
    rw [meanValueKernel, hy, sub_sub_cancel]
    positivity
  have hcont := (contDiff_meanValueKernel B).continuous
  have hint := hcont.integrable_of_hasCompactSupport (μ := μ) (hasCompactSupport_meanValueKernel hc hBc)
  rw [integral_pos_iff_support_of_nonneg (meanValueKernel_nonneg B) hint]
  exact hcont.isOpen_support.measure_pos μ ⟨s • e, hpos⟩

/-- **The mean value identity for `A : D²`**: if `A B = 1` with `B` symmetric and positive
definite, and `G` is `C²` with `A : D²G ≡ 0`, then `∫ G(x - r y) η(y) dy = (∫ η) G(x)` for every
`x` and `r`, with `η = meanValueKernel B`. -/
theorem integral_comp_sub_smul_mul_meanValueKernel {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {A B : E →L[ℝ] E} (hAB : ∀ y, A (B y) = y)
    (hBs : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) {c : ℝ} (hc : 0 < c) (hBc : ∀ y, c * ‖y‖ ^ 2 ≤ ⟪B y, y⟫)
    {G : E → ℝ} (hG : ContDiff ℝ 2 G) (hL : ∀ z, hessTrace b A (fderiv ℝ (fderiv ℝ G) z) = 0)
    (x : E) (r : ℝ) :
    ∫ y, G (x - r • y) * meanValueKernel B y ∂μ = (∫ y, meanValueKernel B y ∂μ) * G x := by
  set η := meanValueKernel B with hηdef
  set H := kernelPotential B with hHdef
  set R0 := max 1 c⁻¹ with hR0
  have hηc : Continuous η := (contDiff_meanValueKernel B).continuous
  have hηs : HasCompactSupport η := hasCompactSupport_meanValueKernel hc hBc
  have hHc : Continuous H := (contDiff_kernelPotential B).continuous
  have hHs : HasCompactSupport H := hasCompactSupport_kernelPotential hc hBc
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDG : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hDGd : Differentiable ℝ (fderiv ℝ G) := hDG.differentiable one_ne_zero
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ G)) := hDG.continuous_fderiv one_ne_zero
  have hηR : ∀ y, η y ≠ 0 → ‖y‖ ≤ R0 := fun y hy =>
    norm_le_of_quadForm_le_one hc hBc (not_lt.1 fun h => hy (meanValueKernel_eq_zero h))
  have hlin : ∀ (s : ℝ) (y : E), HasDerivAt (fun s : ℝ => x - s • y) (-y) s := fun s y => by
    simpa using ((hasDerivAt_id s).smul_const y).const_sub x
  -- the derivative of `F(s) = ∫ G(x - s y) η(y) dy`
  have hF : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ∫ y, G (x - s • y) * η y ∂μ)
      (∫ y, -(fderiv ℝ G (x - s • y) y) * η y ∂μ) s := by
    intro s
    obtain ⟨C0, hC0⟩ := (isCompact_closedBall x ((|s| + 1) * R0)).exists_bound_of_continuousOn
      hDG.continuous.continuousOn
    have hcontF : ∀ s' : ℝ, Continuous fun y => G (x - s' • y) * η y := fun s' =>
      (hG.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).mul hηc
    have hcontF' : Continuous fun y => -(fderiv ℝ G (x - s • y) y) * η y :=
      (((hDG.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).clm_apply
        continuous_id).neg).mul hηc
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s' y => G (x - s' • y) * η y)
      (F' := fun s' y => -(fderiv ℝ G (x - s' • y) y) * η y) (ball_mem_nhds s one_pos)
      (Eventually.of_forall fun s' => (hcontF s').aestronglyMeasurable)
      ((hcontF s).integrable_of_hasCompactSupport hηs.mul_left)
      hcontF'.aestronglyMeasurable (bound := fun y => C0 * R0 * |η y|) ?_
      ((hηc.integrable_of_hasCompactSupport hηs).abs.const_mul _) ?_).2
    · refine Eventually.of_forall fun y s' hs' => ?_
      by_cases hy : η y = 0
      · simp [hy]
      have hyR := hηR y hy
      have hs'' : |s'| ≤ |s| + 1 := by
        have := abs_sub_abs_le_abs_sub s' s
        rw [mem_ball, Real.dist_eq] at hs'
        linarith
      have hz : x - s' • y ∈ closedBall x ((|s| + 1) * R0) := by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs]
        exact mul_le_mul hs'' hyR (norm_nonneg _) (by positivity)
      rw [norm_mul, norm_neg, Real.norm_eq_abs (η y)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact ((fderiv ℝ G (x - s' • y)).le_opNorm y).trans
        (mul_le_mul (hC0 _ hz) hyR (norm_nonneg _) ((norm_nonneg _).trans (hC0 _ hz)))
    · refine Eventually.of_forall fun y s' _ => ?_
      have h := ((hG1 (x - s' • y)).hasFDerivAt.comp_hasDerivAt s' (hlin s' y)).mul_const (η y)
      simpa only [map_neg, Function.comp_def] using h
  -- the derivative vanishes
  have hF'0 : ∀ s : ℝ, ∫ y, -(fderiv ℝ G (x - s • y) y) * η y ∂μ = 0 := by
    intro s
    set f : ι → E → ℝ := fun i y => fderiv ℝ G (x - s • y) (A (b i)) with hfdef
    set f' : ι → E → E →L[ℝ] ℝ := fun i y => (ContinuousLinearMap.apply ℝ ℝ (A (b i))).comp
      ((fderiv ℝ (fderiv ℝ G) (x - s • y)).comp (-(s • ContinuousLinearMap.id ℝ E))) with hf'def
    have hfc : ∀ i, Continuous (f i) := fun i =>
      (hDG.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).clm_apply
        continuous_const
    have hf'c : ∀ i, Continuous fun y => f' i y (b i) := by
      intro i
      simp only [hf'def, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.apply_apply]
      exact ((hD2c.comp (continuous_const.sub (continuous_const.smul continuous_id))).clm_apply
        continuous_const).clm_apply continuous_const
    have hfd : ∀ i y, HasFDerivAt (f i) (f' i y) y := by
      intro i y
      have h1 : HasFDerivAt (fun y : E => x - s • y) (-(s • ContinuousLinearMap.id ℝ E)) y :=
        ((hasFDerivAt_id y).const_smul s).const_sub x
      exact (ContinuousLinearMap.apply ℝ ℝ (A (b i))).hasFDerivAt.comp y
        ((hDGd (x - s • y)).hasFDerivAt.comp y h1)
    have hHd := hasFDerivAt_kernelPotential hBs
    -- the pointwise identity `-DG(z)(y) η(y) = ∑ᵢ DG(z)(A bᵢ) ∂ᵢH(y)`
    have hpt : ∀ y, -(fderiv ℝ G (x - s • y) y) * η y =
        ∑ i, f i y * ((-(η y) • innerSL ℝ (B y)) (b i)) := by
      intro y
      have hsum : ∑ i, ⟪B y, b i⟫ • b i = B y := by
        simpa only [real_inner_comm] using b.sum_repr' (B y)
      simp only [hfdef, smul_apply, innerSL_apply_apply, smul_eq_mul]
      have : ∑ i, fderiv ℝ G (x - s • y) (A (b i)) * (-η y * ⟪B y, b i⟫) =
          -η y * fderiv ℝ G (x - s • y) (A (∑ i, ⟪B y, b i⟫ • b i)) := by
        rw [map_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
        ring
      rw [this, hsum, hAB]
      ring
    have hint1 : ∀ i, Integrable (fun y => f i y * ((-(η y) • innerSL ℝ (B y)) (b i))) μ := by
      intro i
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
        exact (hfc i).mul ((hηc.neg).mul (B.continuous.inner continuous_const))
      · refine HasCompactSupport.mul_left ?_
        simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
        exact (hηs.neg).mul_right
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun i _ => hint1 i]
    -- integrate by parts in each direction
    have hibp : ∀ i, ∫ y, f i y * ((-(η y) • innerSL ℝ (B y)) (b i)) ∂μ =
        ∫ y, s * (fderiv ℝ (fderiv ℝ G) (x - s • y) (b i) (A (b i))) * H y ∂μ := by
      intro i
      have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := μ)
        (f := f i) (f' := f' i) (g := H) (g' := fun y => -(η y) • innerSL ℝ (B y)) (v := b i)
        (B := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ ?_ (fun y _ => hfd i y) (fun y _ => hHd y)
      · simp only [ContinuousLinearMap.mul_apply'] at h
        rw [h, ← integral_neg]
        congr 1
        funext y
        simp only [hf'def, ContinuousLinearMap.coe_comp, Function.comp_apply,
          neg_apply, smul_apply, ContinuousLinearMap.coe_id', id_eq,
          map_neg, map_smul, ContinuousLinearMap.apply_apply, neg_apply]
        simp only [smul_eq_mul]
        ring
      · simp only [ContinuousLinearMap.mul_apply']
        exact ((hf'c i).mul hHc).integrable_of_hasCompactSupport hHs.mul_left
      · simpa only [ContinuousLinearMap.mul_apply'] using hint1 i
      · simp only [ContinuousLinearMap.mul_apply']
        exact ((hfc i).mul hHc).integrable_of_hasCompactSupport hHs.mul_left
    simp_rw [hibp]
    have hint2 : ∀ i, Integrable
        (fun y => s * (fderiv ℝ (fderiv ℝ G) (x - s • y) (b i) (A (b i))) * H y) μ := by
      intro i
      refine Continuous.integrable_of_hasCompactSupport ?_ hHs.mul_left
      exact (continuous_const.mul (((hD2c.comp (continuous_const.sub
        (continuous_const.smul continuous_id))).clm_apply continuous_const).clm_apply
          continuous_const)).mul hHc
    rw [← integral_finsetSum _ fun i _ => hint2 i]
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_zero E ℝ)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have := hL (x - s • y)
    rw [hessTrace] at this
    rw [this, mul_zero, zero_mul]
  -- `F` is constant
  have hconst := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => by rw [(hF s).deriv, hF'0 s]) r 0
  rw [hconst]
  simp only [zero_smul, sub_zero]
  rw [integral_const_mul]
  ring

end SGPT.Foundations.Analysis.Pending.EllipticMeanValue
