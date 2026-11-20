import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Genuine first-order holomorphic gauge and uniform C² real Taylor bound.
The complete source-facing proof route was pinned before this source existed.
These are analytic producers, with no section-growth or evaluation bound input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Set Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Compactness bounds the actual second derivative; two applications of
real mean value manufacture the SAME uniform quadratic Taylor remainder. -/
theorem exists_uniform_quadratic_remainder {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hKU : K ⊆ U)
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a ∈ K, ∀ z ∈ K,
      |p z - p a - fderiv ℝ p a (z - a)| ≤ A * ‖z - a‖ ^ 2 := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ p) U :=
    hp.fderiv_of_isOpen hU (by norm_num)
  have hDD : ContinuousOn (fderiv ℝ (fderiv ℝ p)) U :=
    hD.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hnorm : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ p) x‖) K :=
    ((show Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => ‖A‖) from
      @continuous_norm (E →L[ℝ] E →L[ℝ] ℝ) inferInstance).comp_continuousOn hDD).mono hKU
  obtain ⟨A₀, hA₀raw⟩ := hK.exists_bound_of_continuousOn hnorm
  have hA₀ (x : E) (hx : x ∈ K) : ‖fderiv ℝ (fderiv ℝ p) x‖ ≤ A₀ := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hA₀raw x hx)
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hd (x : E) (hx : x ∈ K) : DifferentiableAt ℝ p x :=
    (hp.differentiableOn (by norm_num) x (hKU hx)).differentiableAt
      (hU.mem_nhds (hKU hx))
  have hdd (x : E) (hx : x ∈ K) : DifferentiableAt ℝ (fderiv ℝ p) x :=
    (hD.differentiableOn (by norm_num) x (hKU hx)).differentiableAt
      (hU.mem_nhds (hKU hx))
  have hLip (a : E) (ha : a ∈ K) (z : E) (hz : z ∈ K) :
      ‖fderiv ℝ p z - fderiv ℝ p a‖ ≤ A * ‖z - a‖ :=
    hconv.norm_image_sub_le_of_norm_fderiv_le hdd
      (fun x hx => (hA₀ x hx).trans (le_max_left _ _)) ha hz
  refine ⟨A, hA, fun a ha z hz => ?_⟩
  have hseg : segment ℝ a z ⊆ K := hconv.segment_subset ha hz
  have hbound (y : E) (hy : y ∈ segment ℝ a z) :
      ‖fderiv ℝ p y - fderiv ℝ p a‖ ≤ A * ‖z - a‖ :=
    (hLip a ha y (hseg hy)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hA)
  have hm := (convex_segment a z).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => hd y (hseg hy)) hbound
    (left_mem_segment ℝ a z) (right_mem_segment ℝ a z)
  simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hm

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Native dual extension, rather than an incoming complex-linear gauge. -/
def holomorphicFirstOrderGauge (D : E →L[ℝ] ℝ) (b : ℝ) (a : E)
    (F : E → ℂ) (z : E) : ℂ :=
  F z * Complex.exp (((b : ℂ) + StrongDual.extendRCLike (𝕜 := ℂ) D (z - a)) / 2)

/-- The gauge is holomorphic on the SAME original domain. -/
theorem holomorphicFirstOrderGauge_differentiableOn (D : E →L[ℝ] ℝ)
    (b : ℝ) (a : E) {F : E → ℂ} {U : Set E}
    (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (holomorphicFirstOrderGauge D b a F) U := by
  apply hF.mul
  apply Complex.differentiable_exp.comp_differentiableOn
  have hlin : Differentiable ℂ (fun z : E =>
      ((b : ℂ) + StrongDual.extendRCLike (𝕜 := ℂ) D (z - a)) / 2) := by
    simp only [div_eq_mul_inv]
    exact ((differentiable_const (c := (b : ℂ))).add
      ((StrongDual.extendRCLike (𝕜 := ℂ) D).differentiable.comp
        (differentiable_id.sub_const a))).mul_const _
  exact hlin.differentiableOn

/-- Exact SAME-point density formula, retaining zeros of the coefficient. -/
theorem holomorphicFirstOrderGauge_norm_sq (D : E →L[ℝ] ℝ)
    (b : ℝ) (a : E) (F : E → ℂ) (z : E) :
    ‖holomorphicFirstOrderGauge D b a F z‖ ^ 2 =
      ‖F z‖ ^ 2 * Real.exp (b + D (z - a)) := by
  rw [holomorphicFirstOrderGauge, norm_mul, mul_pow, Complex.norm_exp]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re,
    StrongDual.extendRCLike_apply]
  simp
  ring

/-- At the center the gauge exactly recovers the original weighted norm. -/
theorem holomorphicFirstOrderGauge_center (D : E →L[ℝ] ℝ)
    (b : ℝ) (a : E) (F : E → ℂ) :
    ‖holomorphicFirstOrderGauge D b a F a‖ ^ 2 = ‖F a‖ ^ 2 * Real.exp b := by
  simp [holomorphicFirstOrderGauge_norm_sq]

end SGPT.Bergman.PolynomialH0Growth
