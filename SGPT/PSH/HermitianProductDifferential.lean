import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

/-!
# Differentiating products with arbitrary smooth background forms

The coefficientwise derivative is computed on the actual distributional
current. Smooth background forms need not be closed. The closedness of
the Bedford--Taylor factor is used only when differentiating its product
with a smooth scalar coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProductDifferential

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCollar LocalBedfordTaylorDecreasing
  LocalCurrentLebesgue ConstantFormProducts CoordinateWedgeAssoc
  LocalBedfordTaylorMass
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {r k m : ℕ}

/-- Smooth scalar multiplication of an arbitrary distributional current. -/
def smoothMulCurrent (R : LocalProductCurrent n U m)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    LocalProductCurrent n U m :=
  precompLM (mulSmoothOnCLM hf) ∘ₗ R

/-- Exterior product by one genuine constant form in the complementary
test space. No positivity or closedness is imposed on either argument. -/
def constantWedge (h : r + k = m) (R : LocalProductCurrent n U m)
    (β : formSpan n k) : LocalProductCurrent n U r :=
  R ∘ₗ (wedgeSpan n h).flip β

theorem wedgeForm_eq_sum_constantWedge (h : r + k = m)
    (R : LocalProductCurrent n U m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm h R hα = ∑ i,
      constantWedge h (smoothMulCurrent R (contDiffOn_formCoeff hα i)) (formBasis n k i) := by
  rfl

/-- The actual distributional `ddᶜ` operator is real-linear. -/
def ddcLinearMap : LocalProductCurrent n U (m + 1) →ₗ[ℝ] LocalProductCurrent n U m where
  toFun := ddc
  map_add' := ddc_add
  map_smul' := ddc_smul

theorem ddc_constantWedge (h : r + 1 + k = m + 1) (h' : r + k = m)
    (R : LocalProductCurrent n U (m + 1)) (β : formSpan n k) :
    ddc (constantWedge h R β) = constantWedge h' (ddc R) β := by
  ext γ φ
  simp only [ddc_apply_apply, constantWedge, LinearMap.comp_apply, LinearMap.flip_apply]
  simp only [wedgeSpan_wedgeLM h h']

/-- Differentiation of a product by an arbitrary smooth form is reduced
to the genuine smooth scalar coefficients. The form need not be closed. -/
theorem ddc_wedgeForm_coefficients (h : r + 1 + k = m + 1) (h' : r + k = m)
    (R : LocalProductCurrent n U (m + 1))
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) :
    ddc (wedgeForm h R hα) = ∑ i,
      constantWedge h' (ddc (smoothMulCurrent R (contDiffOn_formCoeff hα i)))
        (formBasis n k i) := by
  rw [wedgeForm_eq_sum_constantWedge]
  change ddcLinearMap (∑ i, _) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ddc_constantWedge h h' _ _

/-- For a positive current, smooth multiplication agrees with the actual
coefficient-measure multiplication used in the Bedford--Taylor recursion. -/
theorem smoothMulCurrent_eq_mulBorel_indicator
    {R : LocalProductCurrent n U m} (hR : IsPositive R)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    smoothMulCurrent R hf = mulBorel R ((U : Set (ComplexModel n)).indicator f) := by
  ext γ φ
  change R γ (mulSmoothOnCLM hf φ) = _
  rw [mulBorel_apply hR (measurable_indicator_of_continuousOn hf.continuousOn)
    (isLocallyBoundedOn_indicator_of_continuousOn hf.continuousOn),
    hR.apply_eq_integral_density]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · simp only [mulSmoothOnCLM_apply, indicator_of_mem hx]
    ring
  · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (φ.tsupport_subset h))
    simp only [mulSmoothOnCLM_apply, hφ, zero_mul]

/-- Closedness of the current, rather than of the background coefficient,
moves both derivatives onto a genuine smooth scalar coefficient. -/
theorem ddc_smoothMulCurrent_eq_wedge
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R)
    (hRc : IsClosedCurrent R) {f : ComplexModel n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ddc (smoothMulCurrent R hf) = wedgeForm rfl R (contDiffOn_ddcForm hf) := by
  rw [smoothMulCurrent_eq_mulBorel_indicator hR hf]
  change ddcMul R f = _
  rw [ddcMul_eq_ddcWedge hR hRc hf, ddcWedge_eq_wedgeForm]

/-- The distributional second derivative of a closed positive current
wedged with an arbitrary smooth form is the finite sum of actual smooth
Hessian wedges of its coefficients. This constructs its order-zero
representation without assuming closedness of the smooth form. -/
theorem ddc_wedgeForm_closed_positive (h : r + 1 + k = m + 1) (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) :
    ddc (wedgeForm h R hα) = ∑ i,
      constantWedge h' (wedgeForm rfl R
        (contDiffOn_ddcForm (contDiffOn_formCoeff hα i))) (formBasis n k i) := by
  rw [ddc_wedgeForm_coefficients h h' R hα]
  simp_rw [ddc_smoothMulCurrent_eq_wedge hR hRc]

/-- On each compact coordinate set, differentiating a smooth-form factor
has order zero with respect to the actual trace measure of the closed
positive factor. The bound is chosen before the current and the test. -/
theorem exists_ddc_wedgeForm_compact_bound
    (h : r + 1 + k = m + 1) (h' : r + k = m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (γ : formSpan n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : LocalProductCurrent n U (m + 1))
      (hR : IsPositive R), IsClosedCurrent R → ∀ φ : 𝓓(U, ℝ), tsupport φ ⊆ K →
        |ddc (wedgeForm h R hα) γ φ| ≤ C * ∫ x, |φ x| ∂hR.traceMeasure := by
  classical
  let I := Fin (Module.finrank ℝ (formSpan n k)) × Fin (n * 2) × Fin (n * 2)
  let g : I → ComplexModel n → ℝ := fun i =>
    hessFun i.2.1 i.2.2 (formCoeff α i.1)
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) U := fun i =>
    contDiffOn_hessFun (contDiffOn_formCoeff hα i.1) i.2.1 i.2.2
  choose B₀ hB₀ using fun i : I =>
    hK.exists_bound_of_continuousOn ((hg i).continuousOn.mono hKU)
  let B : I → ℝ := fun i => max (B₀ i) 0
  have hB : ∀ i, 0 ≤ B i := fun i => le_max_right _ _
  have hgb : ∀ i x, x ∈ K → |g i x| ≤ B i := by
    intro i x hx
    have hb : |g i x| ≤ B₀ i := by simpa only [Real.norm_eq_abs] using hB₀ i x hx
    exact hb.trans (le_max_left _ _)
  let β : I → formSpan n (m + 1) := fun i =>
    wedgeLM m (isOneOne_coeffForm i.2.1 i.2.2)
      (wedgeSpan n h' γ (formBasis n k i.1))
  choose D hD hD₁ hD₂ using fun i : I => exists_orderUnit (β i).2
  let C : ℝ := (1 / (4 * Real.pi)) * ∑ i, B i * D i
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hB i) (hD i))
  refine ⟨C, hC, ?_⟩
  intro R hR hRc φ hφK
  have hφint : Integrable (fun x => φ x) hR.traceMeasure := by
    simpa only [mul_one] using hR.integrable_mul_of_bounded φ.continuous
      φ.hasCompactSupport φ.tsupport_subset (w := fun _ => (1 : ℝ))
      aestronglyMeasurable_const ⟨1, fun _ _ => by norm_num⟩
  have hterm : ∀ i : I,
      |R (β i) (mulSmoothOnCLM (hg i) φ)| ≤
        (B i * D i) * ∫ x, |φ x| ∂hR.traceMeasure := by
    intro i
    rw [hR.apply_eq_integral_density]
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hφint.abs.const_mul _)
    filter_upwards [abs_density_le_of_orderUnit hR (β i) (hD₁ i) (hD₂ i)] with x hx
    by_cases hxK : x ∈ K
    · simp only [mulSmoothOnCLM_apply, norm_mul, Real.norm_eq_abs]
      calc |φ x| * |g i x| * |hR.density (β i) x|
          ≤ |φ x| * B i * D i := mul_le_mul
            (mul_le_mul_of_nonneg_left (hgb i x hxK) (abs_nonneg _)) hx
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (hB i))
        _ = B i * D i * |φ x| := by ring
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx => hxK (hφK hx))
      simp only [mulSmoothOnCLM_apply, hφ, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
  have heq : ddc (wedgeForm h R hα) γ φ =
      ∑ i : I, (-(1 / (4 * Real.pi))) *
        R (β i) (mulSmoothOnCLM (hg i) φ) := by
    rw [ddc_wedgeForm_closed_positive h h' hR hRc hα]
    have heval (i : Fin (Module.finrank ℝ (formSpan n k))) :
        constantWedge h' (wedgeForm rfl R
          (contDiffOn_ddcForm (contDiffOn_formCoeff hα i))) (formBasis n k i) γ φ =
        ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
          R (wedgeLM m (isOneOne_coeffForm a b)
            (wedgeSpan n h' γ (formBasis n k i)))
            (mulSmoothOnCLM (contDiffOn_hessFun (contDiffOn_formCoeff hα i) a b) φ) := by
      change wedgeForm rfl R (contDiffOn_ddcForm (contDiffOn_formCoeff hα i))
        (wedgeSpan n h' γ (formBasis n k i)) φ = _
      rw [← ddcWedge_eq_wedgeForm R (contDiffOn_formCoeff hα i), ddcWedge_apply]
    simp only [LinearMap.sum_apply, _root_.sum_apply, heval, I, Fintype.sum_prod_type, β, g]
  calc |ddc (wedgeForm h R hα) γ φ|
      = |∑ i : I, (-(1 / (4 * Real.pi))) *
          R (β i) (mulSmoothOnCLM (hg i) φ)| := congrArg abs heq
    _ ≤ ∑ i : I, (1 / (4 * Real.pi)) *
        ((B i * D i) * ∫ x, |φ x| ∂hR.traceMeasure) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi))]
      exact mul_le_mul_of_nonneg_left (hterm i) (by positivity)
    _ = C * ∫ x, |φ x| ∂hR.traceMeasure := by
      simp only [C, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end SGPT.PSH.HermitianProductDifferential
