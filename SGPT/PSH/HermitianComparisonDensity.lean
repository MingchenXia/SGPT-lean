import SGPT.PSH.HermitianProductDifferential

/-!
# Actual order-zero differential pairings with bounded Borel weights

The nonclosed smooth factor is differentiated through its genuine finite
coefficient Hessians. Each resulting coefficient is integrated against the
actual trace measure of the closed positive factor. This gives an explicit
bounded-weight extension and dominated convergence, without an assumed
derivative measure or a desired comparison inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonDensity

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.PSH.HermitianProductDifferential
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n r k m : ℕ} {U : Opens (ComplexModel n)}

private abbrev CoeffIndex (n k : ℕ) :=
  Fin (Module.finrank ℝ (formSpan n k)) × Fin (n * 2) × Fin (n * 2)

private def coeffHessian (α : ComplexModel n → RealForm n (2 * k))
    (i : CoeffIndex n k) : ComplexModel n → ℝ :=
  hessFun i.2.1 i.2.2 (formCoeff α i.1)

private def coeffForm (h' : r + k = m) (γ : formSpan n r)
    (i : CoeffIndex n k) : formSpan n (m + 1) :=
  wedgeLM m (isOneOne_coeffForm i.2.1 i.2.2)
    (wedgeSpan n h' γ (formBasis n k i.1))

/-- The explicit extension of the differentiated smooth wedge to a bounded
Borel scalar weight. It uses actual Hessians and actual coefficient densities. -/
def ddcWedgePairing (h' : r + k = m) {R : LocalProductCurrent n U (m + 1)}
    (hR : IsPositive R) (α : ComplexModel n → RealForm n (2 * k))
    (γ : formSpan n r) (φ : 𝓓(U, ℝ)) (f : ComplexModel n → ℝ) : ℝ :=
  ∑ i : CoeffIndex n k, (-(1 / (4 * Real.pi))) *
    ∫ x, f x * (φ x * ((U : Set (ComplexModel n)).indicator (coeffHessian α i) x *
      hR.density (coeffForm h' γ i) x)) ∂hR.traceMeasure

/-- The actual derivative has the complete finite coefficient-Hessian formula. -/
theorem ddc_wedgeForm_apply_eq_hessian_sum
    (h : r + 1 + k = m + 1) (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R) (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    ddc (wedgeForm h R hα) γ φ =
      ∑ i : CoeffIndex n k, (-(1 / (4 * Real.pi))) *
        R (coeffForm h' γ i) (mulSmoothOnCLM
          (contDiffOn_hessFun (contDiffOn_formCoeff hα i.1) i.2.1 i.2.2) φ) := by
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
  simp only [LinearMap.sum_apply, _root_.sum_apply, heval, CoeffIndex,
    Fintype.sum_prod_type, coeffForm]

/-- Smooth scalar weights recover the SAME original distributional derivative,
including every nonclosed coefficient of the residual form. -/
theorem ddc_wedgeForm_smooth_weight_eq
    (h : r + 1 + k = m + 1) (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R) (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (γ : formSpan n r) (φ : 𝓓(U, ℝ)) {f : ComplexModel n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ddc (wedgeForm h R hα) γ (mulSmoothOnCLM hf φ) =
      ddcWedgePairing h' hR α γ φ f := by
  rw [ddc_wedgeForm_apply_eq_hessian_sum h h' hR hRc hα]
  unfold ddcWedgePairing
  apply Finset.sum_congr rfl
  intro i _
  rw [hR.apply_eq_integral_density]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [mulSmoothOnCLM_apply]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
    dsimp [coeffHessian]
    ring
  · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (φ.tsupport_subset hs))
    simp only [hφ, zero_mul, mul_zero]

/-- The actual finite Hessian-density extension obeys dominated convergence
for bounded Borel weights. There is no assumed order-zero representation:
the trace densities are produced from the closed positive factor itself. -/
theorem ddcWedgePairing_tendsto (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (γ : formSpan n r) (φ : 𝓓(U, ℝ))
    {f : ℕ → ComplexModel n → ℝ} {f₀ : ComplexModel n → ℝ}
    (hf : ∀ j, Measurable (f j))
    (hlim : ∀ x ∈ U, Tendsto (fun j => f j x) atTop (𝓝 (f₀ x)))
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ j x, x ∈ tsupport φ → |f j x| ≤ M) :
    Tendsto (fun j => ddcWedgePairing h' hR α γ φ (f j)) atTop
      (𝓝 (ddcWedgePairing h' hR α γ φ f₀)) := by
  unfold ddcWedgePairing
  apply tendsto_finsetSum
  intro i _
  apply Filter.Tendsto.const_mul
  have hg : ContDiffOn ℝ ∞ (coeffHessian α i) U :=
    contDiffOn_hessFun (contDiffOn_formCoeff hα i.1) i.2.1 i.2.2
  let g : ComplexModel n → ℝ := (U : Set (ComplexModel n)).indicator (coeffHessian α i)
  have hgm : Measurable g := measurable_indicator_of_continuousOn hg.continuousOn
  have hgb : IsLocallyBoundedOn g U := isLocallyBoundedOn_indicator_of_continuousOn hg.continuousOn
  have hbase := hR.integrable_mul_density hgm hgb (coeffForm h' γ i) φ
  obtain ⟨M, hM, hMf⟩ := hbound
  apply tendsto_integral_of_dominated_convergence
    (fun x => M * |φ x * (g x * hR.density (coeffForm h' γ i) x)|)
  · intro j
    exact ((hf j).mul (φ.continuous.measurable.mul
      (hgm.mul (hR.measurable_density _)))).aestronglyMeasurable
  · exact hbase.abs.const_mul M
  · intro j
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hMf j x hx) (by positivity)
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hφ, zero_mul, mul_zero, norm_zero, abs_zero, le_refl]
  · filter_upwards [] with x
    by_cases hx : x ∈ U
    · exact (hlim x hx).mul tendsto_const_nhds
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hx (φ.tsupport_subset hs))
      simpa only [hφ, zero_mul, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end SGPT.PSH.HermitianComparisonDensity
