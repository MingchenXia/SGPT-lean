import SGPT.Foundations.Analysis.Pending.ProductTestForms
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.CurveWeightedClosedForms

open FirstPass FirstPass.MongeAmpere ProductTestForms TopDegreeDensity StronglyPositiveForms

noncomputable section

/-- Genuine alternating tensors vanish above the actual real model dimension. -/
theorem realForm_eq_zero_of_degree_gt {n k : ℕ} (hk : 2 * n < k)
    (a : RealForm n k) : a = 0 := by
  ext v
  have hdep : ¬LinearIndependent ℝ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis (topBasis n), Fintype.card_fin, Fintype.card_fin] at hcard
    omega
  exact a.toAlternatingMap.map_linearDependent v hdep

/-- Actual exterior differentiation makes top-degree forms closed internally. -/
theorem smoothRealForm_isClosed_of_topDegree {n k : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (hk : 2 * n ≤ k) (a : SmoothRealForm n M k) : a.IsClosed := by
  intro e z _
  exact realForm_eq_zero_of_degree_gt (by omega) (extDeriv (a.coeff e) z)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M]

/-- A chart-smooth coefficient weight gives an actual closed curve background;
closedness follows from real dimension two, without a differential certificate. -/
def curveWeightedClosedForm (h : M → ℝ) (hh : ChartSmooth (n := 1) h)
    (α : ClosedRealOneOneForm 1 M) : ClosedRealOneOneForm 1 M := by
  refine ⟨smulFun h hh α.val, smoothRealForm_isClosed_of_topDegree (by omega) _, ?_⟩
  intro e z hz v w
  change (h (e.val.symm z) • α.val.coeff e z) ![Complex.I • v, Complex.I • w] =
    (h (e.val.symm z) • α.val.coeff e z) ![v, w]
  simp only [ContinuousAlternatingMap.smul_apply, α.property.2 e z hz v w]

@[simp] theorem curveWeightedClosedForm_coeff (h : M → ℝ)
    (hh : ChartSmooth (n := 1) h) (α : ClosedRealOneOneForm 1 M)
    (e : ComplexChart 1 M) (z : ComplexModel 1) :
    (curveWeightedClosedForm h hh α).val.coeff e z =
      h (e.val.symm z) • α.val.coeff e z := rfl

/-- Actual nonnegative weighting preserves every complex-line evaluation. -/
theorem curveWeightedClosedForm_isSemipositive {h : M → ℝ}
    (hh : ChartSmooth (n := 1) h) (h0 : ∀ x, 0 ≤ h x)
    {α : ClosedRealOneOneForm 1 M} (hα : α.val.IsSemipositive) :
    (curveWeightedClosedForm h hh α).val.IsSemipositive := by
  intro e z hz v
  rw [curveWeightedClosedForm_coeff, ContinuousAlternatingMap.smul_apply]
  exact mul_nonneg (h0 _) (hα e z hz v)

/-- The actual background coefficient vanishes wherever its scalar weight does. -/
theorem curveWeightedClosedForm_coeff_eq_zero (h : M → ℝ)
    (hh : ChartSmooth (n := 1) h) (α : ClosedRealOneOneForm 1 M)
    (e : ComplexChart 1 M) (z : ComplexModel 1) (hz : h (e.val.symm z) = 0) :
    (curveWeightedClosedForm h hh α).val.coeff e z = 0 := by
  rw [curveWeightedClosedForm_coeff, hz, zero_smul]

end

end SGPT.Foundations.Analysis.Pending.CurveWeightedClosedForms
