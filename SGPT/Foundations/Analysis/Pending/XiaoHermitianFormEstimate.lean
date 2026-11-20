import SGPT.Foundations.Analysis.Pending.XiaoBadSetEstimate
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison

set_option autoImplicit false

/-!
# Xiao's trace lower bound for actual real (1,1)-forms

The quadratic estimate is transferred through the normalized Hermitian matrix,
including its factor π, to genuine line-value semipositivity of real two-forms.
No bounded potentials, compactness, or positive dimension are needed here.
-/

open Matrix
open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.XiaoHermitianFormEstimate

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  SubmanifoldMassConcentration

/-- A trace bound makes the actual difference of coefficient forms semipositive. -/
theorem coefficientSemipositive_sub_inv_smul {n : ℕ} {A B : RealForm n 2}
    (hA : IsOneOne A) (hB : IsOneOne B)
    (hAp : IsStrictlyPositive A) (hBp : IsStrictlyPositive B) {T : ℝ} (hT : 0 < T)
    (htrace : ((normalizedHermitianMatrix A)⁻¹ * normalizedHermitianMatrix B).trace.re ≤ T) :
    CoefficientSemipositive (A - T⁻¹ • B) := by
  classical
  intro v
  let x : Fin n → ℂ := fun j => star (v j)
  have hv : (∑ j, star (x j) • coordinateVector j : ComplexModel n) = v := by
    ext i
    rw [coord_sum_star_smul_coordinateVector]
    simp only [x, star_star]
  have hq := XiaoBadSetEstimate.quad_div_le_of_trace_le
    (ConcentrationMassComparison.normalizedHermitianMatrix_posDef hA hAp)
    (ConcentrationMassComparison.normalizedHermitianMatrix_posDef hB hBp) hT htrace x
  rw [dotProduct_normalizedHermitianMatrix hB, dotProduct_normalizedHermitianMatrix hA,
    Complex.ofReal_re, Complex.ofReal_re, hv] at hq
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  have hline : B ![v, Complex.I • v] / T ≤ A ![v, Complex.I • v] := by
    apply le_of_mul_le_mul_left (a := Real.pi)
    · simpa only [mul_div_assoc] using hq
    · exact Real.pi_pos
  rw [inv_mul_eq_div]
  exact sub_nonneg.mpr hline

/-- The pointwise trace estimate gives global semipositivity of the actual smooth difference. -/
theorem isSemipositive_sub_inv_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A B : ClosedRealOneOneForm n M) (hA : A.val.IsKahler) (hB : B.val.IsKahler)
    {T : ℝ} (hT : 0 < T)
    (htrace : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      ((normalizedHermitianMatrix (A.val.coeff e z))⁻¹ *
        normalizedHermitianMatrix (B.val.coeff e z)).trace.re ≤ T) :
    (A - T⁻¹ • B).val.IsSemipositive := by
  intro e z hz
  simpa only [CoefficientSemipositive, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul] using
    coefficientSemipositive_sub_inv_smul (A.property.2 e z hz) (B.property.2 e z hz)
      (hA.1 e z hz).2 (hB.1 e z hz).2 hT (htrace e z hz)

end SGPT.Foundations.Analysis.Pending.XiaoHermitianFormEstimate
