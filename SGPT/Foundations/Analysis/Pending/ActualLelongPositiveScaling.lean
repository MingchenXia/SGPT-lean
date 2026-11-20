import SGPT.Foundations.Analysis.Pending.LelongNumberScaling
import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong

set_option autoImplicit false

/-! # Literal positive scaling of the actual logarithmic Lelong exponent -/

open Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling

open FirstPass FirstPass.NonKahlerLocus DemaillyApproximantDivisorialLelong

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [IsComplexManifold n Y] in
/-- Inverse positive coefficients turn the actual proved scaling inequality
into a literal extended-real equality, without any finiteness hypothesis. -/
theorem lelongNumber_smul_eq {u : Y → EReal} {x : Y} {c : ℝ} (hc : 0 < c) :
    lelongNumber (n := n) (fun y => (c : EReal) * u y) x =
      ENNReal.ofReal c * lelongNumber (n := n) u x := by
  apply le_antisymm
  · exact LelongNumberScaling.lelongNumber_smul_le hc
  · have hcancel : (fun y => ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * u y)) = u := by
      funext y
      rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
    have hi := LelongNumberScaling.lelongNumber_smul_le (n := n)
      (u := fun y => (c : EReal) * u y) (x := x) (inv_pos.mpr hc)
    rw [hcancel] at hi
    have hmul : ENNReal.ofReal c * lelongNumber (n := n) u x ≤
        ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ *
          lelongNumber (n := n) (fun y => (c : EReal) * u y) x) := by
      gcongr
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_mul] at hmul
    exact hmul

/-- Finite positive multiplication preserves both point and membership
infima, including the empty-set and infinite generic Lelong values. -/
theorem divisorialLelongNumber_smul_eq {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z]
    {u : Z → EReal} {E : Set Z} {c : ℝ} (hc : 0 < c) :
    divisorialLelongNumber m (fun y => (c : EReal) * u y) E =
      ENNReal.ofReal c * divisorialLelongNumber m u E := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  unfold divisorialLelongNumber
  simp_rw [lelongNumber_smul_eq hc,
    ← ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]

end
end SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
