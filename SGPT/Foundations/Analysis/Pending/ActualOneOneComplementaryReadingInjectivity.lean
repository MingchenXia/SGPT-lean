import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix

set_option autoImplicit false

/-! # Recovery of the actual type-(1,1) distribution coefficients

The complete complementary reading will determine the actual
distribution-valued two-form, without a positivity assumption.
-/

noncomputable section
open Set TopologicalSpace
open scoped Distributions
namespace SGPT.Foundations.Analysis.Pending.ActualOneOneComplementaryReadingInjectivity
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentPullbackDdc ActualDistributionTwoFormReading
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem testedTwoForm_isOneOne {A : DistributionForm U 2}
    (hA : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne A)
    (φ : 𝓓(U, ℝ)) : FirstPass.IsOneOne (testedTwoForm A φ) := by
  intro v w
  rw [testedTwoForm_apply, testedTwoForm_apply]
  exact congrArg (fun T : 𝓓'(U, ℝ) => T φ) (hA v w)

/-- Equality of the entire complementary readings recovers every actual
type-(1,1) distribution coefficient, without a positivity assumption. -/
theorem eq_of_complementaryRead_eq {A B : DistributionForm U 2}
    (hA : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne A)
    (hB : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne B)
    (hread : complementaryRead A = complementaryRead B) : A = B := by
  have hform (φ : 𝓓(U, ℝ)) : testedTwoForm A φ = testedTwoForm B φ := by
    apply LocalCurrentDensityMatrix.eq_of_forall_topDensity_eq
      (testedTwoForm_isOneOne hA φ) (testedTwoForm_isOneOne hB φ)
    intro γ
    have h := congrArg (fun T : LocalProductCurrent (m + 1) U m => T γ φ) hread
    simpa only [complementaryRead_apply, formDensity_apply] using h
  apply AlternatingMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro φ
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hval : A ![v 0, v 1] φ = B ![v 0, v 1] φ := by
    simpa only [testedTwoForm_apply] using
      congrArg (fun α : RealForm (m + 1) 2 => α ![v 0, v 1]) (hform φ)
  exact (congrArg (fun w => A w φ) hv).trans
    (hval.trans (congrArg (fun w => B w φ) hv).symm)

end SGPT.Foundations.Analysis.Pending.ActualOneOneComplementaryReadingInjectivity
