import SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
import SGPT.Foundations.Analysis.FirstPass.CurrentPairing

set_option autoImplicit false

/-! # Actual full two-form tests for currents of complementary bidimension one

Blueprint: `bt:actual-bidimension-one-full-test-functional` and its three laws.
The complete mathematical statements and proofs precede this implementation.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.BidimensionOneFullTestFunctional

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorForms ClosedProductCurrents ConstantFormProducts
  LocalBedfordTaylorLocality CompactVariableCurrentTests

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U V : Opens (ComplexModel n)}

private def coefficientTestCLM
    (i : Fin (Module.finrank ℝ (formSpan n 1))) :
    LocalCurrents.TestForm U 2 →L[ℝ] 𝓓(U, ℝ) :=
  TestFunction.postcompCLM ((coeffCLM n 1 i).comp (pi11CLM n))

/-- Canonical full real two-form testing, using the actual `(1,1)` projection. -/
def fullTestFunctional (T : LocalProductCurrent n U 1) :
    LocalCurrents.TestForm U 2 →L[ℝ] ℝ := by
  classical
  exact ∑ i, (T (formBasis n 1 i)).comp (coefficientTestCLM i)

/-- The canonical type projection commutes with every complex-linear pullback. -/
theorem pi11_comp_complexLinear (A : RealForm n 2)
    (S : ComplexModel n →L[ℂ] ComplexModel n) :
    pi11 (A.compContinuousLinearMap (S.restrictScalars ℝ)) =
      (pi11 A).compContinuousLinearMap (S.restrictScalars ℝ) := by
  ext w
  rw [eq_vec_two w]
  simp only [pi11_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ClosedProductCurrents.comp_two]
  change (A ![S (w 0), S (w 1)] + A ![S (Complex.I • w 0), S (Complex.I • w 1)]) / 2 =
    (A ![S (w 0), S (w 1)] + A ![Complex.I • S (w 0), Complex.I • S (w 1)]) / 2
  rw [map_smul, map_smul]

private theorem pi11_formSpan (γ : formSpan n 1) :
    pi11 (γ : RealForm n 2) = γ := by
  apply pi11_eq_self
  intro u v
  have h := formSpan_le_jInvariant 1 γ.property
  have heq := DFunLike.congr_fun h ![u, v]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ClosedProductCurrents.comp_two] at heq
  simpa only [complexJ_apply] using heq

private theorem coefficientTest_constant
    (γ : formSpan n 1) (φ : 𝓓(U, ℝ))
    (i : Fin (Module.finrank ℝ (formSpan n 1))) :
    coefficientTestCLM i (LocalCurrents.constantTestFormCLM (γ : RealForm n 2) φ) =
      (formBasis n 1).repr γ i • φ := by
  ext x
  change coeffCLM n 1 i (pi11 (φ x • (γ : RealForm n 2))) =
    ((formBasis n 1).repr γ i • φ) x
  have hc : coeffCLM n 1 i (γ : RealForm n 2) = (formBasis n 1).repr γ i := by
    change (formBasis n 1).repr (formProj n 1 (γ : RealForm n 2)) i = _
    rw [formProj_coe]
  rw [← pi11CLM_apply, map_smul, pi11CLM_apply, pi11_formSpan,
    map_smul, hc]
  simp only [_root_.smul_apply, smul_eq_mul, mul_comm]

/-- Every original constant form and genuine scalar test retains its exact pairing. -/
theorem fullTestFunctional_constant (T : LocalProductCurrent n U 1)
    (γ : formSpan n 1) (φ : 𝓓(U, ℝ)) :
    fullTestFunctional T (LocalCurrents.constantTestFormCLM (γ : RealForm n 2) φ) =
      T γ φ := by
  classical
  simp only [fullTestFunctional, _root_.sum_apply]
  change (∑ i, T (formBasis n 1 i)
    (coefficientTestCLM i (LocalCurrents.constantTestFormCLM (γ : RealForm n 2) φ))) = T γ φ
  simp only [coefficientTest_constant, map_smul, smul_eq_mul]
  conv_rhs => rw [← (formBasis n 1).sum_repr γ, map_sum, _root_.sum_apply]
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]

/-- The canonical full functional commutes with restriction, on all real two-form tests. -/
theorem fullTestFunctional_restrict (hVU : V ≤ U)
    (T : LocalProductCurrent n U 1) (α : LocalCurrents.TestForm V 2) :
    fullTestFunctional (restrict hVU T) α =
      fullTestFunctional T (TestFunction.monoCLM ℝ α) := by
  classical
  simp only [fullTestFunctional, _root_.sum_apply]
  change (∑ i, restrict hVU T (formBasis n 1 i) (coefficientTestCLM i α)) =
    ∑ i, T (formBasis n 1 i) (coefficientTestCLM i (TestFunction.monoCLM ℝ α))
  simp only [LocalBedfordTaylorLocality.restrict_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext x
  rw [extTest_apply]
  change coeffCLM n 1 i (pi11 (α x)) =
    coeffCLM n 1 i (pi11 ((TestFunction.monoCLM ℝ α : LocalCurrents.TestForm U 2) x))
  have hext : (TestFunction.monoCLM ℝ α : LocalCurrents.TestForm U 2) x = α x := by
    have h := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := U) α
    simpa only [le_refl, hVU, and_self, ↓reduceIte] using congrFun h x
  rw [hext]

end SGPT.Foundations.Analysis.Pending.BidimensionOneFullTestFunctional
