import SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse
import SGPT.Foundations.Analysis.Pending.OneOneFormMixedTrace
import SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity

set_option autoImplicit false

/-! # Actual standard Kähler trace pairing of the native scalar differential

Exterior density, the genuine full-test transpose and coordinate quarter-Levi
operators internally produce every normalization factor.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Module
open scoped Topology Distributions ContDiff InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualScalarCurrentKahlerTracePairing
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts ScalarLeviPositiveCurrent CompactVariableCurrentTests
  LocalCurrentLebesgue LocalBedfordTaylorForms LocalBedfordTaylorCollar
  CompactDifferentialTests CompactDdcCoordinateExpansion ScalarFullTestTranspose
  OneOneFormMixedTrace TopDegreeDensity XiaoPoissonLeviPositivity ConstantFormProducts

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem norm_power_ddc_density (φ : 𝓓(U, ℝ)) (x : ComplexModel (m + 1)) :
    topDensity (coordinateWedge
      (formPower (smoothDDC (fun z : ComplexModel (m + 1) => ‖z‖ ^ 2) 0) m)
      (smoothDDC φ x)) =
      (m.factorial : ℝ) / Real.pi ^ (m + 1) *
        ∑ j, leviForm φ x (coordinateVector j) := by
  have hφ : ContDiffAt ℝ 2 φ x := φ.contDiff.contDiffAt.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hn : ContDiffAt ℝ 2 (fun z : ComplexModel (m + 1) => ‖z‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  rw [topDensity_wedge_formPower _ _ (smoothDDC_isOneOne hφ) (smoothDDC_isOneOne hn),
    normalizedHermitianMatrix_smoothDDC hφ, normalizedHermitianMatrix_smoothDDC hn,
    complexHessian_norm_sq, Matrix.adjugate_one, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, complexHessian_diagonal_re]
  ring

private theorem constant_full_test_pairing {n q : ℕ} {A : Opens (ComplexModel n)}
    (C : LocalProductCurrent n A q) (γ : formSpan n q) (φ : 𝓓(A, ℝ)) :
    let α : 𝓓(A, RealForm n (2 * q)) := TestFunction.postcompCLM
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (γ : RealForm n (2 * q))) φ
    (∑ i, C (formBasis n q i) (coeffTest α i)) = C γ φ := by
  classical
  intro α
  have hspan (x : ComplexModel n) : α x ∈ formSpan n q :=
    (formSpan n q).smul_mem (φ x) γ.property
  have hs := sum_apply_eq_of_forall C (formBasis n q) (coeffTest α)
    (fun _ : Unit => γ) (fun _ : Unit => φ) (fun x _ => by
      rw [← eq_sum_coeffTest α hspan x]
      simp only [Fintype.sum_unique]
      rfl)
  simpa only [Fintype.sum_unique] using hs

/-- Literal native standard Kähler trace pairing, with every factorial and
pi factor internally produced from actual exterior density and compact tests. -/
theorem ddc_scalarTopCurrent_kahlerPower_eq_sum_levi
    (T : 𝓓'(U, ℝ)) (φ : 𝓓(U, ℝ)) :
    ddc (scalarTopCurrent T) (kahlerPower (m + 1) m) φ =
      (m.factorial : ℝ) / Real.pi *
        ∑ j, distributionalLeviCLM (coordinateVector j) T φ := by
  classical
  let γ : formSpan (m + 1) m := (Real.pi⁻¹) ^ m • kahlerPower (m + 1) m
  have hγ : (γ : RealForm (m + 1) (2 * m)) =
      formPower (smoothDDC (fun z : ComplexModel (m + 1) => ‖z‖ ^ 2) 0) m := by
    change (Real.pi⁻¹) ^ m • formPower (kahlerForm (m + 1)) m = _
    simpa only [sub_zero] using
      (formPower_smoothDDC_norm_sub_sq (0 : ComplexModel (m + 1)) 0 m).symm
  let α : 𝓓(U, RealForm (m + 1) (2 * m)) := TestFunction.postcompCLM
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (γ : RealForm (m + 1) (2 * m))) φ
  have hspan (x : ComplexModel (m + 1)) : α x ∈ formSpan (m + 1) m :=
    (formSpan (m + 1) m).smul_mem (φ x) γ.property
  let c : ℝ := (m.factorial : ℝ) / Real.pi ^ (m + 1)
  have hadj : scalarAdjointTest α = c • ∑ j, testLeviCLM (coordinateVector j) φ := by
    ext x
    rw [scalarAdjointTest_apply_eq_actual_density α hspan x]
    change topDensity (castForm _ (localDdcTestCLM
      (TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (γ : RealForm (m + 1) (2 * m))) φ) x)) = _
    rw [localDdcTestCLM_constForm_apply,
      castForm_wedgeTo _ _ (by omega : 2 + 2 * m = 2 * (m + 1))]
    rw [← wedgeTo_comm_of_mem_formSpan γ.property (smoothDDC φ x)
      (rfl : 2 * m + 2 = 2 * (m + 1)) (by omega)]
    change topDensity (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (smoothDDC φ x)) = _
    rw [hγ, norm_power_ddc_density]
    simp only [_root_.smul_apply, _root_.sum_apply, testLeviCLM_apply, smul_eq_mul, c]
  have hp : ddc (scalarTopCurrent T) γ φ =
      c * ∑ j, distributionalLeviCLM (coordinateVector j) T φ := by
    rw [← constant_full_test_pairing (ddc (scalarTopCurrent T)) γ φ,
      ddc_scalarTopCurrent_full_test_transpose]
    change T (scalarAdjointTest α) = _
    rw [hadj, map_smul, map_sum, smul_eq_mul]
    simp only [← distributionalLeviCLM_eq_testLevi]
  change ddc (scalarTopCurrent T) ((Real.pi⁻¹) ^ m • kahlerPower (m + 1) m) φ = _ at hp
  rw [map_smul, _root_.smul_apply, smul_eq_mul] at hp
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    ddc (scalarTopCurrent T) (kahlerPower (m + 1) m) φ =
        Real.pi ^ m * ((Real.pi⁻¹) ^ m *
          ddc (scalarTopCurrent T) (kahlerPower (m + 1) m) φ) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_mul]
    _ = Real.pi ^ m * (c * ∑ j, distributionalLeviCLM (coordinateVector j) T φ) := by rw [hp]
    _ = _ := by
      dsimp [c]
      rw [pow_succ]
      field_simp

end SGPT.Foundations.Analysis.Pending.ActualScalarCurrentKahlerTracePairing
