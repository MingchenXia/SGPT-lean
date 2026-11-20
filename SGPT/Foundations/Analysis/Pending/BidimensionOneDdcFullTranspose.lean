import SGPT.Foundations.Analysis.Pending.BidimensionOneFullTestFunctional
import SGPT.Foundations.Analysis.Pending.CompactDifferentialTests

set_option autoImplicit false

/-!
# Full local ddᶜ transposition in complementary bidimension one

The canonical full-test functional and distributional ddᶜ agree on every compact
real zero-form test. The current is arbitrary and signed; the proof uses the
literal coordinate normalization and requires neither positivity nor closedness.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.BidimensionOneDdcFullTranspose

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts ConstantFormProducts BidimensionOneFullTestFunctional
  CompactDifferentialTests _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem dTest_twice_eq_hessFun
    (φ : 𝓓(U, ℝ)) (a b : Fin (n * 2)) (x : ComplexModel n) :
    dTest (realBasis n b) (dTest (realBasis n a) φ) x =
      hessFun b a (φ : ComplexModel n → ℝ) x := by
  rw [dTest_apply]
  have hfirst :
      (dTest (realBasis n a) φ : ComplexModel n → ℝ) =
        dFun (realBasis n a) (φ : ComplexModel n → ℝ) :=
    funext (dTest_apply (realBasis n a) φ)
  rw [hfirst]
  rfl

/-- A full compact-test equality, before applying any current. -/
private theorem localDdc_unit_expansion (φ : 𝓓(U, ℝ)) :
    localDdcTestCLM
        (constantTestFormCLM (coordinateWedgeUnit : RealForm n 0) φ) =
      ∑ a : Fin (n * 2), ∑ b : Fin (n * 2),
        (-(1 / (4 * Real.pi))) •
          constantTestFormCLM (coeffForm a b)
            (dTest (realBasis n b) (dTest (realBasis n a) φ)) := by
  classical
  apply TestFunction.ext
  intro x
  have hu := localDdcTestCLM_constForm_apply φ (kahlerPower n 0) x
  change localDdcTestCLM
      (constantTestFormCLM (coordinateWedgeUnit : RealForm n 0) φ) x =
    wedgeTo (by omega : 2 + 2 * 0 = 2 * 0 + 1 + 1)
      (smoothDDC φ x) (coordinateWedgeUnit : RealForm n 0) at hu
  rw [wedgeTo_unit_right _ rfl, castForm_self] at hu
  rw [hu]
  simp only [_root_.sum_apply, _root_.smul_apply,
    constantTestFormCLM_apply, smul_smul]
  have hφ : ContDiffAt ℝ 2 (φ : ComplexModel n → ℝ) x :=
    φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [smoothDDC_eq_sum hφ]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hessFun_apply φ.contDiff b a x,
    ← dTest_twice_eq_hessFun φ a b x, coeffForm_comm b a]

/-- Literal local ddᶜ transposition for an arbitrary signed bidimension-one current. -/
private theorem fullTestFunctional_localDdc_scalar
    (S : LocalProductCurrent n U 1) (φ : 𝓓(U, ℝ)) :
    fullTestFunctional S
        (localDdcTestCLM
          (constantTestFormCLM (coordinateWedgeUnit : RealForm n 0) φ)) =
      ddc S (kahlerPower n 0) φ := by
  classical
  have hw (a b : Fin (n * 2)) :
      (wedgeLM 0 (isOneOne_coeffForm a b) (kahlerPower n 0) : RealForm n 2) =
        coeffForm a b := by
    rw [coe_wedgeLM_apply]
    change coordinateWedge (coordinateWedgeUnit : RealForm n 0) (coeffForm a b) =
      coeffForm a b
    exact coordinateWedge_unit_eq _
  have hp (a b : Fin (n * 2)) (ψ : 𝓓(U, ℝ)) :
      fullTestFunctional S (constantTestFormCLM (coeffForm a b) ψ) =
        S (wedgeLM 0 (isOneOne_coeffForm a b) (kahlerPower n 0)) ψ := by
    simpa only [hw a b] using
      fullTestFunctional_constant S
        (wedgeLM 0 (isOneOne_coeffForm a b) (kahlerPower n 0)) ψ
  rw [localDdc_unit_expansion]
  simp only [map_sum, map_smul, smul_eq_mul, hp]
  exact (ddc_apply_apply S (kahlerPower n 0) φ).symm

/-- Every genuine real zero-form test is reconstructed by its actual empty coefficient. -/
private theorem zero_test_reconstruct (α : TestForm U 0) :
    constantTestFormCLM (coordinateWedgeUnit : RealForm n 0)
      (testCoefficientCLM (fun i : Fin 0 => Fin.elim0 i) α) = α := by
  ext x v
  rw [constantTestFormCLM_apply, ContinuousAlternatingMap.smul_apply,
    testCoefficientCLM_apply]
  change α x (fun i : Fin 0 => Fin.elim0 i) * 1 = α x v
  rw [mul_one]
  have hv : (fun i : Fin 0 => Fin.elim0 i) = v := by
    funext i
    exact i.elim0
  rw [hv]

/-- The same identity on ALL genuine compact real zero-form tests, without an input certificate. -/
theorem fullTestFunctional_localDdc
    (S : LocalProductCurrent n U 1) (α : TestForm U 0) :
    fullTestFunctional S (localDdcTestCLM α) =
      ddc S (kahlerPower n 0)
        (testCoefficientCLM (fun i : Fin 0 => Fin.elim0 i) α) := by
  calc
    fullTestFunctional S (localDdcTestCLM α) =
        fullTestFunctional S (localDdcTestCLM
          (constantTestFormCLM (coordinateWedgeUnit : RealForm n 0)
            (testCoefficientCLM (fun i : Fin 0 => Fin.elim0 i) α))) :=
      congrArg (fun β => fullTestFunctional S (localDdcTestCLM β))
        (zero_test_reconstruct α).symm
    _ = _ := fullTestFunctional_localDdc_scalar S
      (testCoefficientCLM (fun i : Fin 0 => Fin.elim0 i) α)

end SGPT.Foundations.Analysis.Pending.BidimensionOneDdcFullTranspose
