import SGPT.PSH.HermitianProducts

/-!
# The normalized Euclidean slot in bounded current products

For the source normalization `ddc = (i / 2π) ∂∂bar`, the function
`π‖z‖²` has `ddc` equal to the standard Euclidean Hermitian form. Its
degree-one Bedford--Taylor slot is therefore exactly the trace of the
remaining positive closed current.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCollar LocalBedfordTaylorLocality ConstantFormProducts
  CoordinateWedgeAssoc
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The quadratic potential whose `ddc` is the Euclidean Hermitian form. -/
def flatQuadratic (z : ComplexModel n) : ℝ := Real.pi * ‖z‖ ^ 2

theorem contDiff_flatQuadratic : ContDiff ℝ ∞ (flatQuadratic (n := n)) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

/-- Exact normalization of the quadratic, in every dimension including zero. -/
theorem smoothDDC_flatQuadratic (z : ComplexModel n) :
    smoothDDC flatQuadratic z = kahlerForm n := by
  have hsmul := smoothDDC_smul
    (h := fun y : ComplexModel n => ‖y‖ ^ 2) isOpen_univ
    (contDiff_norm_sq ℝ).contDiffOn Real.pi (mem_univ z)
  have hflat : smoothDDC flatQuadratic z =
      Real.pi • smoothDDC (fun y : ComplexModel n => ‖y‖ ^ 2) z := by
    have hfun : (flatQuadratic (n := n)) =
        (fun y : ComplexModel n => Real.pi * ‖y‖ ^ 2) := rfl
    rw [hfun]
    simpa only [smul_eq_mul] using hsmul
  have hnorm : smoothDDC (fun y : ComplexModel n => ‖y‖ ^ 2) z =
      Real.pi⁻¹ • kahlerForm n := by
    simpa only [sub_zero] using smoothDDC_norm_sub_sq (0 : ComplexModel n) z
  rw [hflat, hnorm, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]

private theorem kahlerPower_one_coe :
    ((kahlerPower n 1 : formSpan n 1) : RealForm n 2) = kahlerForm n := by
  change coordinateWedge (coordinateWedgeUnit : RealForm n 0) (kahlerForm n) = _
  rw [coordinateWedge_unit_left]
  rfl

/-- A normalized flat quadratic slot is the literal trace pairing of the
remaining positive closed current of bidimension one. -/
theorem ddcMul_flatQuadratic_trace {R : LocalProductCurrent n U 1}
    (hR : IsPositive R) (hRc : IsClosedCurrent R) (χ : 𝓓(U, ℝ)) :
    ddcMul R flatQuadratic (kahlerPower n 0) χ = R (kahlerPower n 1) χ := by
  have hq : ContDiffOn ℝ ∞ (flatQuadratic (n := n)) U := contDiff_flatQuadratic.contDiffOn
  rw [ddcMul_eq_ddcWedge hR hRc hq, ddcWedge_eq_wedgeForm]
  rw [wedgeForm_apply_eq rfl R (contDiffOn_ddcForm hq)
    (fun z _ => by
      rw [ddcForm, smoothDDC_flatQuadratic]
      exact oneOne_mem_formSpan (flatFundamentalForm_isOneOne n))
    (fun _ : Unit => fun _ : ComplexModel n => (1 : ℝ))
    (fun _ => contDiffOn_const) (fun _ => kahlerPower n 1)
    (fun z _ => by
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul,
        ddcForm, smoothDDC_flatQuadratic]
      exact kahlerPower_one_coe.symm)]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hform : wedgeSpan n rfl (kahlerPower n 0) (kahlerPower n 1) = kahlerPower n 1 := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply rfl _ _ (by omega)]
    change wedgeTo (by omega : 0 + 2 = 2)
      (coordinateWedgeUnit : RealForm n 0) ((kahlerPower n 1 : formSpan n 1) : RealForm n 2) = _
    rw [wedgeTo_unit_left (by omega) rfl]
    rfl
  have htest : mulSmoothOnCLM (contDiffOn_const (c := (1 : ℝ))) χ = χ := by
    ext z
    simp only [mulSmoothOnCLM_apply, mul_one]
  rw [hform, htest]

end SGPT.PSH.HermitianProducts
