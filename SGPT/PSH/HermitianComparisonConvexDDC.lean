import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
import SGPT.Foundations.Analysis.Pending.StokesCutoff
import SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
import SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests

/-!
# The positive differential-form defect in convex cutoff comparison

FPT `lem:hermitian-one-factor-comparison`, Step 2, discards the nonnegative
second-derivative term in the convex chain rule. These lemmas identify that
term using the actual real `ddᶜ` two-form and prove its semipositivity.
They do not require a closed background or assert the bounded-potential
integration-by-parts comparison.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonConvexDDC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
open scoped ContDiff Distributions Topology

variable {n : ℕ}

/-- The full two-form scalar chain rule, retaining the actual mixed real
derivatives rather than only its trace. -/
theorem smoothDDC_comp_apply {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    {z : ComplexModel n} (hF : ContDiffAt ℝ 2 F (w z))
    (hw : ContDiffAt ℝ 2 w z) (v₁ v₂ : ComplexModel n) :
    smoothDDC (fun y => F (w y)) z ![v₁, v₂] =
      deriv F (w z) * smoothDDC w z ![v₁, v₂] +
        deriv (deriv F) (w z) *
          (fderiv ℝ w z v₂ * fderiv ℝ w z (Complex.I • v₁) -
            fderiv ℝ w z v₁ * fderiv ℝ w z (Complex.I • v₂)) / (4 * Real.pi) := by
  rw [smoothDDC_apply_eq_realHessian (u := fun y => F (w y)) (hF.comp z hw),
    smoothDDC_apply_eq_realHessian hw,
    StokesCutoff.realHessian_comp hF hw,
    StokesCutoff.realHessian_comp hF hw]
  ring

/-- The exact squared-gradient defect on every complex tangent line. -/
theorem convex_ddc_defect_complexDiagonal {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    {z : ComplexModel n} (hF : ContDiffAt ℝ 2 F (w z))
    (hw : ContDiffAt ℝ 2 w z) (v : ComplexModel n) :
    (smoothDDC (fun y => F (w y)) z - deriv F (w z) • smoothDDC w z)
        ![v, Complex.I • v] =
      deriv (deriv F) (w z) *
        (fderiv ℝ w z v ^ 2 + fderiv ℝ w z (Complex.I • v) ^ 2) / (4 * Real.pi) := by
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  rw [smoothDDC_comp_apply hF hw]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  ring

/-- Convex composition adds an actual semipositive `(1,1)`-form to the
first-derivative multiple of `ddᶜw`, even for a changing-sign `w`. -/
theorem isSemipositiveOneOne_convex_ddc_defect
    {F : ℝ → ℝ} {w : ComplexModel n → ℝ} {z : ComplexModel n}
    (hF : ContDiffAt ℝ 2 F (w z)) (hw : ContDiffAt ℝ 2 w z)
    (hF₂ : 0 ≤ deriv (deriv F) (w z)) :
    IsSemipositiveOneOne
      (smoothDDC (fun y => F (w y)) z - deriv F (w z) • smoothDDC w z) := by
  refine ⟨?_, ?_⟩
  · intro v₁ v₂
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smoothDDC_isOneOne (u := fun y => F (w y)) (hF.comp z hw), smoothDDC_isOneOne hw]
  · intro v
    rw [convex_ddc_defect_complexDiagonal hF hw]
    exact div_nonneg (mul_nonneg hF₂ (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (mul_nonneg (by norm_num) Real.pi_pos.le)

/-- The genuine second differential of a globally smooth real function is smooth. -/
theorem contDiff_smoothDDC {w : ComplexModel n → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (smoothDDC w) := by
  have hdc : ContDiff ℝ ∞ (smoothDc w) := by
    simpa only [contDiffOn_univ] using smoothDc_contDiffOn isOpen_univ hw.contDiffOn
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).contDiff.comp
    (hdc.fderiv_right (m := ∞) (by simp))

/-- The actual nonnegative chain-rule defect, multiplied by one compact scalar
test, is a genuine compact variable two-form test on the same open set. -/
def convexDefectTest {U : TopologicalSpace.Opens (ComplexModel n)}
    (φ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) : 𝓓(U, RealForm n (2 * 1)) := by
  have hderiv : ContDiff ℝ ∞ (deriv F) := by
    change ContDiff ℝ ∞ (fun t => fderiv ℝ F t 1)
    exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let A : ComplexModel n → RealForm n 2 := fun z =>
    smoothDDC (fun y => F (w y)) z - deriv F (w z) • smoothDDC w z
  have hA : ContDiff ℝ ∞ A := (contDiff_smoothDDC (hF.comp hw)).sub
    ((hderiv.comp hw).smul (contDiff_smoothDDC hw))
  exact ⟨fun z => φ z • A z, φ.contDiff.smul hA, φ.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans φ.tsupport_subset⟩

@[simp] theorem convexDefectTest_apply {U : TopologicalSpace.Opens (ComplexModel n)}
    (φ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) (z : ComplexModel n) :
    convexDefectTest φ F w hF hw z =
      φ z • (smoothDDC (fun y => F (w y)) z - deriv F (w z) • smoothDDC w z) := rfl

/-- Every genuine positive current of bidimension `(1,1)` pairs nonnegatively
with the actual convex chain-rule defect. Closedness of the current is not a
hypothesis: this is the positive term discarded in Hermitian comparison. -/
theorem convex_defect_pairing_nonnegative
    {U : TopologicalSpace.Opens (ComplexModel n)}
    (S : LocalProductCurrent n U 1) (hS : IsPositive S)
    (φ : 𝓓(U, ℝ)) (hφ : ∀ z, 0 ≤ φ z)
    {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w)
    (hF₂ : ∀ z, 0 ≤ deriv (deriv F) (w z)) :
    0 ≤ ∑ i, S (formBasis n 1 i) (coeffTest (convexDefectTest φ F w hF hw) i) := by
  apply pairing_nonnegative S hS
  intro z
  rw [convexDefectTest_apply]
  exact smul_mem_spCone (mem_spCone_one
    (isSemipositiveOneOne_convex_ddc_defect
      (hF.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hw.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hF₂ z))) (hφ z)

end SGPT.PSH.HermitianComparisonConvexDDC
