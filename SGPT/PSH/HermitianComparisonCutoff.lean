import SGPT.PSH.HermitianComparisonConvexDDC
import SGPT.PSH.HermitianComparisonTranspose

/-!
# Localized smooth convex-cutoff comparison for nonclosed currents

The current is positive but need not be closed. The proof keeps the genuine
compact test `χ F(w)`, moves its full `ddᶜ` to the current, and explicitly
retains the cutoff-error test `ddᶜ(χ F(w)) - χ ddᶜF(w)`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonCutoff

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
open SGPT.PSH.HermitianComparisonConvexDDC SGPT.PSH.HermitianComparisonTranspose
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

/-- The actual full compact-form pairing in the fixed coefficient basis. -/
def pairing (S : LocalProductCurrent n U q) (α : 𝓓(U, RealForm n (2 * q))) : ℝ :=
  ∑ i, S (formBasis n q i) (coeffTest α i)

theorem pairing_sub (S : LocalProductCurrent n U q)
    (α β : 𝓓(U, RealForm n (2 * q))) :
    pairing S (α - β) = pairing S α - pairing S β := by
  simp only [pairing, coeffTest, map_sub, Finset.sum_sub_distrib]

/-- A scalar test regarded as its literal compact zero-form. -/
def scalarTest (ψ : 𝓓(U, ℝ)) : 𝓓(U, RealForm n (2 * 0)) :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight
    (coordinateWedgeUnit : RealForm n 0)) ψ

theorem scalarTest_mem_formSpan (ψ : 𝓓(U, ℝ)) (z : ComplexModel n) :
    scalarTest ψ z ∈ formSpan n 0 :=
  (formSpan n 0).smul_mem (ψ z) (mem_formSpan_of_mem_spCone (unit_mem_spCone (n := n)))

/-- The actual unit zero-form, as an element of the current's type span. -/
def scalarUnit : formSpan n 0 :=
  ⟨coordinateWedgeUnit, mem_formSpan_of_mem_spCone (unit_mem_spCone (n := n))⟩

/-- The full zero-form pairing is the literal scalar current test. -/
theorem pairing_scalarTest (S : LocalProductCurrent n U 0) (ψ : 𝓓(U, ℝ)) :
    pairing S (scalarTest ψ) = S scalarUnit ψ := by
  have h := sum_apply_eq_of_forall S (formBasis n 0) (coeffTest (scalarTest ψ))
    (fun _ : Fin 1 => scalarUnit) (fun _ => ψ) (fun z _ => by
      rw [← eq_sum_coeffTest (scalarTest ψ) (scalarTest_mem_formSpan ψ) z]
      simp only [Fin.sum_univ_one, scalarTest, TestFunction.postcompCLM_apply,
        Function.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, scalarUnit])
  simpa only [pairing, Fin.sum_univ_one] using h

/-- Full compact transposition, retaining the actual nonclosed derivative. -/
theorem pairing_ddc_scalarTest (S : LocalProductCurrent n U 1) (ψ : 𝓓(U, ℝ)) :
    pairing (ddc S) (scalarTest ψ) = pairing S (ddcFullTest (scalarTest ψ)) :=
  ddc_full_test_transpose S (scalarTest ψ) (scalarTest_mem_formSpan ψ)

/-- Multiplication of a globally smooth two-form field by a genuine scalar
test internally produces a compact full two-form test. -/
def smoothFormTest (χ : 𝓓(U, ℝ)) (A : ComplexModel n → RealForm n 2)
    (hA : ContDiff ℝ ∞ A) : 𝓓(U, RealForm n (2 * 1)) :=
  ⟨fun z => χ z • A z, χ.contDiff.smul hA, χ.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩

@[simp] theorem smoothFormTest_apply (χ : 𝓓(U, ℝ))
    (A : ComplexModel n → RealForm n 2) (hA : ContDiff ℝ ∞ A) (z : ComplexModel n) :
    smoothFormTest χ A hA z = χ z • A z := rfl

/-- The true compact scalar product `F(w)χ`. -/
def cutoffScalarTest (χ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) : 𝓓(U, ℝ) :=
  mulTest (hF.comp hw) χ

/-- The actual compact test `χ ddᶜF(w)`. -/
def compositeTest (χ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) : 𝓓(U, RealForm n (2 * 1)) :=
  smoothFormTest χ (smoothDDC (fun z => F (w z)))
    (contDiff_smoothDDC (w := fun z => F (w z)) (hF.comp hw))

/-- The actual compact test `χ F'(w)ddᶜw`. -/
def firstDerivativeTest (χ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) : 𝓓(U, RealForm n (2 * 1)) := by
  have hd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  exact smoothFormTest χ (fun z => deriv F (w z) • smoothDDC w z)
    ((hd.comp hw).smul (contDiff_smoothDDC hw))

/-- The complete localized differential error, without discarding any
first-derivative or torsion term. -/
def cutoffErrorTest (χ : 𝓓(U, ℝ)) (F : ℝ → ℝ) (w : ComplexModel n → ℝ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) : 𝓓(U, RealForm n (2 * 1)) :=
  ddcFullTest (scalarTest (cutoffScalarTest χ F w hF hw)) - compositeTest χ F w hF hw

/-- The positive convex-chain contribution is exactly the difference of the
two original compact tests. -/
theorem composite_sub_first_eq_defect (χ : 𝓓(U, ℝ)) (F : ℝ → ℝ)
    (w : ComplexModel n → ℝ) (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) :
    compositeTest χ F w hF hw - firstDerivativeTest χ F w hF hw =
      convexDefectTest χ F w hF hw := by
  apply TestFunction.ext
  intro z
  simp only [sub_apply, compositeTest, firstDerivativeTest, smoothFormTest_apply,
    convexDefectTest_apply, smul_sub]

/-- The localized smooth convex-cutoff inequality on an arbitrary positive
current of bidimension `(1,1)`. Every differential and cutoff term is an
actual internally constructed compact test; closedness is not assumed. -/
theorem localized_convex_cutoff_comparison
    (S : LocalProductCurrent n U 1) (hS : IsPositive S)
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w)
    (hF₂ : ∀ z, 0 ≤ deriv (deriv F) (w z)) :
    pairing S (firstDerivativeTest χ F w hF hw) ≤
      ddc S scalarUnit (cutoffScalarTest χ F w hF hw) -
        pairing S (cutoffErrorTest χ F w hF hw) := by
  have hpositive : 0 ≤ pairing S (compositeTest χ F w hF hw - firstDerivativeTest χ F w hF hw) := by
    rw [composite_sub_first_eq_defect]
    exact convex_defect_pairing_nonnegative S hS χ hχ hF hw hF₂
  rw [pairing_sub] at hpositive
  have ht := pairing_ddc_scalarTest S (cutoffScalarTest χ F w hF hw)
  rw [pairing_scalarTest] at ht
  rw [cutoffErrorTest, pairing_sub, ht]
  linarith

end SGPT.PSH.HermitianComparisonCutoff
