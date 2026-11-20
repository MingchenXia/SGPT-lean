import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

/-!
# Full compact-test transposition for a possibly nonclosed current

The Hermitian one-factor argument moves `ddᶜ` from a smooth scalar cutoff to
the mixed current. This module proves transposition for every local current
in the existing coefficient representation, on genuine full compact form
tests. No closedness of the current or of a background form is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonTranspose

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
  SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
  SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

/-- The actual full compact `ddᶜ` test with its mathematically equal degree. -/
def ddcFullTest (α : 𝓓(U, RealForm n (2 * q))) : 𝓓(U, RealForm n (2 * (q + 1))) :=
  (by omega : 2 * q + 1 + 1 = 2 * (q + 1)) ▸ localDdcTestCLM α

private theorem test_cast_apply {r s : ℕ} (h : r = s)
    (α : 𝓓(U, RealForm n r)) (x : ComplexModel n) :
    (h ▸ α : 𝓓(U, RealForm n s)) x = castForm h (α x) := by
  cases h
  rfl

theorem ddcFullTest_apply (α : 𝓓(U, RealForm n (2 * q))) (x : ComplexModel n) :
    ddcFullTest α x = castForm
      (by omega : 2 * q + 1 + 1 = 2 * (q + 1)) (localDdcTestCLM α x) := by
  unfold ddcFullTest
  exact test_cast_apply (by omega : 2 * q + 1 + 1 = 2 * (q + 1)) (localDdcTestCLM α) x

/-- The actual full differential stays in the genuine real type span. -/
theorem ddcFullTest_mem_formSpan (α : 𝓓(U, RealForm n (2 * q)))
    (hα : ∀ x, α x ∈ formSpan n q) (x : ComplexModel n) :
    ddcFullTest α x ∈ formSpan n (q + 1) := by
  rw [ddcFullTest_apply, localDdcTest_eq_coordinate_sum α hα x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact (formSpan n (q + 1)).smul_mem _ (wedgeLM q
    (isOneOne_coeffForm a b) (formBasis n q i)).property

/-- The genuine compact-test transpose identity for an arbitrary local
current. In particular, the current may be a mixed Hermitian product with a
nonclosed background. -/
theorem ddc_full_test_transpose (S : LocalProductCurrent n U (q + 1))
    (α : 𝓓(U, RealForm n (2 * q))) (hα : ∀ x, α x ∈ formSpan n q) :
    (∑ i, ddc S (formBasis n q i) (coeffTest α i)) =
      ∑ j, S (formBasis n (q + 1) j) (coeffTest (ddcFullTest α) j) := by
  let ι := Fin (Module.finrank ℝ (formSpan n q)) ×
    (Fin (n * 2) × Fin (n * 2))
  let γ : ι → formSpan n (q + 1) := fun t =>
    wedgeLM q (isOneOne_coeffForm t.2.1 t.2.2) (formBasis n q t.1)
  let ψ : ι → 𝓓(U, ℝ) := fun t => (-(1 / (4 * Real.pi))) •
    dTest (realBasis n t.2.2) (dTest (realBasis n t.2.1) (coeffTest α t.1))
  have h := sum_apply_eq_of_forall S (formBasis n (q + 1))
    (coeffTest (ddcFullTest α)) γ ψ (fun x _ => by
      rw [← eq_sum_coeffTest (ddcFullTest α) (ddcFullTest_mem_formSpan α hα) x,
        ddcFullTest_apply, localDdcTest_eq_coordinate_sum α hα x]
      simp only [ι, γ, ψ, Fintype.sum_prod_type, _root_.smul_apply, smul_eq_mul])
  simpa only [ι, γ, ψ, Fintype.sum_prod_type, map_smul, smul_eq_mul, ddc_apply_apply]
    using h.symm

end SGPT.PSH.HermitianComparisonTranspose
