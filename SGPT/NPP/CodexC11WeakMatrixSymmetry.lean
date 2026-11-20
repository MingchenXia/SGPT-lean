import SGPT.NPP.CodexC11BoundedChartWeakUniqueness

/-! Symmetry of weak complex-Hessian coordinate representatives follows
from their actual test identities and uniqueness of bounded densities.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11WeakMatrixSymmetry.lean` (module `C11WeakMatrixSymmetry`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.NPP.Codex.BoundedChartWeakUniqueness

namespace SGPT.NPP.Codex.C11WeakMatrixSymmetry
variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- The real entries are a.e. symmetric and the imaginary entries are a.e.
antisymmetric whenever bounded representatives have the Hessian weak tests. -/
theorem ae_hermitian_of_component_tests
    (ξ : Measure Ω) [IsLocallyFiniteMeasure ξ] [IsFiniteMeasure ξ]
    (g : ComplexModel n → ℝ) (R I : Fin n → Fin n → Ω → ℝ)
    (BR BI : Fin n → Fin n → ℝ)
    (hd : ∀ j k, Measurable (R j k) ∧ Measurable (I j k) ∧
      (∀ᵐ z ∂ξ, |R j k z| ≤ BR j k) ∧ (∀ᵐ z ∂ξ, |I j k z| ≤ BI j k))
    (ht : ∀ j k (φ : 𝓓(Ω, ℝ)),
      (∫ z, g z * (complexHessian φ z j k).re) = ∫ z : Ω, φ z * R j k z ∂ξ ∧
      (∫ z, g z * (complexHessian φ z j k).im) = ∫ z : Ω, φ z * I j k z ∂ξ) :
    ∀ j k, (R j k =ᵐ[ξ] R k j) ∧ (I j k =ᵐ[ξ] fun z => -I k j z) := by
  intro j k
  have hreal (φ : 𝓓(Ω, ℝ)) (z : ComplexModel n) :
      (complexHessian φ z j k).re = (complexHessian φ z k j).re := by
    have hφ2 : ContDiff ℝ 2 (φ : ComplexModel n → ℝ) :=
      φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have h := (complexHessian_isHermitian (z := z) hφ2.contDiffAt).apply j k
    have hr := congrArg Complex.re h
    simpa using hr.symm
  have himag (φ : 𝓓(Ω, ℝ)) (z : ComplexModel n) :
      (complexHessian φ z j k).im = -(complexHessian φ z k j).im := by
    have hφ2 : ContDiff ℝ 2 (φ : ComplexModel n → ℝ) :=
      φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have h := (complexHessian_isHermitian (z := z) hφ2.contDiffAt).apply j k
    have hi := congrArg Complex.im h
    simpa using hi.symm
  constructor
  · apply ae_eq_of_bounded_test_pairings ξ (hd j k).1 (hd k j).1
      (hd j k).2.2.1 (hd k j).2.2.1
    intro φ
    rw [← (ht j k φ).1, ← (ht k j φ).1]
    apply integral_congr_ae
    filter_upwards with z
    rw [hreal φ z]
  · apply ae_eq_of_bounded_test_pairings ξ (hd j k).2.1 (hd k j).2.1.neg
      (hd j k).2.2.2 (by simpa only [Pi.neg_apply, abs_neg] using (hd k j).2.2.2)
    intro φ
    simp only [Pi.neg_apply, mul_neg, integral_neg]
    rw [← (ht j k φ).2, ← (ht k j φ).2, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    rw [himag φ z]
    ring

end SGPT.NPP.Codex.C11WeakMatrixSymmetry
