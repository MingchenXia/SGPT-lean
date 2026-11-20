import SGPT.Foundations.Analysis.Pending.HormanderAbstract
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The finite-family Hilbert-space step for the twisted estimate

A family of local test pieces is not itself a vector space: one must take the
free vector space on those pieces before using the Hörmander/Riesz theorem.
The data pairing is conjugate-linear, while the adjoint test section is linear.
This module isolates that algebra and the corresponding quantitative Riesz
representation. It is a conditional support result, not a proof of the global
Bochner--Kodaira inequality or of the twisted correction theorem.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open scoped InnerProductSpace ComplexConjugate
open SGPT.Foundations.Analysis.Pending.Hormander

/-- Finite-family Riesz representation, with the convention that the inner
product is conjugate-linear in its first argument. -/
theorem exists_riesz_of_finite_test_bound {I H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : I → H) (ℓ : I → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ α : I →₀ ℂ,
      ‖∑ i ∈ α.support, conj (α i) * ℓ i‖ ≤
        C * ‖∑ i ∈ α.support, α i • v i‖) :
    ∃ u ∈ (LinearMap.range (Finsupp.linearCombination ℂ v)).topologicalClosure,
      ‖u‖ ≤ C ∧ ∀ i, ⟪v i, u⟫_ℂ = ℓ i := by
  classical
  let A := Finsupp.linearCombination ℂ v
  let a := Finsupp.linearCombination ℂ (fun i => conj (ℓ i))
  have hb : ∀ α : I →₀ ℂ, ‖⟪a α, (1 : ℂ)⟫_ℂ‖ ≤ C * ‖A α‖ := by
    intro α
    simpa [a, A, Finsupp.linearCombination_apply, Finsupp.sum,
      RCLike.inner_apply, map_sum, map_mul] using hbound α
  obtain ⟨u, hu, hnorm, htest⟩ := exists_solution_of_bound a A (1 : ℂ) hC hb
  refine ⟨u, hu, hnorm, ?_⟩
  intro i
  have h := htest (Finsupp.single i 1)
  simpa [a, A, Finsupp.linearCombination_single, RCLike.inner_apply] using h

end SGPT.Trace.TwistedL2
