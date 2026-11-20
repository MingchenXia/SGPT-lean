import SGPT.NPP.CodexC11OriginalMatrixDensity

/-! Uniqueness of bounded chart densities from their actual smooth tests.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/BoundedChartWeakUniqueness.lean` (module `BoundedChartWeakUniqueness`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions
open SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder

namespace SGPT.NPP.Codex.BoundedChartWeakUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- Equal pairings against all smooth tests identify measurable bounded
representatives almost everywhere on a finite open-domain measure. -/
theorem ae_eq_of_bounded_test_pairings
    (ξ : Measure Ω) [IsLocallyFiniteMeasure ξ] [IsFiniteMeasure ξ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hA : ∀ᵐ x ∂ξ, |f x| ≤ A) (hB : ∀ᵐ x ∂ξ, |g x| ≤ B)
    (heq : ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x * f x ∂ξ) = ∫ x : Ω, φ x * g x ∂ξ) :
    f =ᵐ[ξ] g := by
  have hfi : Integrable f ξ := Integrable.of_bound hf.aestronglyMeasurable A
    (by simpa only [Real.norm_eq_abs] using hA)
  have hgi : Integrable g ξ := Integrable.of_bound hg.aestronglyMeasurable B
    (by simpa only [Real.norm_eq_abs] using hB)
  have hfg := ae_le_of_nonnegative_test_integrals ξ hf hg hfi.locallyIntegrable
    hgi.locallyIntegrable (fun φ _ => (heq φ).le)
  have hgf := ae_le_of_nonnegative_test_integrals ξ hg hf hgi.locallyIntegrable
    hfi.locallyIntegrable (fun φ _ => (heq φ).ge)
  filter_upwards [hfg,hgf] with x h1 h2
  exact le_antisymm h1 h2

end SGPT.NPP.Codex.BoundedChartWeakUniqueness
