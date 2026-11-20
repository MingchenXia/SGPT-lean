import SGPT.NPP.CodexC11PolarizationBound
import SGPT.NPP.CodexC11BoundedDistributionDensity
import SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder

/-! Bounded measurable directional Levi density on a finite chart domain,
constructed from the source local distributional test bound.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11DirectionalDensity.lean` (module `C11DirectionalDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.NPP.Codex.C11PolarizationBound SGPT.NPP.Codex.BoundedDistributionDensity
open SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder

namespace SGPT.NPP.Codex.C11DirectionalDensity

variable {n : ℕ}

/-- On an open finite-volume domain inside a compact chart set, the actual
directional distributional Levi form has a bounded measurable representative. -/
theorem exists_directional_levi_density
    {g : ComplexModel n → ℝ} {U K : Set (ComplexModel n)}
    (h : HasLocallyBoundedComplexHessianOn g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (Ω : Opens (ComplexModel n))
    (hΩK : (Ω : Set (ComplexModel n)) ⊆ K)
    (hg : LocallyIntegrableOn g Ω volume) (v : ComplexModel n)
    [IsFiniteMeasure (volume.comap (Subtype.val : Ω → ComplexModel n))] :
    ∃ (A : ℝ) (d : Ω → ℝ), 0 ≤ A ∧ Measurable d ∧
      (∀ᵐ z ∂(volume.comap Subtype.val), |d z| ≤ A) ∧
      ∀ φ : 𝓓(Ω, ℝ),
        (∫ z, g z * leviForm φ z v) =
          ∫ z : Ω, φ z * d z ∂(volume.comap Subtype.val) := by
  let ξ : Measure Ω := volume.comap Subtype.val
  let : IsLocallyFiniteMeasure ξ := isLocallyFiniteMeasure_open_comap volume
  obtain ⟨A,hA,hbound⟩ := exists_distributional_levi_test_bound h hK hKU Ω hΩK hg v
  obtain ⟨d,hd,hda,htest⟩ := exists_density_of_bounded_distribution ξ
    (distributionalLeviCLM v (regularDistribution volume g hg)) A hA hbound
  refine ⟨A,d,hA,hd,hda,?_⟩
  intro φ
  rw [← distributionalLeviCLM_regularDistribution_apply hg φ v]
  exact htest φ

end SGPT.NPP.Codex.C11DirectionalDensity
