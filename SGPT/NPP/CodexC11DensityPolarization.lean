import SGPT.NPP.CodexC11OriginalHessianReadback

/-! Algebra for packaging bounded directional density integrals as a single
polarized real component.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11DensityPolarization.lean` (module `C11DensityPolarization`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.NPP.Codex.C11DensityPolarization

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Bounded measurable directional densities can be combined inside the
integral, retaining the exact polarization normalization. -/
theorem integral_polarized_density {ψ a b : X → ℝ} {A B : ℝ}
    (hψ : Integrable ψ μ) (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ᵐ x ∂μ, |a x| ≤ A) (hB : ∀ᵐ x ∂μ, |b x| ≤ B) :
    (∫ x, ψ x * ((a x - b x) / 4) ∂μ) =
      ((∫ x, ψ x * a x ∂μ) - (∫ x, ψ x * b x ∂μ)) / 4 := by
  have ha' : Integrable (fun x => ψ x * a x) μ :=
    hψ.mul_bdd ha.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hA)
  have hb' : Integrable (fun x => ψ x * b x) μ :=
    hψ.mul_bdd hb.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hB)
  calc
    (∫ x, ψ x * ((a x - b x) / 4) ∂μ) =
        ∫ x, (ψ x * a x - ψ x * b x) / 4 ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = _ := by rw [integral_div, integral_sub ha' hb']

end SGPT.NPP.Codex.C11DensityPolarization
