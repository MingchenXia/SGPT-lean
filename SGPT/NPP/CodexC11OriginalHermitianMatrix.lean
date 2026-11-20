import SGPT.NPP.CodexC11HermitianPointwise

/-! Actual original source obstacle's coordinate densities form one Hermitian
matrix on a single common almost-everywhere set.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11OriginalHermitianMatrix.lean` (module `C11OriginalHermitianMatrix`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11OriginalHermitianDensity
open SGPT.NPP.Codex.C11HermitianPointwise

namespace SGPT.NPP.Codex.C11OriginalHermitianMatrix
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The same bounded measurable component densities satisfy all original
weak pairings and form a Hermitian complex matrix on one a.e. set. -/
theorem exists_original_hermitian_matrix_density
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ (2*r) ⊆ e.val.target ∧
      let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
      ∃ (R I : Fin n → Fin n → Ω → ℝ) (BR BI : Fin n → Fin n → ℝ),
        (∀ j k, Measurable (R j k) ∧ Measurable (I j k) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |R j k z| ≤ BR j k) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |I j k z| ≤ BI j k)) ∧
        (∀ j k (φ : 𝓓(Ω, ℝ)),
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).re) =
            ∫ z : Ω, φ z * R j k z ∂(volume.comap Subtype.val) ∧
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).im) =
            ∫ z : Ω, φ z * I j k z ∂(volume.comap Subtype.val)) ∧
        ∀ᵐ z ∂(volume.comap Subtype.val), Matrix.IsHermitian
          (fun j k => (R j k z : ℂ) + Complex.I * (I j k z : ℂ)) := by
  obtain ⟨r,hr,htarget,R,I,BR,BI,hd,ht,hs⟩ :=
    exists_original_hermitian_component_densities hf e hz₀
  exact ⟨r,hr,htarget,R,I,BR,BI,hd,ht,ae_matrix_isHermitian R I hs⟩

end SGPT.NPP.Codex.C11OriginalHermitianMatrix
