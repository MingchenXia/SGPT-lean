import SGPT.NPP.CodexC11DensityPolarization

/-! Bounded measurable real and imaginary coordinate Hessian densities for the
original source obstacle on one chart ball.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11OriginalMatrixDensity.lean` (module `C11OriginalMatrixDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions CompactlySupported
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11OriginalHessianReadback
open SGPT.NPP.Codex.C11DensityPolarization

namespace SGPT.NPP.Codex.C11OriginalMatrixDensity
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- On a single chart ball, each original complex-Hessian coordinate has
bounded measurable real and imaginary densities with actual weak tests. -/
theorem exists_original_complex_hessian_component_densities
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ (2*r) ⊆ e.val.target ∧
      let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
      ∃ (R I : Fin n → Fin n → Ω → ℝ) (BR BI : Fin n → Fin n → ℝ),
        (∀ j k, Measurable (R j k) ∧ Measurable (I j k) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |R j k z| ≤ BR j k) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |I j k z| ≤ BI j k)) ∧
        ∀ j k (φ : 𝓓(Ω, ℝ)),
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).re) =
            ∫ z : Ω, φ z * R j k z ∂(volume.comap Subtype.val) ∧
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).im) =
            ∫ z : Ω, φ z * I j k z ∂(volume.comap Subtype.val) := by
  obtain ⟨r,hr,htarget,A,d,hd,ht⟩ := exists_original_complex_hessian_test_readback hf e hz₀
  let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
  let ξ : Measure Ω := volume.comap Subtype.val
  let : IsLocallyFiniteMeasure ξ := isLocallyFiniteMeasure_open_comap volume
  let R : Fin n → Fin n → Ω → ℝ := fun j k z => (d j k 0 z - d j k 1 z) / 4
  let I : Fin n → Fin n → Ω → ℝ := fun j k z => (d j k 2 z - d j k 3 z) / 4
  let BR : Fin n → Fin n → ℝ := fun j k => (A j k 0 + A j k 1) / 4
  let BI : Fin n → Fin n → ℝ := fun j k => (A j k 2 + A j k 3) / 4
  refine ⟨r,hr,htarget,R,I,BR,BI,?_,?_⟩
  · intro j k
    refine ⟨((hd j k 0).2.1.sub (hd j k 1).2.1).div_const _,
      ((hd j k 2).2.1.sub (hd j k 3).2.1).div_const _,?_,?_⟩
    · filter_upwards [(hd j k 0).2.2,(hd j k 1).2.2] with z h0 h1
      dsimp [R,BR]
      rw [abs_div, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add h0 h1)) (by norm_num)
    · filter_upwards [(hd j k 2).2.2,(hd j k 3).2.2] with z h2 h3
      dsimp [I,BI]
      rw [abs_div, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add h2 h3)) (by norm_num)
  · intro j k φ
    let ψ : Ω → ℝ := fun z => φ z
    let ψc : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    have hψ : Integrable ψ ξ := by
      have he : ψ = ψc := by funext z; rfl
      rw [he]
      exact ψc.continuous.integrable_of_hasCompactSupport ψc.hasCompactSupport
    constructor
    · rw [(ht j k φ).1]
      exact (integral_polarized_density hψ (hd j k 0).2.1 (hd j k 1).2.1
        (hd j k 0).2.2 (hd j k 1).2.2).symm
    · rw [(ht j k φ).2]
      exact (integral_polarized_density hψ (hd j k 2).2.1 (hd j k 3).2.1
        (hd j k 2).2.2 (hd j k 3).2.2).symm

end SGPT.NPP.Codex.C11OriginalMatrixDensity
