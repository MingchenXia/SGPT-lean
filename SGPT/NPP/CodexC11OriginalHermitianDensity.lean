import SGPT.NPP.CodexC11WeakMatrixSymmetry

/-! The actual source obstacle's bounded coordinate densities are Hermitian
almost everywhere, as forced by their weak test identities.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11OriginalHermitianDensity.lean` (module `C11OriginalHermitianDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11OriginalMatrixDensity
open SGPT.NPP.Codex.C11WeakMatrixSymmetry

namespace SGPT.NPP.Codex.C11OriginalHermitianDensity
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- On one actual chart ball the original complex-Hessian component densities
are bounded and measurable, have the genuine weak pairings, and are Hermitian
almost everywhere for each coordinate pair. -/
theorem exists_original_hermitian_component_densities
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
        ∀ j k, (R j k =ᵐ[volume.comap Subtype.val] R k j) ∧
          (I j k =ᵐ[volume.comap Subtype.val] fun z => -I k j z) := by
  obtain ⟨r,hr,htarget,R,I,BR,BI,hd,ht⟩ :=
    exists_original_complex_hessian_component_densities hf e hz₀
  let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
  let ξ : Measure Ω := volume.comap Subtype.val
  let : IsLocallyFiniteMeasure ξ := isLocallyFiniteMeasure_open_comap volume
  let : IsFiniteMeasure ξ := ⟨by
    have h : ξ univ ≤ volume (Subtype.val '' (univ : Set Ω)) :=
      Measure.comap_apply_le _ _ nullMeasurableSet_univ
    rw [image_univ,Subtype.range_coe] at h
    have hk : volume (Ω : Set (ComplexModel n)) < ⊤ :=
      (measure_mono (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith)))).trans_lt
          (isCompact_closedBall z₀ (2*r)).measure_lt_top
    exact h.trans_lt hk⟩
  exact ⟨r,hr,htarget,R,I,BR,BI,hd,ht,
    ae_hermitian_of_component_tests ξ (fun z => f (e.val.symm z)) R I BR BI hd ht⟩

end SGPT.NPP.Codex.C11OriginalHermitianDensity
