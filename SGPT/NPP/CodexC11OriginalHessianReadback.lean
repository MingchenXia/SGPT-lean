import SGPT.NPP.CodexC11PolarizedWeakReadback

/-! Actual original source obstacle, complex-Hessian test readback from the
same selected directional weak densities on one chart ball.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11OriginalHessianReadback.lean` (module `C11OriginalHessianReadback`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11PolarizingDirections
open SGPT.NPP.Codex.C11PolarizedWeakReadback

namespace SGPT.NPP.Codex.C11OriginalHessianReadback
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The same finite directional densities give the real and imaginary weak
pairings of every actual complex-Hessian coordinate entry. -/
theorem exists_original_complex_hessian_test_readback
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ (2*r) ⊆ e.val.target ∧
      let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
      ∃ (A : Fin n → Fin n → Fin 4 → ℝ)
        (d : Fin n → Fin n → Fin 4 → Ω → ℝ),
        (∀ j k t, 0 ≤ A j k t ∧ Measurable (d j k t) ∧
          (∀ᵐ z ∂(volume.comap Subtype.val), |d j k t z| ≤ A j k t)) ∧
        ∀ j k (φ : 𝓓(Ω, ℝ)),
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).re) =
            ((∫ z : Ω, φ z * d j k 0 z ∂(volume.comap Subtype.val)) -
             (∫ z : Ω, φ z * d j k 1 z ∂(volume.comap Subtype.val))) / 4 ∧
          (∫ z, f (e.val.symm z) * (complexHessian φ z j k).im) =
            ((∫ z : Ω, φ z * d j k 2 z ∂(volume.comap Subtype.val)) -
             (∫ z : Ω, φ z * d j k 3 z ∂(volume.comap Subtype.val))) / 4 := by
  obtain ⟨r,hr,htarget,A,d,hd⟩ := exists_original_polarizing_direction_densities hf e hz₀
  refine ⟨r,hr,htarget,A,d,?_,?_⟩
  · intro j k t
    exact ⟨(hd j k t).1,(hd j k t).2.1,(hd j k t).2.2.1⟩
  · let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
    have hΩ : (Ω : Set (ComplexModel n)) ⊆ e.val.target :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans htarget
    have hg : LocallyIntegrableOn (fun z => f (e.val.symm z)) Ω volume :=
      (hf.1.comp_continuousOn (e.val.continuousOn_symm.mono hΩ)).locallyIntegrableOn
        Ω.isOpen.measurableSet
    intro j k φ
    exact ⟨real_component_pairing hg j k φ _ _ ((hd j k 0).2.2.2 φ) ((hd j k 1).2.2.2 φ),
      imaginary_component_pairing hg j k φ _ _ ((hd j k 2).2.2.2 φ) ((hd j k 3).2.2.2 φ)⟩

end SGPT.NPP.Codex.C11OriginalHessianReadback
