import SGPT.NPP.CodexC11DirectionalDensity

/-! Actual source C¹¹-bar obstacle on an original complex chart.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11OriginalChartDensity.lean` (module `C11OriginalChartDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11DirectionalDensity

namespace SGPT.NPP.Codex.C11OriginalChartDensity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A source C¹¹-bar function has an actual bounded directional Levi density
on every open chart domain lying in a compact subset of the chart target. -/
theorem exists_original_chart_directional_density
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ e.val.target)
    (Ω : Opens (ComplexModel n)) (hΩK : (Ω : Set (ComplexModel n)) ⊆ K)
    (v : ComplexModel n) :
    ∃ (A : ℝ) (d : Ω → ℝ), 0 ≤ A ∧ Measurable d ∧
      (∀ᵐ z ∂(volume.comap Subtype.val), |d z| ≤ A) ∧
      ∀ φ : 𝓓(Ω, ℝ),
        (∫ z, f (e.val.symm z) * leviForm φ z v) =
          ∫ z : Ω, φ z * d z ∂(volume.comap Subtype.val) := by
  have hΩU : (Ω : Set (ComplexModel n)) ⊆ e.val.target := hΩK.trans hKU
  have hg : LocallyIntegrableOn (fun z => f (e.val.symm z)) Ω volume :=
    ((hf.1.comp_continuousOn (e.val.continuousOn_symm.mono hΩU)).locallyIntegrableOn
      Ω.isOpen.measurableSet)
  let : IsFiniteMeasure (volume.comap (Subtype.val : Ω → ComplexModel n)) := ⟨by
    have h : (volume.comap (Subtype.val : Ω → ComplexModel n)) univ ≤
        volume (Subtype.val '' (univ : Set Ω)) :=
      Measure.comap_apply_le _ _ nullMeasurableSet_univ
    have hk : volume (Ω : Set (ComplexModel n)) < ⊤ :=
      (measure_mono hΩK).trans_lt hK.measure_lt_top
    rw [image_univ, Subtype.range_coe] at h
    simpa using h.trans_lt hk⟩
  exact exists_directional_levi_density (hf.2 e) hK hKU Ω hΩK hg v

end SGPT.NPP.Codex.C11OriginalChartDensity
