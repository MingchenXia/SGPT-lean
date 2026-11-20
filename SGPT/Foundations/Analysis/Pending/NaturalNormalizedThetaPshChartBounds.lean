import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1

/-!
# Actual singular normalized chart bounds and weak distributions

The original Harnack producer is used without a continuous-potential
restriction. Pole values remain original throughout the bound.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshChartBounds

open FirstPass ThetaPshChartLimitGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : SmoothRealForm n M 2}

/-- Genuine normalized singular potentials have uniformly bounded real chart absolute integrals. -/
theorem exists_integral_abs_chart_toReal_le
    (hθ : HasSmoothLocalPotentials θ) (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    ∃ B : ℝ, ∀ u : M → EReal, IsThetaPshPotential θ u →
      (∀ x, u x ≤ 0) → (∃ x₀, 0 ≤ u x₀) →
      ∫ z in K, |(chartFunction u e z).toReal| ∂volume ≤ B := by
  obtain ⟨B, hB, hbd⟩ :=
    ThetaPshUniformL1Bound.exists_lintegral_compact_le hθ e hK hKe 0
  refine ⟨B.toReal, fun u hu hle hx => ?_⟩
  have hlin := hbd u hu.1 hle (by simpa using hx)
  have hfun (z : ComplexModel n) : ENNReal.ofReal |(chartFunction u e z).toReal| ≤
      (-u (e.val.symm z)).toENNReal := by
    have hz := hle (e.val.symm z)
    change ENNReal.ofReal |(u (e.val.symm z)).toReal| ≤ _
    generalize u (e.val.symm z) = a at *
    induction a using EReal.rec with
    | bot => simp
    | top => simp at hz
    | coe t =>
      have ht : t ≤ 0 := EReal.coe_nonpos.mp hz
      simp only [EReal.toReal_coe, ← EReal.coe_neg, EReal.real_coe_toENNReal,
        abs_of_nonpos ht]
      exact le_rfl
  have habs := (hu.quasiPshPotential.integrableOn_chart_toReal e hK hKe).abs
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => abs_nonneg _)) habs.aestronglyMeasurable]
  exact ENNReal.toReal_mono hB.ne ((lintegral_mono hfun).trans hlin)

/-- The original real chart representatives of normalized singular potentials have actual weak distributions. -/
theorem exists_isChartLimit_of_normalized
    (hθ : HasSmoothLocalPotentials θ) {ι : Type*} (U : Ultrafilter ι)
    (u : ι → M → EReal) (hu : ∀ i, IsThetaPshPotential θ (u i))
    (hle : ∀ i x, u i x ≤ 0) (hnorm : ∀ i, ∃ x₀, 0 ≤ u i x₀) :
    ∃ T : ∀ e : ComplexChart n M, 𝓓'(chartTarget e, ℝ),
      ∀ e, IsChartLimit volume (U : Filter ι) (fun i x => (u i x).toReal) e (T e) := by
  refine exists_isChartLimit (μ := volume) U (fun i x => (u i x).toReal)
    (fun i e => (hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e) ?_
  intro e K hK hKe
  obtain ⟨B, hB⟩ := exists_integral_abs_chart_toReal_le hθ e hK hKe
  exact ⟨B, fun i => hB (u i) (hu i) (hle i) (hnorm i)⟩

end SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshChartBounds
