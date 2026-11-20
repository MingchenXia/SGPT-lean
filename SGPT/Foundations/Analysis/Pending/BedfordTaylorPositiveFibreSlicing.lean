import SGPT.Foundations.Analysis.Pending.BedfordTaylorBorelFibreSlicing

set_option autoImplicit false

/-! # Nonnegative Borel fibre slicing

The actual real Borel formula supplies all integrability before any
conversion to a nonnegative extended-real integral. This is a levelwise
producer for non-pluripolar increasing limits, not a finite-mass claim
about those limits.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorPositiveFibreSlicing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylor BedfordTaylorFibreSlicing MixedDensityRankOneSlot

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
  {ν : Measure (ComplexModel (n + 1))} {μ : ℂ → Measure (ComplexModel n)}
  {χ : ComplexModel (n + 1) → ℝ}

/-- Actual positive Borel slicing and base AE measurability, with all
integrability produced by the real slicing theorem. -/
theorem lintegral_indicator_isBTLimit_eq_fibre
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {E : Set (ComplexModel (n + 1))} (hE : MeasurableSet E) :
    AEMeasurable (fun τ : ℂ => ∫⁻ y,
      E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y) ∂μ τ) ∧
    (∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q ∂ν) =
      (∫⁻ τ : ℂ, ∫⁻ y,
        E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y) ∂μ τ) /
          ENNReal.ofReal Real.pi := by
  classical
  let f : ComplexModel (n + 1) → ℝ := fun q => χ q * E.indicator (fun _ => 1) q
  let I : ℂ → ℝ := fun τ => ∫ y, f (fibreMap n τ y) ∂μ τ
  have hf0 (q : ComplexModel (n + 1)) : 0 ≤ f q := by
    by_cases hq : q ∈ E <;> simp [f, hq, hχ0 q]
  have hf (q : ComplexModel (n + 1)) :
      ENNReal.ofReal (f q) = E.indicator (fun z => ENNReal.ofReal (χ z)) q := by
    by_cases hq : q ∈ E <;> simp [f, hq]
  have hs := BedfordTaylorBorelFibreSlicing.integral_indicator_isBTLimit_eq_fibre
    hlast hν hμ hχ hχc hχΩ hχ0 hE
  have hIj : Integrable I := hs.2.2.1
  have hI0 (τ : ℂ) : 0 ≤ I τ := integral_nonneg fun y => hf0 (fibreMap n τ y)
  have hinner (τ : ℂ) : ENNReal.ofReal (I τ) =
      ∫⁻ y, E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y) ∂μ τ := by
    change ENNReal.ofReal (∫ y, f (fibreMap n τ y) ∂μ τ) = _
    have hit : Integrable (fun y => f (fibreMap n τ y)) (μ τ) := hs.2.1 τ
    rw [ofReal_integral_eq_lintegral_ofReal hit
      (Eventually.of_forall fun y => hf0 (fibreMap n τ y))]
    exact lintegral_congr fun y => hf (fibreMap n τ y)
  refine ⟨?_, ?_⟩
  · have hm := ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hIj.aestronglyMeasurable.aemeasurable
    simpa only [Function.comp_def, hinner] using hm
  · have hjoint : ENNReal.ofReal (∫ q, f q ∂ν) =
        ∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q ∂ν := by
      rw [ofReal_integral_eq_lintegral_ofReal hs.1 (Eventually.of_forall hf0)]
      exact lintegral_congr hf
    have houter := ofReal_integral_eq_lintegral_ofReal hIj (Eventually.of_forall hI0)
    have hreal : (∫ q, f q ∂ν) = (∫ τ : ℂ, I τ) / Real.pi := hs.2.2.2
    rw [← hjoint, hreal, ENNReal.ofReal_div_of_pos Real.pi_pos, houter]
    congr 1
    exact lintegral_congr hinner

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorPositiveFibreSlicing
