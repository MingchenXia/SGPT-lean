import SGPT.Foundations.Analysis.Pending.NonPluripolarFibreSlicing

set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarBorelFibreWeights

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylorFibreSlicing MixedDensityRankOneSlot NonPluripolarFibreSlicing

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- Arbitrary nonnegative Borel weights for the actual NP joint and
fibre products, with no kernel or finite-mass premise. -/
theorem lintegral_mul_npLimit_eq_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {χ : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {F : ComplexModel (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    AEMeasurable (fun τ : ℂ => ∫⁻ y,
      ENNReal.ofReal (χ (fibreMap n τ y)) * F (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ)) ∧
    (∫⁻ q, ENNReal.ofReal (χ q) * F q
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu) =
      (∫⁻ τ : ℂ, ∫⁻ y,
        ENNReal.ofReal (χ (fibreMap n τ y)) * F (fibreMap n τ y)
          ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
            (plurisubharmonicOn_fibrePotentials hu τ)) /
          ENNReal.ofReal Real.pi := by
  classical
  let ν := MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu
  let μ := fun τ => MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ)
    (fibrePotentials u τ) (plurisubharmonicOn_fibrePotentials hu τ)
  let w := fun q => ENNReal.ofReal (χ q)
  let J := fun g : ComplexModel (n + 1) → ℝ≥0∞ => ∫⁻ q, w q * g q ∂ν
  let I := fun (g : ComplexModel (n + 1) → ℝ≥0∞) (τ : ℂ) =>
    ∫⁻ y, w (fibreMap n τ y) * g (fibreMap n τ y) ∂μ τ
  have hw : Measurable w := ENNReal.continuous_ofReal.measurable.comp hχ.measurable
  change AEMeasurable (I F) ∧ J F = (∫⁻ τ : ℂ, I F τ) / ENNReal.ofReal Real.pi
  refine hF.ennreal_induction
    (motive := fun g => AEMeasurable (I g) ∧
      J g = (∫⁻ τ : ℂ, I g τ) / ENNReal.ofReal Real.pi) ?_ ?_ ?_
  · intro c E hE
    have hs := lintegral_indicator_npLimit_eq_fibre hu hlast hχ hχc hχΩ hχ0 hE
    have hid (q : ComplexModel (n + 1)) :
        w q * E.indicator (fun _ => c) q = c * E.indicator w q := by
      by_cases hq : q ∈ E <;> simp [hq, mul_comm]
    have hj : J (E.indicator (fun _ => c)) = c * ∫⁻ q, E.indicator w q ∂ν := by
      dsimp only [J]
      simp_rw [hid]
      exact lintegral_const_mul c (hw.indicator hE)
    have hi (τ : ℂ) : I (E.indicator (fun _ => c)) τ =
        c * ∫⁻ y, E.indicator w (fibreMap n τ y) ∂μ τ := by
      dsimp only [I]
      simp_rw [hid]
      exact lintegral_const_mul c ((hw.indicator hE).comp (continuous_fibreMap τ).measurable)
    refine ⟨?_, ?_⟩
    · change AEMeasurable (fun τ => I (E.indicator (fun _ => c)) τ)
      simp_rw [hi]
      exact (aemeasurable_const : AEMeasurable (fun _ : ℂ => c)).mul hs.1
    · rw [hj]
      have hs' : (∫⁻ q, E.indicator w q ∂ν) =
          (∫⁻ τ : ℂ, ∫⁻ y, E.indicator w (fibreMap n τ y) ∂μ τ) /
            ENNReal.ofReal Real.pi := hs.2
      rw [hs']
      simp_rw [hi]
      rw [lintegral_const_mul'' c hs.1]
      simp only [div_eq_mul_inv, mul_assoc]
      rfl
  · intro f g _ hf hg hif hig
    have hj : J (f + g) = J f + J g := by
      dsimp only [J]
      simp only [Pi.add_apply, mul_add]
      exact lintegral_add_left (hw.mul hf) _
    have hi (τ : ℂ) : I (f + g) τ = I f τ + I g τ := by
      dsimp only [I]
      simp only [Pi.add_apply, mul_add]
      exact lintegral_add_left ((hw.mul hf).comp (continuous_fibreMap τ).measurable) _
    refine ⟨?_, ?_⟩
    · change AEMeasurable (fun τ => I (f + g) τ)
      simp_rw [hi]
      exact hif.1.add hig.1
    · rw [hj, hif.2, hig.2]
      simp_rw [hi]
      rw [lintegral_add_left' hif.1]
      simp only [div_eq_mul_inv, add_mul]
  · intro f hf hmono ih
    have hImono (τ : ℂ) : Monotone (fun k => I (f k) τ) := by
      intro k l hkl
      apply lintegral_mono
      intro y
      dsimp only
      gcongr
      exact hmono hkl (fibreMap n τ y)
    have hi (τ : ℂ) : I (fun q => ⨆ k, f k q) τ = ⨆ k, I (f k) τ := by
      dsimp only [I]
      simp_rw [ENNReal.mul_iSup]
      exact lintegral_iSup (fun k => (hw.mul (hf k)).comp (continuous_fibreMap τ).measurable)
        (fun k l hkl y => by gcongr; exact hmono hkl (fibreMap n τ y))
    have hj : J (fun q => ⨆ k, f k q) = ⨆ k, J (f k) := by
      dsimp only [J]
      simp_rw [ENNReal.mul_iSup]
      exact lintegral_iSup (fun k => hw.mul (hf k))
        (fun k l hkl q => by gcongr; exact hmono hkl q)
    refine ⟨?_, ?_⟩
    · change AEMeasurable (fun τ => I (fun q => ⨆ k, f k q) τ)
      simp_rw [hi]
      exact AEMeasurable.iSup (fun k => (ih k).1)
    · rw [hj]
      simp_rw [(ih _).2]
      rw [← ENNReal.iSup_div]
      rw [← lintegral_iSup' (fun k => (ih k).1) (Eventually.of_forall hImono)]
      simp_rw [hi]

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarBorelFibreWeights
