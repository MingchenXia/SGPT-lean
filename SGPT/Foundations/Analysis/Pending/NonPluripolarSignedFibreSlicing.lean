import SGPT.Foundations.Analysis.Pending.NonPluripolarBorelFibreWeights

set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarSignedFibreSlicing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylorFibreSlicing MixedDensityRankOneSlot NonPluripolarFibreSlicing
  NonPluripolarBorelFibreWeights

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- Actual signed NP slicing: joint integrability produces almost every
fibre's integrability and integrability of the actual outer fibre integral. -/
theorem integral_mul_npLimit_eq_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {χ : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {G : ComplexModel (n + 1) → ℝ} (hG : Measurable G)
    (hint : Integrable (fun q => χ q * G q)
      (MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu)) :
    (∀ᵐ τ : ℂ, Integrable (fun y => χ (fibreMap n τ y) * G (fibreMap n τ y))
      (MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ))) ∧
    Integrable (fun τ : ℂ => ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) ∧
    (∫ q, χ q * G q ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu) =
      (∫ τ : ℂ, ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ)) / Real.pi := by
  let ν := MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu
  let μ := fun τ => MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ)
    (fibrePotentials u τ) (plurisubharmonicOn_fibrePotentials hu τ)
  let w := fun q => ENNReal.ofReal (χ q)
  let J := fun H : ComplexModel (n + 1) → ℝ≥0∞ => ∫⁻ q, w q * H q ∂ν
  let I := fun (H : ComplexModel (n + 1) → ℝ≥0∞) (τ : ℂ) =>
    ∫⁻ y, w (fibreMap n τ y) * H (fibreMap n τ y) ∂μ τ
  let p := fun q => ENNReal.ofReal (G q)
  let m := fun q => ENNReal.ofReal (-G q)
  let a := fun q => ENNReal.ofReal |G q|
  have hp : Measurable p := ENNReal.continuous_ofReal.measurable.comp hG
  have hm : Measurable m := ENNReal.continuous_ofReal.measurable.comp hG.neg
  have ha : Measurable a :=
    ENNReal.continuous_ofReal.measurable.comp (continuous_abs.measurable.comp hG)
  have hs {H : ComplexModel (n + 1) → ℝ≥0∞} (hH : Measurable H) :
      AEMeasurable (I H) ∧ J H = (∫⁻ τ : ℂ, I H τ) / ENNReal.ofReal Real.pi :=
    lintegral_mul_npLimit_eq_fibre hu hlast hχ hχc hχΩ hχ0 hH
  have hpa (q : ComplexModel (n + 1)) : p q ≤ a q :=
    ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hma (q : ComplexModel (n + 1)) : m q ≤ a q :=
    ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have hnorm (q : ComplexModel (n + 1)) :
      w q * a q = ENNReal.ofReal ‖χ q * G q‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ0 q), ENNReal.ofReal_mul (hχ0 q)]
  have hpos (q : ComplexModel (n + 1)) :
      w q * p q = ENNReal.ofReal (χ q * G q) := (ENNReal.ofReal_mul (hχ0 q)).symm
  have hneg (q : ComplexModel (n + 1)) :
      w q * m q = ENNReal.ofReal (-(χ q * G q)) := by
    dsimp only [w, m]
    rw [← ENNReal.ofReal_mul (hχ0 q), mul_neg]
  have hJa : J a ≠ ∞ := by
    dsimp only [J]
    simp_rw [hnorm]
    exact ((hasFiniteIntegral_iff_norm _).1 hint.hasFiniteIntegral).ne
  have hJp : J p ≠ ∞ := ne_top_of_le_ne_top hJa (lintegral_mono fun q => by
    dsimp only; gcongr; exact hpa q)
  have hJm : J m ≠ ∞ := ne_top_of_le_ne_top hJa (lintegral_mono fun q => by
    dsimp only; gcongr; exact hma q)
  have houter {H : ComplexModel (n + 1) → ℝ≥0∞} (hH : Measurable H)
      (hJ : J H ≠ ∞) : (∫⁻ τ : ℂ, I H τ) ≠ ∞ := by
    intro ht
    apply hJ
    rw [(hs hH).2, ht, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
  have hIa := houter ha hJa
  have hIp := houter hp hJp
  have hIm := houter hm hJm
  have hfa : ∀ᵐ τ : ℂ, I a τ < ∞ := ae_lt_top' (hs ha).1 hIa
  have hfp : ∀ᵐ τ : ℂ, I p τ < ∞ := ae_lt_top' (hs hp).1 hIp
  have hfm : ∀ᵐ τ : ℂ, I m τ < ∞ := ae_lt_top' (hs hm).1 hIm
  have hfi : ∀ᵐ τ : ℂ,
      Integrable (fun y => χ (fibreMap n τ y) * G (fibreMap n τ y)) (μ τ) := by
    filter_upwards [hfa] with τ hτ
    refine ⟨((hχ.measurable.mul hG).comp (continuous_fibreMap τ).measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [← hnorm]
    exact hτ
  have hPr : Integrable (fun τ : ℂ => (I p τ).toReal) :=
    integrable_toReal_of_lintegral_ne_top (hs hp).1 hIp
  have hMr : Integrable (fun τ : ℂ => (I m τ).toReal) :=
    integrable_toReal_of_lintegral_ne_top (hs hm).1 hIm
  have heq : (fun τ : ℂ => ∫ y, χ (fibreMap n τ y) * G (fibreMap n τ y) ∂μ τ) =ᵐ[volume]
      (fun τ : ℂ => (I p τ).toReal - (I m τ).toReal) := by
    filter_upwards [hfi] with τ hτ
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hτ]
    simp_rw [← hpos, ← hneg]
    rfl
  refine ⟨hfi, (hPr.sub hMr).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_sub hPr hMr,
    integral_toReal (hs hp).1 hfp, integral_toReal (hs hm).1 hfm,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  have hJpr : (∫⁻ q, ENNReal.ofReal (χ q * G q) ∂ν).toReal =
      (∫⁻ τ : ℂ, I p τ).toReal / Real.pi := by
    have h := congrArg ENNReal.toReal (hs hp).2
    simpa only [J, hpos, ENNReal.toReal_div, ENNReal.toReal_ofReal Real.pi_pos.le] using h
  have hJmr : (∫⁻ q, ENNReal.ofReal (-(χ q * G q)) ∂ν).toReal =
      (∫⁻ τ : ℂ, I m τ).toReal / Real.pi := by
    have h := congrArg ENNReal.toReal (hs hm).2
    simpa only [J, hneg, ENNReal.toReal_div, ENNReal.toReal_ofReal Real.pi_pos.le] using h
  rw [hJpr, hJmr]
  exact (sub_div _ _ _).symm

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarSignedFibreSlicing
