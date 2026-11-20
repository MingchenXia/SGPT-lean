import SGPT.PSH.HermitianProductsBoundedTransgression
import SGPT.PSH.HermitianProductsBorelTransgression
import SGPT.PSH.HermitianComparisonStrict

/-!
# The actual bounded Borel distinguished-factor identity

The unweighted identity is the proved theorem on the original bounded PSH
domain, with its actual mollifiers and limits produced internally. Its
bounded Borel extension is then applied to the genuine positive complete
products. The native negative-semipositive residual supplies every positive
orientation, and the actual scalar weight is produced from Borel bounded H.
No unweighted identity, approximation or weighted conclusion is an input.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorCollar
open HermitianComparisonOneFactor HermitianComparisonStrict

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Global boundedness of H produces the original local Borel-weight bound;
the distinguished potentials need no ambient bound outside their domain. -/
theorem locallyBounded_indicator_difference_comp (a b : ComplexModel n → ℝ)
    {H : ℝ → ℝ} (hH : ∃ C : ℝ, ∀ t, |H t| ≤ C) :
    IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) U := by
  obtain ⟨C, hC⟩ := hH
  intro K _ hKU
  refine ⟨C, fun z hz => ?_⟩
  rw [indicator_of_mem (hKU hz)]
  exact hC _

/-- The actual strict difference weight is the ordinary indicator of the
strict set inside the original open domain. -/
theorem indicator_strict_difference_eq (a b : ComplexModel n → ℝ) :
    (U : Set (ComplexModel n)).indicator (fun z => strictIndicator (b z - a z)) =
      ((U : Set (ComplexModel n)) ∩ {z | a z < b z}).indicator (fun _ => (1 : ℝ)) := by
  funext z
  by_cases hz : z ∈ U
  · rw [indicator_of_mem hz]
    by_cases hlt : a z < b z
    · have hm : z ∈ (U : Set (ComplexModel n)) ∩ {z | a z < b z} := ⟨hz, hlt⟩
      rw [indicator_of_mem hm]
      simp only [strictIndicator, sub_pos.mpr hlt, ↓reduceIte]
    · rw [indicator_of_notMem (fun h => hlt h.2)]
      simp only [strictIndicator, sub_pos, hlt, ↓reduceIte]
  · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz h.1)]

/-- The genuine bounded Borel insertion identity for the original actual
Hermitian products. All unweighted transgression and weight-regularity
producers are invoked internally; there is no identity-result premise. -/
theorem backgroundExpansion_borel_transgression (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hnegσ : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    (hA : IsPositive (backgroundExpansion (p + 1) 0 (Fin.cons b v) hσ (castLPC (by omega) T)))
    (hB : IsPositive (backgroundExpansion (p + 1) 0 (Fin.cons a v) hσ (castLPC (by omega) T)))
    {H : ℝ → ℝ} (hH : Measurable H) (hHb : ∃ C : ℝ, ∀ t, |H t| ≤ C) :
    mulBorel (backgroundExpansion (p + 1) 0 (Fin.cons b v) hσ (castLPC (by omega) T))
        ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) -
      mulBorel (backgroundExpansion (p + 1) 0 (Fin.cons a v) hσ (castLPC (by omega) T))
        ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) =
      weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b H := by
  have hσS : ∀ z ∈ U, σ z ∈ formSpan n 1 := by
    intro z hz
    have hs := (formSpan n 1).neg_mem (oneOne_mem_formSpan (hnegσ z hz).1)
    simpa only [neg_neg] using hs
  exact mulBorel_backgroundResidual_transgression p T hT hTc v hv hσ hnegσ hA hB ha hb
    (backgroundExpansion_transgression p T hT hTc v hv ha hb hσ hσS) H
    (measurable_indicator_difference_comp
      (measurable_indicator_of_isLocallyBoundedPshOn ha)
      (measurable_indicator_of_isLocallyBoundedPshOn hb) hH)
    (locallyBounded_indicator_difference_comp a b hHb)

/-- Literal strict-set insertion for the original complete positive
products. The genuine strict indicator is Borel and bounded internally. -/
theorem backgroundExpansion_strict_transgression (p : ℕ)
    (T : LocalProductCurrent n U (1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hnegσ : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    (hA : IsPositive (backgroundExpansion (p + 1) 0 (Fin.cons b v) hσ (castLPC (by omega) T)))
    (hB : IsPositive (backgroundExpansion (p + 1) 0 (Fin.cons a v) hσ (castLPC (by omega) T))) :
    mulBorel (backgroundExpansion (p + 1) 0 (Fin.cons b v) hσ (castLPC (by omega) T))
        ((U : Set (ComplexModel n)).indicator (fun z => strictIndicator (b z - a z))) -
      mulBorel (backgroundExpansion (p + 1) 0 (Fin.cons a v) hσ (castLPC (by omega) T))
        ((U : Set (ComplexModel n)).indicator (fun z => strictIndicator (b z - a z))) =
      weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b strictIndicator := by
  apply backgroundExpansion_borel_transgression p T hT hTc v hv ha hb hσ hnegσ hA hB
    measurable_strictIndicator
  refine ⟨1, fun t => ?_⟩
  unfold strictIndicator
  split <;> norm_num

end SGPT.PSH.HermitianProducts
