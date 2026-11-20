import SGPT.NPP.LogConcavityKhovanskiiTeissier
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers

/-!
# Log-concavity of mixed masses: currents with bounded potentials

Source `thm:logconc` (chapter on non-pluripolar products), second assertion, for closed
positive `(1,1)`-currents `Tᵢ = θᵢ + ddᶜuᵢ` whose potentials `uᵢ` are bounded:

`∫_X ⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ ∏ᵢ (∫_X ⟨Tᵢⁿ⟩)^{1/n}`.

The masses are the source non-pluripolar masses `sourceMixedNonPluripolarMass` (the book's
non-pluripolar products of `prop:nppwelldef`, TN's `globalMixedMass`). For bounded potentials the
classes are nef (TN `nefWithRespectTo_of_isBoundedPotential`) and the masses are the intersection
numbers (TN `globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential`), so the inequality is
the Khovanskii–Teissier inequality `prod_slotIntegral_rpow_le_slotIntegral_of_nef`.

The general (unbounded) case of `thm:logconc` is not covered here.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NPP.LogConcavity

open Set Filter MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`thm:logconc`, mixed-mass inequality, bounded potentials.** On a compact connected Kähler
manifold of dimension `n = q + 1`, for closed real `(1,1)`-forms `θᵢ` and bounded `θᵢ`-psh
functions `uᵢ`,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜuᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜu₁) ∧ ⋯ ∧ (θₙ + ddᶜuₙ)⟩`
(all masses finite, read as real numbers). -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_bounded (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i))
    (hb : ∀ i, BoundedGlobalProduct.IsBoundedPotential (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal := by
  have hpsh : ∀ i, ThetaPlurisubharmonic (atlasClosedFormToNative (θ i)).val (u i) := fun i =>
    ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1
  have hmixed : (sourceMixedNonPluripolarMass θ u hu).toReal =
      NefMixedMass.slotIntegral ω (fun i => atlasClosedFormToNative (θ i)) := by
    rw [sourceMixedNonPluripolarMass_eq_native]
    exact DominationIntersectionNumbers.globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential
      ω hpsh hb
  have hpure : ∀ i, (sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i)
      (fun _ => hu i)).toReal =
      NefMixedMass.slotIntegral ω (fun _ => atlasClosedFormToNative (θ i)) := by
    intro i
    rw [sourceMixedNonPluripolarMass_eq_native]
    exact DominationIntersectionNumbers.globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential
      ω (fun _ => hpsh i) (fun _ => hb i)
  simp_rw [hmixed, hpure]
  exact prod_slotIntegral_rpow_le_slotIntegral_of_nef ω _ fun i =>
    DominationIntersectionNumbers.nefWithRespectTo_of_isBoundedPotential ω (hpsh i) (hb i)

end SGPT.NPP.LogConcavity
