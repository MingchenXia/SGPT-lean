import SGPT.PSH.SourceIGoodAnalyticCharacterization
import SGPT.PSH.SourcePIComparison
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Envelopes.SourcePositiveAffineEnvelopes
import SGPT.PSH.SourceSingleVolumeRepresentativeChange
import SGPT.PSH.SourceSubgeodesicBackground
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-!
# The mass gap `Macron(θ_φ) = vol θ_φ - ∫_X θ_φ^n`

Source `rmk:Macron` (chapter *𝓘-good singularities*): for `φ ∈ PSH(X, θ)` the book introduces
the defect
`Macron(θ_φ) ≔ vol θ_φ - ∫_X θ_φ^n`
between the volume (`def:volqpsh`, the non-pluripolar mass of the `𝓘`-envelope `P_θ[φ]_𝓘`) and
the non-pluripolar mass of `θ_φ`, and observes ("in view of `thm:charIgoodasclosure` and
`cor:compnppmassandvol`") that it characterizes the failure of `𝓘`-goodness of a potential
`φ ∈ PSH(X, θ)_{>0}`.

## Main declarations

* `SGPT.IGood.sourceMassGap`: the defect, as an extended nonnegative real.
* `SGPT.IGood.sourceMassGap_add_mass`: it is the genuine difference: `Macron + ∫ θ_φ^n = vol θ_φ`
  (`cor:compnppmassandvol` gives `∫ θ_φ^n ≤ vol θ_φ`), and both terms are finite
  (`SGPT.IGood.sourceIVolume_lt_top`), so `Macron` is also the real difference
  (`SGPT.IGood.sourceMassGap_toReal`).
* `SGPT.IGood.sourceIGood_iff_sourceMassGap_eq_zero`: for `φ ∈ PSH(X, θ)_{>0}`,
  `φ` is `𝓘`-good iff `Macron(θ_φ) = 0`.
* `SGPT.IGood.sourceMassGap_smooth_representative_invariance`: `Macron(θ_φ)` only depends on the
  current `θ_φ` (it is unchanged under `θ ↦ θ + dd^c g`, `φ ↦ φ - g`), as the notation suggests.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.IGood

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Source `rmk:Macron`: the mass gap `Macron(θ_φ) = vol θ_φ - ∫_X θ_φ^n` of `φ ∈ PSH(X, θ)`,
where `vol θ_φ = ∫_X θ_{P_θ[φ]_𝓘}^n` (`def:volqpsh`, `sourceIVolume`) and `∫_X θ_φ^n` is the
non-pluripolar mass. It is the true difference by `sourceMassGap_add_mass`. -/
def sourceMassGap (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : ℝ≥0∞ :=
  sourceIVolume θ φ hφ - sourcePotentialNonPluripolarMeasure θ φ hφ univ

/-- The volume `vol θ_φ` is finite. -/
theorem sourceIVolume_lt_top (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : sourceIVolume θ φ hφ < ⊤ :=
  sourceAffine_mass_lt_top ω (isThetaPSH_sourceIEnvelope hφ)

/-- `Macron(θ_φ)` is the genuine difference: `Macron(θ_φ) + ∫_X θ_φ^n = vol θ_φ`
(source `cor:compnppmassandvol`: `∫_X θ_φ^n ≤ vol θ_φ`). -/
theorem sourceMassGap_add_mass (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceMassGap θ φ hφ + sourcePotentialNonPluripolarMeasure θ φ hφ univ =
      sourceIVolume θ φ hφ :=
  tsub_add_cancel_of_le (sourceMass_le_iVolume ω hφ)

/-- `Macron(θ_φ)` is finite. -/
theorem sourceMassGap_lt_top (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : sourceMassGap θ φ hφ < ⊤ :=
  lt_of_le_of_lt tsub_le_self (sourceIVolume_lt_top ω hφ)

/-- The real-valued reading of `rmk:Macron`: `Macron(θ_φ) = vol θ_φ - ∫_X θ_φ^n` as real numbers,
with both terms finite. -/
theorem sourceMassGap_toReal (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    (sourceMassGap θ φ hφ).toReal =
      (sourceIVolume θ φ hφ).toReal - (sourcePotentialNonPluripolarMeasure θ φ hφ univ).toReal :=
  ENNReal.toReal_sub_of_le (sourceMass_le_iVolume ω hφ) (sourceIVolume_lt_top ω hφ).ne

/-- `Macron(θ_φ) = 0` iff the mass equals the volume, `∫_X θ_φ^n = vol θ_φ`. -/
theorem sourceMassGap_eq_zero_iff (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceMassGap θ φ hφ = 0 ↔
      sourcePotentialNonPluripolarMeasure θ φ hφ univ = sourceIVolume θ φ hφ := by
  unfold sourceMassGap
  rw [tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm (sourceMass_le_iVolume ω hφ) h, fun h => h.ge⟩

/-- Source `rmk:Macron`, the characterization: for `φ ∈ PSH(X, θ)_{>0}`, the potential `φ` is
`𝓘`-good (`def:Igoodpot`) iff `Macron(θ_φ) = 0`; equivalently `φ` fails to be `𝓘`-good iff
`Macron(θ_φ) > 0`. This combines `thm:charIgoodasclosure` (mass = volume iff
`P_θ[φ] = P_θ[φ]_𝓘`) with the background independence of `𝓘`-goodness. -/
theorem sourceIGood_iff_sourceMassGap_eq_zero (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    sourceIGood (n := n) φ ↔ sourceMassGap θ φ hφ = 0 := by
  have hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) :=
    sourcePositiveMassClass_isBig ω ⟨φ, hφ, hpos⟩
  obtain ⟨hm, he, -⟩ :=
    sourceIGood_analytic_mass_envelope_equivalences ω θ hbig ⟨φ, hφ⟩ hpos
  rw [sourceIGood_iff_PI_eq ω hφ hpos, sourceMassGap_eq_zero_iff ω hφ]
  exact he.symm.trans hm

/-- The same characterization in a fixed background: `sourceIGoodWith θ φ` (positive mass and
`P_θ[φ] = P_θ[φ]_𝓘`) iff the mass is positive and `Macron(θ_φ) = 0`. -/
theorem sourceIGoodWith_iff_sourceMassGap_eq_zero (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIGoodWith θ φ hφ ↔
      0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ ∧ sourceMassGap θ φ hφ = 0 := by
  constructor
  · intro h
    exact ⟨h.1, (sourceIGood_iff_sourceMassGap_eq_zero ω hφ h.1).mp h.iGood⟩
  · rintro ⟨hpos, h0⟩
    exact (sourceIGood_iff_with_positive_background ω hφ hpos).mp
      ((sourceIGood_iff_sourceMassGap_eq_zero ω hφ hpos).mpr h0)

/-- The failure of `𝓘`-goodness of `φ ∈ PSH(X, θ)_{>0}` is exactly a positive mass gap. -/
theorem not_sourceIGood_iff_sourceMassGap_pos (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    ¬ sourceIGood (n := n) φ ↔ 0 < sourceMassGap θ φ hφ := by
  rw [sourceIGood_iff_sourceMassGap_eq_zero ω hφ hpos, pos_iff_ne_zero]

/-- `Macron(θ_φ)` only depends on the current `θ_φ`: a smooth change of representative
`θ ↦ η = θ + dd^c g`, `φ ↦ φ - g` (same current) leaves it unchanged. -/
theorem sourceMassGap_smooth_representative_invariance (ω : KahlerBackground n M)
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}
    (hchange : SourceSmoothBackgroundChange θ η g) {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    ∃ hφ' : (ofFixedModel n M).IsThetaPSH η (fun x => φ x - (g x : EReal)),
      sourceMassGap θ φ hφ = sourceMassGap η (fun x => φ x - (g x : EReal)) hφ' := by
  obtain ⟨hφ', hvol⟩ := sourceIVolume_smooth_representative_invariance ω hchange hφ
  refine ⟨hφ', ?_⟩
  obtain ⟨hg, hθη⟩ := (sourceSmoothBackgroundChange_iff_native θ η g).mp hchange
  have hm : sourcePotentialNonPluripolarMeasure η (fun x => φ x - (g x : EReal)) hφ' univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ univ :=
    congrArg (fun μ : Measure M => μ univ)
      (SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
        (θ := fun _ : Fin n => atlasClosedFormToNative θ)
        (η := fun _ : Fin n => atlasClosedFormToNative η)
        (u := fun _ => φ) (f := fun _ => g)
        (fun _ => hg) (fun _ => hθη)
        (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1))
  unfold sourceMassGap
  rw [hvol, hm]

end SGPT.IGood
