import SGPT.Envelopes.SourceEqualMassEnvelope
import SGPT.Envelopes.SourceMixedEnergyIntegrability
import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.SourcePIComparison
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.PSH.SourceIVolumeGoodness

/-!
# Interpolation between the `I`-envelope and the `P`-envelope

Source: Chapter "The envelope operators", `rmk:envelopes:L2443`. For
`φ ∈ PSH(X,θ)_{>0}` and `j ∈ {0, …, n}` the remark defines
`P_{θ,j}[φ] = usc sup {ψ ∈ PSH(X,θ) : ψ ≤ 0, φ ⪯ ψ,
  ∫ θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j} = ∫ θ_ψ^j ∧ θ_{P_θ[ψ]_I}^{n-j}}`
and states that `j = 0` and `j = n` recover the `I`- and `P`-envelopes. Both endpoint
statements are proved here (`sourceInterpolatedEnvelope_zero`,
`sourceInterpolatedEnvelope_last`). The remark's further assertion that one *could show*
that every `P_{θ,j}` is a projection operator is recorded as the proposition
`SourceInterpolatedEnvelopeProjection`; it is not proved here.

The mixed mass `∫ θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j}` is `sourceEndpointMixedMeasure` with the
first `j` slots equal to `φ` and the remaining `n - j` slots equal to `P_θ[φ]_I`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}

/-- The mixed mass `∫_X θ_φ^j ∧ θ_{P_θ[φ]_I}^{n-j}` of `rmk:envelopes:L2443`. -/
def sourceInterpolatedMass (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (j : Fin (n + 1)) (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) : ENNReal :=
  sourceEndpointMixedMeasure θ (sourceIEnvelope θ u) u (isThetaPSH_sourceIEnvelope hu) hu j univ

/-- The competitors of `P_{θ,j}[φ]` in `rmk:envelopes:L2443`. -/
def sourceInterpolatedEnvelopeCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (j : Fin (n + 1)) (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) :=
  {v : M → EReal // ∃ hv : (ofFixedModel n M).IsThetaPSH θ v, v ≤ 0 ∧
    SGPT.PSH.SingularityLE u v ∧ sourceInterpolatedMass θ j u hu = sourceInterpolatedMass θ j v hv}

/-- Source `rmk:envelopes:L2443`: the interpolating envelope `P_{θ,j}[φ]`. -/
def sourceInterpolatedEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (j : Fin (n + 1)) (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) : M → EReal :=
  uscSup (fun v : sourceInterpolatedEnvelopeCompetitors θ j u hu => v.1)

omit [BorelSpace M] in
/-- For `j = n` the interpolated mass is the non-pluripolar mass `∫_X θ_φ^n`. -/
theorem sourceInterpolatedMass_last (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceInterpolatedMass θ (Fin.last n) u hu = sourcePotentialNonPluripolarMeasure θ u hu univ := by
  unfold sourceInterpolatedMass
  rw [sourceEndpointMixedMeasure_last]

omit [BorelSpace M] in
/-- For `j = 0` the interpolated mass is the volume `vol(θ, φ) = ∫_X θ_{P_θ[φ]_I}^n`. -/
theorem sourceInterpolatedMass_zero (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceInterpolatedMass θ ⟨0, Nat.zero_lt_succ n⟩ u hu = sourceIVolume θ u hu := by
  unfold sourceInterpolatedMass sourceIVolume
  rw [sourceEndpointMixedMeasure_zero]

/-- Source `rmk:envelopes:L2443`, the case `j = n`: `P_{θ,n}[φ] = P_θ[φ]` for
`φ ∈ PSH(X,θ)_{>0}`. -/
theorem sourceInterpolatedEnvelope_last (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceInterpolatedEnvelope θ (Fin.last n) u hu = sourceSingularityEnvelope θ u := by
  apply le_antisymm
  · refine uscRegularization_le (upperSemicontinuous_sourceSingularityEnvelope θ u)
      (fun x => iSup_le fun v => ?_)
    obtain ⟨hv, hv0, huv, hmass⟩ := v.2
    have hm := (sourceInterpolatedMass_last θ u hu).symm.trans
      (hmass.trans (sourceInterpolatedMass_last θ v.1 hv))
    exact le_sourceSingularityEnvelope_of_equalMass ω hu hpos ⟨v.1, hv, hv0, huv, hm⟩ x
  · intro x
    have hc := (sourceEnvelopeEqualMassCompetitor ω hu).2
    obtain ⟨hP, hP0, huP, hmass⟩ := hc
    refine le_trans ?_ (le_uscRegularization _ x)
    exact le_iSup (fun v : sourceInterpolatedEnvelopeCompetitors θ (Fin.last n) u hu => v.1 x)
      ⟨sourceSingularityEnvelope θ u, hP, hP0, huP,
        (sourceInterpolatedMass_last θ u hu).trans
          (hmass.trans (sourceInterpolatedMass_last θ _ hP).symm)⟩

/-- Source `rmk:envelopes:L2443`, the case `j = 0`: `P_{θ,0}[φ] = P_θ[φ]_I` for
`φ ∈ PSH(X,θ)_{>0}`. -/
theorem sourceInterpolatedEnvelope_zero (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceInterpolatedEnvelope θ ⟨0, Nat.zero_lt_succ n⟩ u hu = sourceIEnvelope θ u := by
  have hI := isThetaPSH_sourceIEnvelope hu
  have hvolpos : 0 < sourcePotentialNonPluripolarMeasure θ (sourceIEnvelope θ u) hI univ :=
    lt_of_lt_of_le hpos (sourceMass_le_iVolume ω hu)
  have huI : SGPT.PSH.SingularityLE u (sourceIEnvelope θ u) := by
    have h1 : SGPT.PSH.SingularityLE u (sourceSingularityEnvelope θ u) :=
      (sourceEnvelopeEqualMassCompetitor ω hu).2.2.2.1
    obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h1
    exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun x =>
      (hC x).trans (add_le_add_left (sourcePEnvelope_le_IEnvelope hu x) _)⟩
  apply le_antisymm
  · refine uscRegularization_le (upperSemicontinuous_sourceIEnvelope θ u)
      (fun x => iSup_le fun v => ?_)
    obtain ⟨hv, hv0, huv, hmass⟩ := v.2
    have hm := (sourceInterpolatedMass_zero θ u hu).symm.trans
      (hmass.trans (sourceInterpolatedMass_zero θ v.1 hv))
    have hvI := isThetaPSH_sourceIEnvelope hv
    -- `v ≤ P_θ[v]_I ≤ P_θ[P_θ[u]_I] = P_θ[u]_I`
    have h1 : v.1 ≤ sourceIEnvelope θ v.1 :=
      le_sourceIEnvelope hv hv0 (sourceIEquivalent_refl ⟨θ, hv⟩)
    have hmono : sourceIEnvelope θ u ≤ sourceIEnvelope θ v.1 :=
      sourceIEnvelope_mono_of_singularityLE hu hv huv
    have h2 : sourceIEnvelope θ v.1 ≤ sourceSingularityEnvelope θ (sourceIEnvelope θ u) :=
      le_sourceSingularityEnvelope_of_equalMass ω hI hvolpos
        ⟨sourceIEnvelope θ v.1, hvI, sourceIEnvelope_le_zero θ v.1,
          (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by
            simpa only [EReal.coe_zero, add_zero] using hmono x⟩, hm⟩
    rw [sourcePEnvelope_iEnvelope hu] at h2
    exact (h1 x).trans (h2 x)
  · intro x
    refine le_trans ?_ (le_uscRegularization _ x)
    refine le_iSup (fun v : sourceInterpolatedEnvelopeCompetitors θ ⟨0, Nat.zero_lt_succ n⟩ u hu =>
      v.1 x) ⟨sourceIEnvelope θ u, hI, sourceIEnvelope_le_zero θ u, huI, ?_⟩
    refine (sourceInterpolatedMass_zero θ u hu).trans
      (Eq.trans ?_ (sourceInterpolatedMass_zero θ _ hI).symm)
    unfold sourceIVolume
    exact congrArg (fun μ : Measure M => μ univ)
      (sourcePotentialNonPluripolarMeasure_congr (sourceIEnvelope_idempotent hu).symm _ _)

/-- The (unproved) assertion of `rmk:envelopes:L2443` that every `P_{θ,j}` is a projection
operator on `PSH(X,θ)_{>0}`: `P_{θ,j}[φ]` has positive mass and
`P_{θ,j}[P_{θ,j}[φ]] = P_{θ,j}[φ]`. Stated, not proved. -/
def SourceInterpolatedEnvelopeProjection (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (j : Fin (n + 1)) : Prop :=
  ∀ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u),
    0 < sourcePotentialNonPluripolarMeasure θ u hu univ →
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ (sourceInterpolatedEnvelope θ j u hu),
      0 < sourcePotentialNonPluripolarMeasure θ _ hP univ ∧
      sourceInterpolatedEnvelope θ j (sourceInterpolatedEnvelope θ j u hu) hP =
        sourceInterpolatedEnvelope θ j u hu

end SGPT.PSH.VariableComplexAtlas
