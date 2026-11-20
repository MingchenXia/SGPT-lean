import SGPT.PSH.SourceIEnvelope
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.IGoodBasic

/-! # Original I-projection, volume and I-goodness

The analytic I-envelope theorem is reused on the literal original all-chart
domain. The whole projection includes the unregularized supremum assertion.
Volume keeps the actual non-pluripolar measure and the original background.
Goodness quantifies over all smooth closed real (1,1) backgrounds.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- A genuine original reference internally produces a normalized actual
I-equivalent competitor; nonemptiness is not an extra hypothesis. -/
theorem sourceICompetitors_nonempty
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    Nonempty (sourceICompetitors θ φ) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  obtain ⟨v, ⟨hv, hv0⟩, hvφ⟩ := iSingularityCompetitors_nonempty hn
  have hv' := (isThetaPSH_iff_nativeThetaPotential θ v).mpr hv
  exact ⟨⟨v, hv', hv0, (sourceIEquivalent_iff_native ⟨θ, hv'⟩ ⟨θ, hφ⟩).mpr hvφ⟩⟩

/-- Actual regularity for every genuine source theta-PSH reference. -/
theorem isThetaPSH_sourceIEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceIEnvelope θ φ) :=
  isThetaPSH_sourceIEnvelope_of_nonempty (sourceICompetitors_nonempty hφ)

/-- The original reference and its original envelope have the same actual
multiplier germs in every chart at every positive real exponent. -/
theorem sourceIEquivalent_iEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEquivalent (ofFixedModel n M) φ (sourceIEnvelope θ φ) := by
  have hψ := isThetaPSH_sourceIEnvelope hφ
  apply (sourceIEquivalent_iff_native ⟨θ, hφ⟩ ⟨θ, hψ⟩).mpr
  rw [sourceIEnvelope_eq_native θ φ hφ]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact iEquivalent_iSingularityEnvelope (atlasClosedFormToNative θ).val
    θ.closed θ.typeOneOne hn.1.hasSmoothLocalPotentials φ hn

theorem sourceIEnvelope_idempotent
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEnvelope θ (sourceIEnvelope θ φ) = sourceIEnvelope θ φ :=
  (sourceIEnvelope_eq_of_equivalent (sourceIEquivalent_iEnvelope hφ)).symm

/-- The output itself is an actual original competitor. Thus the entire
unregularized supremum already equals the original I-envelope, even at poles. -/
theorem sourceIEnvelope_eq_rawSup
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEnvelope θ φ = fun x => ⨆ v : sourceICompetitors θ φ, v.1 x := by
  funext x
  apply le_antisymm
  · exact le_iSup (fun v : sourceICompetitors θ φ => v.1 x)
      ⟨sourceIEnvelope θ φ, isThetaPSH_sourceIEnvelope hφ,
        sourceIEnvelope_le_zero θ φ, sourceIEquivalent_symm (sourceIEquivalent_iEnvelope hφ)⟩
  · exact iSup_le fun v => le_sourceIEnvelope v.2.1 v.2.2.1 v.2.2.2 x

/-- All three clauses of the original `prop:Ienvprojection`, together. -/
theorem sourceIEnvelope_projection
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEquivalent (ofFixedModel n M) φ (sourceIEnvelope θ φ) ∧
      sourceIEnvelope θ (sourceIEnvelope θ φ) = sourceIEnvelope θ φ ∧
      sourceIEnvelope θ φ = (fun x => ⨆ v : sourceICompetitors θ φ, v.1 x) :=
  ⟨sourceIEquivalent_iEnvelope hφ, sourceIEnvelope_idempotent hφ,
    sourceIEnvelope_eq_rawSup hφ⟩

theorem sourceIEnvelope_isIModel
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIModel θ (sourceIEnvelope θ φ) :=
  ⟨isThetaPSH_sourceIEnvelope hφ, (sourceIEnvelope_idempotent hφ).symm⟩

variable [MeasurableSpace M]

/-- Original `def:volqpsh`: the same-background actual global non-pluripolar
measure of the produced I-envelope, evaluated on all of the manifold. -/
def sourceIVolume (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : ℝ≥0∞ :=
  sourcePotentialNonPluripolarMeasure θ (sourceIEnvelope θ φ)
    (isThetaPSH_sourceIEnvelope hφ) univ

theorem sourceIVolume_proof_independent
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ hφ' : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIVolume θ φ hφ = sourceIVolume θ φ hφ' := rfl

variable [BorelSpace M]

omit [BorelSpace M] in
/-- The literal source mass agrees with native I-volume for any native local
potential witness. No positive-mass or Kähler-background premise is added. -/
theorem sourceIVolume_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hlocal : HasSmoothLocalPotentials (atlasClosedFormToNative θ).val) :
    sourceIVolume θ φ hφ = iVolume (atlasClosedFormToNative θ) hlocal φ
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ) := by
  simp only [sourceIVolume, sourcePotentialNonPluripolarMeasure,
    sourceIEnvelope_eq_native θ φ hφ, iVolume, diagonalPotentialMass]

omit [BorelSpace M] [Nonempty M] in
/-- Goodness in one arbitrary original background uses the original
potential's actual mass and equality of the two entire source envelopes. -/
def sourceIGoodWith (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : Prop :=
  0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ ∧
    sourceSingularityEnvelope θ φ = sourceIEnvelope θ φ

omit [BorelSpace M] [Nonempty M] in
/-- Original `def:Igoodpot`: the witness is any smooth closed real (1,1)
background. Its actual positive-mass source potential is part of the witness. -/
def sourceIGood (φ : M → EReal) : Prop :=
  ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ), sourceIGoodWith θ φ hφ

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGoodWith_proof_independent
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ hφ' : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIGoodWith θ φ hφ ↔ sourceIGoodWith θ φ hφ' := Iff.rfl

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGoodWith_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIGoodWith θ φ hφ ↔ IGoodWith (atlasClosedFormToNative θ) φ
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ) := by
  unfold sourceIGoodWith IGoodWith
  rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native θ φ hφ]
  rfl

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGood_iff_native (φ : M → EReal) :
    sourceIGood (n := n) φ ↔ IGood (n := n) φ := by
  constructor
  · rintro ⟨θ, hφ, hg⟩
    exact ⟨atlasClosedFormToNative θ, (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ,
      (sourceIGoodWith_iff_native θ φ hφ).mp hg⟩
  · rintro ⟨θ, hφ, hg⟩
    have hφ' : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) φ := by
      apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas θ) φ).mpr
      simpa only [sourceNativeAtlasForm_roundTrip] using hφ
    refine ⟨nativeClosedFormToAtlas θ, hφ', ?_⟩
    apply (sourceIGoodWith_iff_native (nativeClosedFormToAtlas θ) φ hφ').mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using hg

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGoodWith.positiveMass
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : (ofFixedModel n M).IsThetaPSH θ φ} (h : sourceIGoodWith θ φ hφ) :
    0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ := h.1

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGoodWith.envelope_eq
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : (ofFixedModel n M).IsThetaPSH θ φ} (h : sourceIGoodWith θ φ hφ) :
    sourceSingularityEnvelope θ φ = sourceIEnvelope θ φ := h.2

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGoodWith.iGood
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : (ofFixedModel n M).IsThetaPSH θ φ} (h : sourceIGoodWith θ φ hφ) :
    sourceIGood (n := n) φ := ⟨θ, hφ, h⟩

omit [BorelSpace M] [Nonempty M] in
theorem sourceIGood.isQPSH {φ : M → EReal} (h : sourceIGood (n := n) φ) :
    (ofFixedModel n M).IsQPSH φ := by
  obtain ⟨θ, hφ, _⟩ := h
  exact ⟨θ, hφ⟩

end SGPT.PSH.VariableComplexAtlas
