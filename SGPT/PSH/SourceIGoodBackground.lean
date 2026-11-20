import SGPT.PSH.SourceIVolumeGoodness
import SGPT.PSH.AtlasQPSHAddition
import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence

/-! # Original I-goodness and positive admissible backgrounds

The complete source route is in `source-i-good-background.tex`.
The same actual closed forms and original potential are retained.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual source sum retains every coefficient of the same native sum. -/
theorem sourceNativeClosedForm_add
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    atlasClosedFormToNative (θ.add σ) =
      atlasClosedFormToNative θ + atlasClosedFormToNative σ := rfl

/-- The same original potential is PSH in the actual enlarged background. -/
theorem sourceThetaPSH_add_kahler (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH (θ.add (nativeClosedFormToAtlas ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) ω.isSemipositive

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Genuine positive enlarged mass is produced without positive original mass. -/
theorem sourcePositiveMass_add_kahler (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    0 < sourcePotentialNonPluripolarMeasure
      (θ.add (nativeClosedFormToAtlas ω.form)) u (sourceThetaPSH_add_kahler ω hu) univ := by
  change HasPositivePotentialMass
    (atlasClosedFormToNative (θ.add (nativeClosedFormToAtlas ω.form))) u _
  simpa only [one_smul, sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip] using
    SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) zero_lt_one

/-- Original I-goodness is unchanged by an actual Kähler enlargement. -/
theorem sourceIGoodWith_iff_add_kahler (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceIGoodWith θ u hu ↔
      sourceIGoodWith (θ.add (nativeClosedFormToAtlas ω.form)) u
        (sourceThetaPSH_add_kahler ω hu) := by
  rw [sourceIGoodWith_iff_native, sourceIGoodWith_iff_native]
  simpa only [sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip] using
    IGoodPositiveBackgroundIndependence.iGoodWith_iff_add_kahler ω
      (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hpos

/-- Whole original `lma:Igoodinsenspert`, with the two literal envelope equalities. -/
theorem sourcePI_eq_iff_add_kahler (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    (sourceSingularityEnvelope θ u = sourceIEnvelope θ u) ↔
      sourceSingularityEnvelope (θ.add (nativeClosedFormToAtlas ω.form)) u =
        sourceIEnvelope (θ.add (nativeClosedFormToAtlas ω.form)) u := by
  simpa only [sourceIGoodWith, hpos, sourcePositiveMass_add_kahler ω hu, true_and]
    using sourceIGoodWith_iff_add_kahler ω hu hpos

/-- Arbitrary actual closed backgrounds are retained, with positive mass in each. -/
theorem sourceIGoodWith_iff_positive_background (ω : KahlerBackground n M)
    {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH σ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hpos' : 0 < sourcePotentialNonPluripolarMeasure σ u hv univ) :
    sourceIGoodWith θ u hu ↔ sourceIGoodWith σ u hv := by
  rw [sourceIGoodWith_iff_native, sourceIGoodWith_iff_native]
  exact IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential ω
    (atlasClosedFormToNative θ) (atlasClosedFormToNative σ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential σ u).mp hv) hpos hpos'

/-- The original existential predicate equals goodness in every positive background. -/
theorem sourceIGood_iff_with_positive_background (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceIGood (n := n) u ↔ sourceIGoodWith θ u hu := by
  constructor
  · rintro ⟨σ, hv, hg⟩
    exact (sourceIGoodWith_iff_positive_background ω hv hu hg.1 hpos).mp hg
  · intro hg
    exact ⟨θ, hu, hg⟩

/-- No chosen positive admissible background changes the original envelope test. -/
theorem sourceIGood_iff_PI_eq (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceIGood (n := n) u ↔ sourceSingularityEnvelope θ u = sourceIEnvelope θ u := by
  rw [sourceIGood_iff_with_positive_background ω hu hpos, sourceIGoodWith]
  exact and_iff_right hpos

end SGPT.PSH.VariableComplexAtlas
