import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.SingularPEnvelopeMixedMassPreservation
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

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

/-- The literal ordinary envelope preserves the SAME diagonal mass, including zero. -/
theorem sourceOrdinaryEnvelope_diagonalMass_eq (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
        (sourceOrdinaryEnvelope_genuine hu) univ =
      sourcePotentialNonPluripolarMeasure θ u hu univ := by
  have hnu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnP := (isThetaPSH_iff_nativeThetaPotential θ _).mp
    (sourceOrdinaryEnvelope_genuine hu)
  simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass,
    sourceSingularityEnvelope_eq_native] using
    (singularityEnvelopeMassPreserving ω (atlasClosedFormToNative θ) u hnu
      (by simpa only [← sourceSingularityEnvelope_eq_native] using hnP))

/-- WHOLE original independent mixed mass preservation, with no positive-mass premise. -/
theorem sourceOrdinaryEnvelope_mixedMass_eq (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceMixedNonPluripolarMass θ (fun i => sourceSingularityEnvelope (θ i) (u i))
        (fun i => sourceOrdinaryEnvelope_genuine (hu i)) =
      sourceMixedNonPluripolarMass θ u hu := by
  simpa only [sourceMixedNonPluripolarMass_eq_native, sourceSingularityEnvelope_eq_native] using
    (SingularPEnvelopeMixedMassPreservation.globalMixedMass_singularityEnvelope_eq ω
      (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)))

/-- Positive ORIGINAL mass produces the literal ordinary-envelope fixed point. -/
theorem sourceOrdinaryEnvelope_idempotent_of_positive_mass (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpositive : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceSingularityEnvelope θ (sourceSingularityEnvelope θ u) =
      sourceSingularityEnvelope θ u := by
  simpa only [sourceSingularityEnvelope_eq_native] using
    (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      ω (atlasClosedFormToNative θ) u
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hpositive)

/-- The original positive model fields are ALL produced from the original input. -/
theorem sourceOrdinaryEnvelope_model (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpositive : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    SourceModelPotential θ (sourceSingularityEnvelope θ u) := by
  refine ⟨sourceOrdinaryEnvelope_genuine hu,
    (sourceOrdinaryEnvelope_idempotent_of_positive_mass ω hu hpositive).symm, ?_⟩
  simpa only [sourceOrdinaryEnvelope_diagonalMass_eq ω hu] using hpositive

/-- WHOLE printed original model conclusion together with its separate mass equality. -/
theorem sourceOrdinaryEnvelope_model_and_mass (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpositive : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    SourceModelPotential θ (sourceSingularityEnvelope θ u) ∧
      sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
          (sourceOrdinaryEnvelope_genuine hu) univ =
        sourcePotentialNonPluripolarMeasure θ u hu univ :=
  ⟨sourceOrdinaryEnvelope_model ω hu hpositive, sourceOrdinaryEnvelope_diagonalMass_eq ω hu⟩

end SGPT.PSH.VariableComplexAtlas
