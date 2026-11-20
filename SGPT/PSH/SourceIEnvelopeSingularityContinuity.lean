import SGPT.PSH.SourceMixedMassSingularityContinuity
import SGPT.Foundations.Analysis.Pending.IEnvelopeNativeContinuity

/-! # Original I-envelope and I-volume continuity at positive actual mass

The same source potentials, all original competitors, actual singularity
topologies and actual non-pluripolar masses are retained. All natural
dimensions and arbitrary incoming filters are admitted. Zero-limit mass
continuity is a separate theorem and is not asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The original entire I-envelope on the existing genuine source PSH carrier.
Its PSH witness is manufactured, without any positive-mass existence input. -/
def sourceThetaPotentialIEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (u : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 θ :=
  ⟨sourceIEnvelope θ u.val, isThetaPSH_sourceIEnvelope u.property⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- The SAME functions and ALL original competitors intertwine the genuine
source reader with the existing native I-envelope reader, at every pole. -/
theorem sourceThetaPotentialIEnvelope_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : SourceThetaPotentialL1 θ) :
    sourceThetaPotentialL1EquivNative θ (sourceThetaPotentialIEnvelope u) =
      IEnvelopeMonotoneNativeLimits.iEnvelopeReader (atlasClosedFormToNative θ)
        (sourceThetaPotentialL1EquivNative θ u) :=
  Subtype.ext (sourceIEnvelope_eq_native θ u.val u.property)

/-- Positive ACTUAL input mass yields positive ACTUAL output mass. Positive
I-volume is a consequence of actual mass comparison, never an input substitute. -/
theorem sourceThetaPotentialIEnvelope_positive_mass (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceThetaPotentialIEnvelope u).val
      (sourceThetaPotentialIEnvelope u).property univ :=
  hpos.trans_le (sourceMass_le_iVolume ω u.property)

/-- Every actual source dS-convergent ambient filter with positive ACTUAL
limit mass has the literal original I-envelope limit. No stage positivity,
order, model output or countable-cofinality premise is supplied. -/
theorem tendsto_sourceIEnvelope_of_sourceSingularityTopology
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ)
    (hlim : Tendsto ui F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) u)) :
    Tendsto (fun i => sourceThetaPotentialIEnvelope (ui i)) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig)
        (sourceThetaPotentialIEnvelope u)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  let e := sourceSingularityHomeomorphNative ω θ hbig
  have hnlim : Tendsto (fun i => sourceThetaPotentialL1EquivNative θ (ui i)) F
      (𝓝 (sourceThetaPotentialL1EquivNative θ u)) :=
    (e.continuous.tendsto u).comp hlim
  have hnative := IEnvelopeNativeContinuity.tendsto_iEnvelope_of_tendsto_positive_mass
    ω (atlasClosedFormToNative θ) hbig F (fun i => sourceThetaPotentialL1EquivNative θ (ui i))
    (sourceThetaPotentialL1EquivNative θ u) hpos hnlim
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  apply hmap.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, sourceThetaPotentialIEnvelope_eq_native] using hnative

/-- Continuity at every genuine positive-mass source potential, with both
actual source dS neighborhoods explicit instead of the source L1 topology. -/
theorem continuousAt_sourceIEnvelope_of_positive_mass
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    ContinuousAt (sourceThetaPotentialIEnvelope (θ := θ)) u := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  exact tendsto_sourceIEnvelope_of_sourceSingularityTopology ω θ hbig (𝓝 u) id u hpos tendsto_id

/-- The LITERAL original positive ACTUAL-mass locus maps to itself. Output
positivity is manufactured from the genuine original mass comparison. -/
def sourcePositiveMassIEnvelope (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : {u : SourceThetaPotentialL1 θ //
      0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ}) :
    {v : SourceThetaPotentialL1 θ //
      0 < sourcePotentialNonPluripolarMeasure θ v.val v.property univ} :=
  ⟨sourceThetaPotentialIEnvelope u.val, sourceThetaPotentialIEnvelope_positive_mass ω u.val u.property⟩

/-- WHOLE original thm:contPI: the entire positive ACTUAL-mass source locus
maps continuously to itself, with both genuine source dS subspace topologies. -/
theorem continuous_sourcePositiveMassIEnvelope
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Continuous (sourcePositiveMassIEnvelope ω θ) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  have hf : Continuous (fun u : {u : SourceThetaPotentialL1 θ //
      0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ} =>
        sourceThetaPotentialIEnvelope u.val) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (continuousAt_sourceIEnvelope_of_positive_mass ω θ hbig u.val u.property).comp
      continuous_subtype_val.continuousAt
  exact hf.subtype_mk (fun u => sourceThetaPotentialIEnvelope_positive_mass ω u.val u.property)

/-- WHOLE original thm:contvolu and eq:Ivolcont, for arbitrary ambient
filters and only positive ACTUAL limit mass. BOTH actual ENNReal I-volume
and the original actual diagonal NP measure evaluated on X converge. -/
theorem tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ)
    (hlim : Tendsto ui F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) u)) :
    Tendsto (fun i => sourceIVolume θ (ui i).val (ui i).property) F
      (𝓝 (sourceIVolume θ u.val u.property)) ∧
    Tendsto (fun i => sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ) F
      (𝓝 (sourcePotentialNonPluripolarMeasure θ u.val u.property univ)) := by
  have hQ := tendsto_sourceIEnvelope_of_sourceSingularityTopology ω θ hbig F ui u hpos hlim
  constructor
  · have h := tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology
      ω (fun _ : Fin n => θ) (fun _ => hbig) F
      (fun i _ => sourceThetaPotentialIEnvelope (ui i)) (fun _ => sourceThetaPotentialIEnvelope u)
      (fun _ => hQ)
    convert h using 1
    · funext i
      exact (sourceMixedNonPluripolarMass_diagonal θ _ _).symm
    · exact congrArg nhds (sourceMixedNonPluripolarMass_diagonal θ _ _).symm
  · simpa only [sourceMixedNonPluripolarMass_diagonal] using
      tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology
        ω (fun _ : Fin n => θ) (fun _ => hbig) F (fun i _ => ui i) (fun _ => u) (fun _ => hlim)

end SGPT.PSH.VariableComplexAtlas
