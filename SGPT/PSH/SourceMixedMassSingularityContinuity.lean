import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.ActualNativeMixedMassContinuity

/-! # Whole original mixed-mass continuity in the singularity topologies

Each independent original source dS topology and the unchanged actual mixed
measure are retained. All zero masses and dimension zero are included. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Whole original `thm:convdS`, strengthened to arbitrary incoming filters:
independent original big backgrounds, genuine source PSH and exact source dS
slot topologies give the actual mixed-mass limit with no positivity premises. -/
theorem tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology
    (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i ↦ ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a))
        (sourceSingularityTopology ω (θ a) (hbig a)) (u a))) :
    Tendsto (fun i ↦ sourceMixedNonPluripolarMass θ
      (fun a ↦ (ui i a).val) (fun a ↦ (ui i a).property)) F
      (𝓝 (sourceMixedNonPluripolarMass θ (fun a ↦ (u a).val) (fun a ↦ (u a).property))) := by
  have hnlim (a : Fin n) : Tendsto
      (fun i ↦ sourceThetaPotentialL1EquivNative (θ a) (ui i a)) F
      (@nhds (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative (θ a)).val)
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
          ω (atlasClosedFormToNative (θ a)) (hbig a)).toUniformSpace.toTopologicalSpace
        (sourceThetaPotentialL1EquivNative (θ a) (u a))) := by
    let := sourceSingularityPseudoMetricSpace ω (θ a) (hbig a)
    let : UniformSpace (SourceThetaPotentialL1 (θ a)) :=
      sourceSingularityUniformSpace ω (θ a) (hbig a)
    let : TopologicalSpace (SourceThetaPotentialL1 (θ a)) :=
      sourceSingularityTopology ω (θ a) (hbig a)
    let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative (θ a)) (hbig a)
    let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative (θ a)).val) :=
      (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
        ω (atlasClosedFormToNative (θ a)) (hbig a)).toUniformSpace
    let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative (θ a)).val) :=
      (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
        ω (atlasClosedFormToNative (θ a)) (hbig a)).toUniformSpace.toTopologicalSpace
    have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative (θ a)) :=
      Topology.IsInducing.induced _
    exact hmap.tendsto_nhds_iff.mp (hlim a)
  simpa only [sourceMixedNonPluripolarMass_eq_native] using
    ActualNativeMixedMassContinuity.tendsto_globalMixedMass_of_native
      (θ := fun a ↦ atlasClosedFormToNative (θ a)) ω hbig F
      (fun i a ↦ (isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (ui i a).property)
      (fun a ↦ (isThetaPSH_iff_nativeThetaPotential (θ a) _).mp (u a).property) hnlim

/-- The entire original conclusion on the literal actual mixed source
measures evaluated on X, rather than a replacement numerical mass object. -/
theorem tendsto_sourceMixedNonPluripolarMeasure_univ_of_sourceSingularityTopology
    (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i ↦ ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a))
        (sourceSingularityTopology ω (θ a) (hbig a)) (u a))) :
    Tendsto (fun i ↦ sourceMixedNonPluripolarMeasure θ
      (fun a ↦ (ui i a).val) (fun a ↦ (ui i a).property) univ) F
      (𝓝 (sourceMixedNonPluripolarMeasure θ
        (fun a ↦ (u a).val) (fun a ↦ (u a).property) univ)) :=
  tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology ω θ hbig F ui u hlim

/-- Actual Kähler finiteness is obtained before composing the proved actual
mass limit with realification; no target finiteness certificate is assumed. -/
theorem tendsto_sourceMixedNonPluripolarMassReal_of_sourceSingularityTopology
    (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ a))))
    {I : Type*} (F : Filter I)
    (ui : I → (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (u : (a : Fin n) → SourceThetaPotentialL1 (θ a))
    (hlim : ∀ a, Tendsto (fun i ↦ ui i a) F
      (@nhds (SourceThetaPotentialL1 (θ a))
        (sourceSingularityTopology ω (θ a) (hbig a)) (u a))) :
    Tendsto (fun i ↦ (sourceMixedNonPluripolarMass θ
      (fun a ↦ (ui i a).val) (fun a ↦ (ui i a).property)).toReal) F
      (𝓝 (sourceMixedNonPluripolarMass θ
        (fun a ↦ (u a).val) (fun a ↦ (u a).property)).toReal) :=
  (ENNReal.tendsto_toReal
    (sourceMixedNonPluripolarMass_lt_top ω θ (fun a ↦ (u a).val) (fun a ↦ (u a).property)).ne).comp
    (tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology ω θ hbig F ui u hlim)

end SGPT.PSH.VariableComplexAtlas
