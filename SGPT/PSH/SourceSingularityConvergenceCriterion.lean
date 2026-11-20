import SGPT.PSH.SourceSingularityDistanceConvergence
import Mathlib.Data.List.TFAE

/-! # The whole original three-way singularity convergence criterion

The complete source-first mathematical route is in
`source-singularity-convergence-criterion.tex`. All functions and endpoint
measures are the existing literal original ones, with their actual dS topology.
-/

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

/-- The SAME actual maximum family is genuinely ordered above its target;
the global positive common background is produced internally, including
zero original masses. Every original endpoint index and every filter occur. -/
theorem tendsto_sourceSingularityTopology_maximum_iff_mixedMass
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    Tendsto (fun i ↦ sourceThetaPotentialMaximum (w i) v) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) v) ↔
    ∀ j : Fin (n + 1),
      Tendsto (fun i ↦ sourceMinimalMixedMass ω θ hbig
        (sourceThetaPotentialMaximum (w i) v).val
        (sourceThetaPotentialMaximum (w i) v).property j)
        F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  have horder (i : I) : GlobalPComparison.sourcePOrder (n := n)
      v.val (sourceThetaPotentialMaximum (w i) v).val :=
    SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω
      (atlasClosedFormToNative θ) (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp
        (sourceThetaPotentialMaximum (w i) v).property)
      (MoreSingularOn.of_le fun _ _ ↦ le_max_right _ _)
  exact tendsto_sourceSingularityTopology_iff_mixedMass_of_sourcePOrder
    ω θ hbig F (fun i ↦ sourceThetaPotentialMaximum (w i) v) v horder

/-- Original items 1 and 2 of `cor:dsconvcrit`, on the entire actual source
carrier. No order, model, original positivity or dimension restriction is input. -/
theorem tendsto_sourceSingularityTopology_iff_maximum_and_mixedMass
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    Tendsto w F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) v) ↔
    (Tendsto (fun i ↦ sourceThetaPotentialMaximum (w i) v) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) v) ∧
      ∀ j : Fin (n + 1),
        Tendsto (fun i ↦ sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j)
          F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j))) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  have hboth := tendsto_sourceSingularityTopology_iff_mixedMass ω θ hbig F w v
  have hmax := tendsto_sourceSingularityTopology_maximum_iff_mixedMass ω θ hbig F w v
  constructor
  · intro h
    have hm := hboth.mp h
    exact ⟨hmax.mpr (fun j ↦ (hm j).2), fun j ↦ (hm j).1⟩
  · rintro ⟨hmaxlim, hm⟩
    exact hboth.mpr (fun j ↦ ⟨hm j, hmax.mp hmaxlim j⟩)

/-- WHOLE original `cor:dsconvcrit`: all three numbered assertions and both
literal families of original mixed-mass limits, for every filter and n=0. -/
theorem sourceSingularityConvergence_three_way
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    List.TFAE [
      Tendsto w F
        (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) v),
      Tendsto (fun i ↦ sourceThetaPotentialMaximum (w i) v) F
        (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) v) ∧
        ∀ j : Fin (n + 1),
          Tendsto (fun i ↦ sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j)
            F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)),
      ∀ j : Fin (n + 1),
        Tendsto (fun i ↦ sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j)
          F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)) ∧
        Tendsto (fun i ↦ sourceMinimalMixedMass ω θ hbig
          (sourceThetaPotentialMaximum (w i) v).val
          (sourceThetaPotentialMaximum (w i) v).property j)
          F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j))] := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  have h12 := tendsto_sourceSingularityTopology_iff_maximum_and_mixedMass ω θ hbig F w v
  have h13 := tendsto_sourceSingularityTopology_iff_mixedMass ω θ hbig F w v
  exact List.tfae_cons_cons.mpr
    ⟨h12, List.tfae_cons_cons.mpr ⟨h12.symm.trans h13, List.tfae_singleton _⟩⟩

end SGPT.PSH.VariableComplexAtlas
