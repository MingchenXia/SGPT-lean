import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingPNets

/-! # Whole original positive-mass singularity completeness

Actual source Cauchy filters and original mass bounds produce a genuine
model limit. Decreasing global P-types supply their own Cauchyness. -/

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

/-- Whole original Cauchy-net clause of `cor:completenessdS`, strengthened
to arbitrary filters. Original masses and actual dS Cauchyness are the only
analytic hypotheses; model membership, mass and limit are all produced. -/
theorem sourceSingularity_exists_model_limit_of_cauchy_map
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ) {δ : ℝ}
    (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Cauchy (map ui F) → ∃ U : SourceThetaPotentialL1 θ,
      SourceModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ sourcePotentialNonPluripolarMeasure θ U.val U.property univ ∧
      Tendsto ui F (𝓝 U) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  intro hcauchy
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hisom : Isometry (sourceThetaPotentialL1EquivNative θ) := fun _ _ ↦ rfl
  have hn : Cauchy (map (fun i ↦ sourceThetaPotentialL1EquivNative θ (ui i)) F) := by
    simpa only [Filter.map_map, Function.comp_def] using hcauchy.map hisom.uniformContinuous
  obtain ⟨U, hU, hδU, hlim⟩ :=
    SingularCanonicalSingularityPositiveCauchyFilters.exists_model_limit_of_cauchy_map
      ω (atlasClosedFormToNative θ) hbig F
      (fun i ↦ sourceThetaPotentialL1EquivNative θ (ui i)) hδ hstage hn
  let V : SourceThetaPotentialL1 θ := (sourceThetaPotentialL1EquivNative θ).symm U
  refine ⟨V, (sourceModelPotential_iff_native θ _).mpr hU, hδU, ?_⟩
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  apply hmap.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, V, Equiv.apply_symm_apply] using hlim

/-- Actual global P-antitonicity manufactures original dS Cauchyness on the
entire directed net, without positive-mass or limiting-potential premises. -/
theorem sourceSingularity_cauchy_map_of_antitone_sourcePOrder
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → SourceThetaPotentialL1 θ)
    (horder : ∀ i j, i ≤ j → GlobalPComparison.sourcePOrder (n := n) (ui j).val (ui i).val) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Cauchy (map ui atTop) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hisom : Isometry (sourceThetaPotentialL1EquivNative θ) := fun _ _ ↦ rfl
  apply hisom.isUniformInducing.cauchy_map_iff.mp
  simpa only [Filter.map_map, Function.comp_def] using
    SingularCanonicalSingularityDecreasingPNets.cauchy_map_of_antitone_sourcePOrder
      ω (atlasClosedFormToNative θ) hbig
      (fun i ↦ sourceThetaPotentialL1EquivNative θ (ui i)) horder

/-- The whole original decreasing-type assertion, with original positive
masses and no Cauchy/limit certificate. It strengthens pointwise decrease
to the book's genuine global P-type decrease. -/
theorem sourceSingularity_exists_model_limit_of_antitone_sourcePOrder
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → SourceThetaPotentialL1 θ)
    (horder : ∀ i j, i ≤ j → GlobalPComparison.sourcePOrder (n := n) (ui j).val (ui i).val)
    {δ : ℝ} (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ) :
    ∃ U : SourceThetaPotentialL1 θ, SourceModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ sourcePotentialNonPluripolarMeasure θ U.val U.property univ ∧
      Tendsto ui atTop (@nhds (SourceThetaPotentialL1 θ)
        (sourceSingularityTopology ω θ hbig) U) := by
  exact sourceSingularity_exists_model_limit_of_cauchy_map ω θ hbig atTop ui hδ hstage
    (sourceSingularity_cauchy_map_of_antitone_sourcePOrder ω θ hbig ui horder)

/-- The literal pointwise-decreasing-net clause of `cor:completenessdS`.
The global P order needed for the complete producer is manufactured here. -/
theorem sourceSingularity_exists_model_limit_of_antitone
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → SourceThetaPotentialL1 θ) (hanti : Antitone fun i ↦ (ui i).val)
    {δ : ℝ} (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θ (ui i).val (ui i).property univ) :
    ∃ U : SourceThetaPotentialL1 θ, SourceModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ sourcePotentialNonPluripolarMeasure θ U.val U.property univ ∧
      Tendsto ui atTop (@nhds (SourceThetaPotentialL1 θ)
        (sourceSingularityTopology ω θ hbig) U) := by
  apply sourceSingularity_exists_model_limit_of_antitone_sourcePOrder ω θ hbig ui ?_ hδ hstage
  intro i j hij
  exact SingularGlobalPOrder.sourcePOrder_of_moreSingularOn ω
    (atlasClosedFormToNative θ) (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (ui j).property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (ui i).property)
    (MoreSingularOn.of_le fun x _ ↦ hanti hij x)

end SGPT.PSH.VariableComplexAtlas
