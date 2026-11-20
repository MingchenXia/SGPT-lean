import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrderedConvergence
import SGPT.Foundations.Analysis.Pending.SingularDecreasingPEnvelopeNets

/-! # Whole original increasing/decreasing singularity-distance convergence

The complete source-facing route in `source-singularity-distance-convergence.tex`
precedes this implementation. Reuse the original whole PSH carrier, its actual
singularity metric/uniformity/topology and the existing genuine native proofs.
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

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual original regularized supremum is genuinely theta-PSH from
one finite upper bound. No positive-dimensional slot or limit witness is used. -/
theorem sourceIncreasingSingularitySupremum_thetaPSH
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} [Nonempty I] (w : I → SourceThetaPotentialL1 θ)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (uscRegularization (⨆ i, (w i).val)) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
      (fun i => (isThetaPSH_iff_nativeThetaPotential θ _).mp (w i).property) hC)

/-- The literal USC supremum, packaged in the existing ENTIRE source carrier. -/
def sourceIncreasingSingularitySupremum
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} [Nonempty I] (w : I → SourceThetaPotentialL1 θ)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) : SourceThetaPotentialL1 θ :=
  ⟨uscRegularization (⨆ i, (w i).val), sourceIncreasingSingularitySupremum_thetaPSH θ w hC⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Entire-function source readback, retaining every pole and dimension zero. -/
theorem sourceIncreasingSingularitySupremum_val
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} [Nonempty I] (w : I → SourceThetaPotentialL1 θ)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) :
    (sourceIncreasingSingularitySupremum θ w hC).val =
      uscRegularization (⨆ i, (w i).val) := rfl

/-- WHOLE incnetdSconv: actual finite defining distance tends to zero along
the entire directed net, with genuine limit membership produced internally. -/
theorem tendsto_sourceSingularityDistance_of_monotone
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (w : I → SourceThetaPotentialL1 θ) (hmono : Monotone fun i => (w i).val)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) :
    Tendsto (fun i => (sourceSingularityDistance ω θ hbig (w i)
      (sourceIncreasingSingularitySupremum θ w hC)).toReal) atTop (𝓝 0) := by
  simp only [sourceSingularityDistance_eq_native, sourceIncreasingSingularitySupremum_val]
  exact (SingularCanonicalSingularityIncreasing.tendsto_singularityDistance_of_monotone_uniformlyBounded
    ω (atlasClosedFormToNative θ) hbig
    (fun i => (isThetaPSH_iff_nativeThetaPotential θ _).mp (w i).property) hmono hC).2

/-- WHOLE incnetdSconv in the explicitly selected genuine source dS topology. -/
theorem tendsto_sourceSingularityTopology_of_monotone
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (w : I → SourceThetaPotentialL1 θ) (hmono : Monotone fun i => (w i).val)
    {C : ℝ} (hC : ∀ i x, (w i).val x ≤ (C : EReal)) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Tendsto w atTop (𝓝 (sourceIncreasingSingularitySupremum θ w hC)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [sourceSingularityPseudoMetricSpace_dist] using
    tendsto_sourceSingularityDistance_of_monotone ω θ hbig w hmono hC

/-- The exact printed D_n=3(n+1)C_n, using the existing SAME C_n definition. -/
def sourceSingularityMassLipschitzConstant (n : ℕ) : ℝ :=
  3 * ((n : ℝ) + 1) * sourceIThetaComparisonConstant n

theorem sourceSingularityMassLipschitzConstant_pos :
    0 < sourceSingularityMassLipschitzConstant n := by
  unfold sourceSingularityMassLipschitzConstant sourceIThetaComparisonConstant
  positivity

/-- Genuine stronger endpoint estimate, with actual finite masses and actual
finite original distance established before realification. -/
theorem sourceMinimalMixedMass_abs_sub_le
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) (j : Fin (n + 1)) :
    |(sourceMinimalMixedMass ω θ hbig u.val u.property j).toReal -
      (sourceMinimalMixedMass ω θ hbig v.val v.property j).toReal| ≤
      (((n : ℝ) + 1) * sourceIThetaComparisonConstant n) *
        (sourceSingularityDistance ω θ hbig u v).toReal := by
  simp only [sourceMinimalMixedMass_eq_native, sourceSingularityDistance_eq_native,
    sourceIThetaComparisonConstant]
  exact SingularCanonicalSingularityMassLipschitz.abs_endpointMixedMass_sub_le
    ω (atlasClosedFormToNative θ) hbig
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property) j

/-- WHOLE cor:massdiffdS: the original actual diagonal measures obey EXACT D_n,
including both zero original masses and dimension zero. -/
theorem sourcePotentialMass_abs_sub_le
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    |(sourcePotentialNonPluripolarMeasure θ u.val u.property univ).toReal -
      (sourcePotentialNonPluripolarMeasure θ v.val v.property univ).toReal| ≤
      sourceSingularityMassLipschitzConstant n *
        (sourceSingularityDistance ω θ hbig u v).toReal := by
  simpa only [sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMass,
    sourceSingularityMassLipschitzConstant, sourceIThetaComparisonConstant,
    sourceSingularityDistance_eq_native] using
    (SingularCanonicalSingularityMassLipschitz.abs_diagonalPotentialMass_sub_le
      ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)).2

/-- The exact original quantitative bound is a Lipschitz bound for the actual
source dS metric on the entire source carrier. -/
theorem sourcePotentialMass_lipschitzWith
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    LipschitzWith ⟨sourceSingularityMassLipschitzConstant n,
      le_of_lt sourceSingularityMassLipschitzConstant_pos⟩
      (fun u : SourceThetaPotentialL1 θ =>
        (sourcePotentialNonPluripolarMeasure θ u.val u.property univ).toReal) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [Real.dist_eq, sourceSingularityPseudoMetricSpace_dist]
  exact sourcePotentialMass_abs_sub_le ω θ hbig u v

/-- The full original mass uniform-continuity assertion, for the genuine
explicit dS uniformity, retaining zero original masses. -/
theorem sourcePotentialMass_uniformContinuous
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    UniformContinuous (fun u : SourceThetaPotentialL1 θ =>
      (sourcePotentialNonPluripolarMeasure θ u.val u.property univ).toReal) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  exact (sourcePotentialMass_lipschitzWith ω θ hbig).uniformContinuous

/-- WHOLE first decnetdS equivalence, strengthened to every filter with genuine
GLOBAL P-order and including original zero target/stage masses. -/
theorem tendsto_sourceSingularityTopology_iff_mixedMass_of_sourcePOrder
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (horder : ∀ i, GlobalPComparison.sourcePOrder (n := n) v.val (w i).val) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Tendsto w F (𝓝 v) ↔ ∀ j : Fin (n + 1),
      Tendsto (fun i => sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j)
        F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (a : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
  rw [hmap.tendsto_nhds_iff]
  simpa only [Function.comp_def, sourceMinimalMixedMass_eq_native, hread] using
    SingularGlobalPOrderedConvergence.tendsto_native_iff_endpointMixedMass_of_sourcePOrder
      ω (atlasClosedFormToNative θ) hbig F
      (fun i => sourceThetaPotentialL1EquivNative θ (w i))
      (sourceThetaPotentialL1EquivNative θ v) horder

/-- WHOLE positive-target decnetdS equivalence: ONLY the actual target mass
is assumed positive; all original stage positivity is manufactured internally. -/
theorem tendsto_sourceSingularityTopology_iff_mass_of_sourcePOrder_of_positive_target
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (horder : ∀ i, GlobalPComparison.sourcePOrder (n := n) v.val (w i).val)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ v.val v.property univ) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Tendsto w F (𝓝 v) ↔
      Tendsto (fun i => sourcePotentialNonPluripolarMeasure θ (w i).val (w i).property univ)
        F (𝓝 (sourcePotentialNonPluripolarMeasure θ v.val v.property univ)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (a : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
  rw [hmap.tendsto_nhds_iff]
  simpa only [Function.comp_def, sourcePotentialNonPluripolarMeasure,
    DiagonalMass.diagonalPotentialMass, hread] using
    SingularGlobalPOrderedConvergence.tendsto_native_iff_diagonalPotentialMass_of_sourcePOrder_of_positive_target
      ω (atlasClosedFormToNative θ) hbig F
      (fun i => sourceThetaPotentialL1EquivNative θ (w i))
      (sourceThetaPotentialL1EquivNative θ v) horder hpos

/-- ENTIRE eq:Pcontdecseq on the original arbitrary directed net. The actual
global P-antitonicity and true dS limit manufacture all tail/positive/model data. -/
theorem sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_tendsto
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hanti : ∀ i j, i ≤ j → GlobalPComparison.sourcePOrder (n := n) (w j).val (w i).val)
    (hlim : Tendsto w atTop (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology ω θ hbig) v))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ v.val v.property univ) :
    sourceSingularityEnvelope θ v.val = ⨅ i, sourceSingularityEnvelope θ (w i).val := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (a : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
  have hn := hmap.tendsto_nhds_iff.mp hlim
  have he := SingularDecreasingPEnvelopeNets.iInf_singularityEnvelope_eq_of_sourcePOrder_tendsto_native
    ω (atlasClosedFormToNative θ) hbig
    (fun i => sourceThetaPotentialL1EquivNative θ (w i))
    (sourceThetaPotentialL1EquivNative θ v) hanti hn hpos
  simpa only [sourceSingularityEnvelope_eq_native, hread] using he.symm

/-- The full positive decreasing-net envelope identity already follows from
the SINGLE original top-mass limit, with the book's actual P lower bound. -/
theorem sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_mass_tendsto
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hanti : ∀ i j, i ≤ j → GlobalPComparison.sourcePOrder (n := n) (w j).val (w i).val)
    (horder : ∀ i, GlobalPComparison.sourcePOrder (n := n) v.val (w i).val)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ v.val v.property univ)
    (hmass : Tendsto
      (fun i => sourcePotentialNonPluripolarMeasure θ (w i).val (w i).property univ)
      atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ v.val v.property univ))) :
    sourceSingularityEnvelope θ v.val = ⨅ i, sourceSingularityEnvelope θ (w i).val := by
  exact sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_tendsto ω θ hbig w v hanti
    ((tendsto_sourceSingularityTopology_iff_mass_of_sourcePOrder_of_positive_target
      ω θ hbig atTop w v horder hpos).mpr hmass) hpos

end SGPT.PSH.VariableComplexAtlas
