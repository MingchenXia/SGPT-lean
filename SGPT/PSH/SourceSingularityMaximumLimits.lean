import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed

set_option autoImplicit false
noncomputable section

/-! # Whole original maximum continuity and closed global P-order

The complete source-first proofs are in `source-singularity-maximum-limits.tex`.
The existing native theorems are reused on the unchanged original PSH carrier
through its actual SAME-function equivalence and explicit dS topology.
-/

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- WHOLE original prop:lor_dS_conv for EVERY filter, including dimension
zero and zero target masses. The actual source maximum and dS topology are
unchanged; no positive-mass or model certificate is an input. -/
theorem tendsto_sourceThetaPotentialMaximum (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (a b : I → SourceThetaPotentialL1 θ)
    (p q : SourceThetaPotentialL1 θ)
    (ha : Tendsto a F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) p))
    (hb : Tendsto b F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) q)) :
    Tendsto (fun i => sourceThetaPotentialMaximum (a i) (b i)) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig)
        (sourceThetaPotentialMaximum p q)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have han := hmap.tendsto_nhds_iff.mp ha
  have hbn := hmap.tendsto_nhds_iff.mp hb
  have hnative := SingularNativeMaximumContinuity.tendsto_native_max
    ω (atlasClosedFormToNative θ) hbig F
    (fun i => sourceThetaPotentialL1EquivNative θ (a i))
    (fun i => sourceThetaPotentialL1EquivNative θ (b i))
    (sourceThetaPotentialL1EquivNative θ p) (sourceThetaPotentialL1EquivNative θ q) han hbn
  apply hmap.tendsto_nhds_iff.mpr
  convert hnative using 1
  rfl

/-- WHOLE original prop:dsconvpresorder. A nontrivial filter and eventual
actual global P-order suffice; every nonempty directed original net supplies
that filter qualification. Both limits use the explicitly selected dS topology. -/
theorem sourcePOrder_of_sourceSingularityLimits (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) [F.NeBot] (a b : I → SourceThetaPotentialL1 θ)
    (p q : SourceThetaPotentialL1 θ)
    (ha : Tendsto a F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) p))
    (hb : Tendsto b F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) q))
    (horder : ∀ᶠ i in F, GlobalPComparison.sourcePOrder (n := n) (a i).val (b i).val) :
    GlobalPComparison.sourcePOrder (n := n) p.val q.val := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (r : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ r).val = r.val := rfl
  have horderNative : ∀ᶠ i in F, SingularGlobalPOrder.SourcePOrder (n := n)
      (sourceThetaPotentialL1EquivNative θ (a i)).val
      (sourceThetaPotentialL1EquivNative θ (b i)).val := by
    simpa only [hread] using horder
  have h := SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
    ω (atlasClosedFormToNative θ) hbig F
    (fun i => sourceThetaPotentialL1EquivNative θ (a i))
    (fun i => sourceThetaPotentialL1EquivNative θ (b i))
    (sourceThetaPotentialL1EquivNative θ p) (sourceThetaPotentialL1EquivNative θ q)
    (hmap.tendsto_nhds_iff.mp ha) (hmap.tendsto_nhds_iff.mp hb) horderNative
  simpa only [hread] using h

end SGPT.PSH.VariableComplexAtlas
