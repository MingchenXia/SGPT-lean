import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination

/-! # The original general two-potential interpolation limit

The source-first proof of `cor:lineardsconv` is in
`source-singularity-general-interpolation.tex`. The same two original inputs,
their literal convex combination and the genuine source dS topology are kept.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination
open EndpointMixedMassConvexCombination EndpointMixedMassGeneralConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal original path, with genuine PSH membership produced from
the two independent inputs on the whole closed coefficient interval. -/
def sourceGeneralInterpolation
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (t : Icc (0 : ℝ) 1)
    (u₀ u₁ : SourceThetaPotentialL1 θ) : SourceThetaPotentialL1 θ :=
  ⟨convexComb t.val u₁.val u₀.val,
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (isThetaPshPotential_convexComb_closed
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u₁.property)
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u₀.property)
        t.property.1 t.property.2)⟩

/-- The same source formula, including zero-coefficient conventions at poles. -/
theorem sourceGeneralInterpolation_val
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (t : Icc (0 : ℝ) 1)
    (u₀ u₁ : SourceThetaPotentialL1 θ) :
    (sourceGeneralInterpolation θ t u₀ u₁).val =
      fun x => ((1 - t.val : ℝ) : EReal) * u₀.val x + (t.val : EReal) * u₁.val x := by
  funext x
  exact add_comm _ _

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Whole original `cor:lineardsconv`, strengthened to arbitrary incoming
filters of genuine interior coefficients tending to zero. Neither endpoint
needs positive mass or minimal singularities, including in dimension zero. -/
theorem tendsto_sourceGeneralInterpolation_zero (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u₀ u₁ : SourceThetaPotentialL1 θ) {I : Type*} (F : Filter I)
    (t : I → Ioo (0 : ℝ) 1) (ht : Tendsto (fun i => (t i).val) F (𝓝 0)) :
    Tendsto (fun i => sourceGeneralInterpolation θ
      ⟨(t i).val, (t i).property.1.le, (t i).property.2.le⟩ u₀ u₁) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) u₀) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
    ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  apply hmap.tendsto_nhds_iff.mpr
  exact tendsto_native_general_convex_zero ω (atlasClosedFormToNative θ) hbig
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp u₁.property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp u₀.property) F t ht

end SGPT.PSH.VariableComplexAtlas
