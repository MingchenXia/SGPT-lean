import SGPT.PSH.SourceIGoodAnalyticCharacterization
import SGPT.Foundations.Analysis.Pending.IGoodNativeClosed

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
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The original globally I-good locus is closed in the actual source dS topology,
without any assumption on its original-background masses. -/
theorem sourceIGood_isClosed (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    @IsClosed (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig)
      {v | sourceIGood (n := n) v.val} := by
  let := sourceSingularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
    (atlasClosedFormToNative θ) hbig
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
      (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  let e := sourceSingularityHomeomorphNative omega θ hbig
  have h := (IGoodNativeClosed.isClosed_iGood_native omega (atlasClosedFormToNative θ)
    hbig).preimage e.continuous
  change @IsClosed (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig)
    {v | IGood (n := n) v.val} at h
  simpa only [sourceIGood_iff_native] using h

/-- Whole original cor:Igoodclosed, strengthened to eventual goodness along ANY
nontrivial filter. The original target mass may be zero. -/
theorem sourceIGood_of_tendsto {I : Type*} (F : Filter I) [NeBot F]
    (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (v : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hgood : ∀ᶠ i in F, sourceIGood (n := n) (v i).val)
    (hlim : Tendsto v F (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology omega θ hbig) u)) :
    sourceIGood (n := n) u.val := by
  let := sourceSingularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
  exact (sourceIGood_isClosed omega θ hbig).mem_of_tendsto hlim hgood

end SGPT.PSH.VariableComplexAtlas
