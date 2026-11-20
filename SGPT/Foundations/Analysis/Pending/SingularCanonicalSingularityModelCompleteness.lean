import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelMetricSpace
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCauchyLimit
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

/-! # Complete actual model metric spaces at a fixed positive mass threshold

SGPT PDF0231--0232 model sequence completeness argument, with the true
native fixed-threshold carrier. Its inclusion transports Cauchy sequences
to the genuine target-free model limit producer and recovers their actual
native limits. The proved Mathlib sequential criterion yields genuine
uniform completeness. Only a fixed delta > 0 is asserted complete.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCompleteness

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularCanonicalSingularityModelMetricSpace SingularCanonicalSingularityModelCauchyLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual native model metric space is complete above a fixed positive
actual top-mass threshold; no completeness or limit certificate is supplied. -/
theorem completeSpace_modelMetricSpace (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {δ : ℝ} (hδ : 0 < δ) :
    letI := modelMetricSpace omega θ hbig δ
    letI : UniformSpace (MassBoundedModelPotential θ δ) :=
      (modelMetricSpace omega θ hbig δ).toUniformSpace
    letI : TopologicalSpace (MassBoundedModelPotential θ δ) :=
      (modelMetricSpace omega θ hbig δ).toUniformSpace.toTopologicalSpace
    CompleteSpace (MassBoundedModelPotential θ δ) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let := modelMetricSpace omega θ hbig δ
  let : UniformSpace (MassBoundedModelPotential θ δ) :=
    (modelMetricSpace omega θ hbig δ).toUniformSpace
  let : TopologicalSpace (MassBoundedModelPotential θ δ) :=
    (modelMetricSpace omega θ hbig δ).toUniformSpace.toTopologicalSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro ui hcauchy
  have hisom := model_inclusion_isometry omega θ hbig δ
  have hc : CauchySeq (fun i => (ui i).val) := hisom.uniformContinuous.comp_cauchySeq hcauchy
  obtain ⟨U, hU, hδU, hlim⟩ := exists_model_limit_of_cauchySeq omega θ hbig
    (fun i => (ui i).val) (fun i => (ui i).property.1) hδ
    (fun i => (ui i).property.2) hc
  let V : MassBoundedModelPotential θ δ := ⟨U, hU, hδU⟩
  exact ⟨V, hisom.tendsto_nhds_iff.mpr hlim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCompleteness
