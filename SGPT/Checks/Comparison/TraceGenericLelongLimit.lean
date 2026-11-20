import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.NativeDivisorialLelongLimit
import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

/-! Original whole-target generic Lelong continuity at the ACTUAL image set.
Blueprint: `trace-na-decreasing-limit.tex`. No target algebraization/modification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open ThetaPshL1Topology SingularCanonicalSingularityDistance DemaillyApproximantDivisorialLelong
open SourceTraceRepresentativeDefinition
open scoped Topology ENNReal

/-- Exact original squared-log normalization on the actual target image,
including noninjective maps, infinite values and empty targets. -/
theorem sourceGenericLelongNumber_eq_half_image {m : ℕ} {M V : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    (ι : V → M) (u : M → EReal) :
    sourceGenericLelongNumber (n := m+1) ι u =
      (2 : ℝ≥0∞)⁻¹ * divisorialLelongNumber m u (range ι) := by
  rw [divisorialLelongNumber, iInf_range, nativeGeneric_eq_two_mul_source (Nat.succ_ne_zero m)]
  exact (ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)).symm

/-- The ORIGINAL native dS topology controls its SAME original generic
reader along ANY actual target map, in EVERY ambient dimension. -/
theorem tendsto_sourceGenericLelongNumber_of_native
    {n : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (ι : V → M) :
    Tendsto (fun i => sourceGenericLelongNumber (n := n) ι (w i).val) F
      (𝓝 (sourceGenericLelongNumber (n := n) ι u.val)) := by
  cases n with
  | zero =>
    have hread (a : M → EReal) : sourceGenericLelongNumber (n := 0) ι a =
        sourceGenericLelongNumber (n := 0) ι (fun _ => 0) := by
      simp only [sourceGenericLelongNumber, SquaredLogLelongSourceNormalization.squaredLogLelongNumber, ite_true]
    simpa only [hread] using (tendsto_const_nhds : Tendsto
      (fun _ : I => sourceGenericLelongNumber (n := 0) ι (fun _ => 0)) F
      (𝓝 (sourceGenericLelongNumber (n := 0) ι (fun _ => 0))))
  | succ m =>
    have hnative := NativeDivisorialLelongLimit.tendsto_divisorialLelongNumber_of_native
      omega θ hbig F w u hlim (range ι)
    have hcont : Continuous (fun a : ℝ≥0∞ => (2 : ℝ≥0∞)⁻¹ * a) :=
      ENNReal.continuous_const_mul (by norm_num)
    simpa only [Function.comp_def, ← sourceGenericLelongNumber_eq_half_image] using
      (hcont.tendsto (divisorialLelongNumber m u.val (range ι))).comp hnative

/-- The same continuity in the EXISTING original source singularity
carrier/topology, with the actual native carrier equivalence internal. -/
theorem tendsto_sourceGenericLelongNumber_of_sourceSingularityTopology
    {n : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (hlim : Tendsto w F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u))
    (ι : V → M) :
    Tendsto (fun i => sourceGenericLelongNumber (n := n) ι (w i).val) F
      (𝓝 (sourceGenericLelongNumber (n := n) ι u.val)) := by
  let := sourceSingularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
    omega (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (singularityPseudoMetricSpace omega (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (singularityPseudoMetricSpace omega (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) := Topology.IsInducing.induced _
  exact tendsto_sourceGenericLelongNumber_of_native omega (atlasClosedFormToNative θ) hbig F
    (fun i => sourceThetaPotentialL1EquivNative θ (w i))
    (sourceThetaPotentialL1EquivNative θ u) (hmap.tendsto_nhds_iff.mp hlim) ι

end SGPT.NAPotential.TraceComparison
