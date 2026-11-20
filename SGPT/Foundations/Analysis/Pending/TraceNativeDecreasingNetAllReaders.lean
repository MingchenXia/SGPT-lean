import SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingSequenceAllReaders
import SGPT.Foundations.Analysis.Pending.DirectedFrequentMetricSequence

set_option autoImplicit false

/-! # Actual native trace continuity for every directed decreasing net -/

open Set Filter Metric
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingNetAllReaders

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  TraceRepresentativeConstruction ThetaPshL1Topology SingularCanonicalSingularityDistance

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [CompactSpace V] [ConnectedSpace V]

/-- Actual frequent-bad selection reduces every directed antitone net
to the produced every-reader sequence theorem, with all original auxiliaries. -/
theorem tendsto_native_trace_readers_of_antitone_net
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun i => (ui i).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (η : ClosedRealOneOneForm k V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τi : I → ThetaPshL1 η.val) (τ : ThetaPshL1 η.val)
    {omegai : I → KahlerBackground n M} {omegaVi : I → KahlerBackground k V}
    {omega₀ : KahlerBackground n M} {omegaV₀ : KahlerBackground k V}
    (hTi : ∀ i, IsTraceRepresentativeAlong (omegai i) (omegaVi i) hι (ui i).val (τi i).val)
    (hT : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u.val τ.val) :
    Tendsto τi atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace τ) := by
  classical
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let := singularityPseudoMetricSpace omegaV η hη
  let : TopologicalSpace (ThetaPshL1 η.val) :=
    (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace
  by_contra hnot
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨a, ha, hbad⟩ := hnot
  have hfreq : ∃ᶠ i in (atTop : Filter I), a ≤ dist (τi i) τ := by
    simpa only [not_lt] using hbad
  obtain ⟨j, hjmono, _hjstart, hjbad, hjlim⟩ :=
    DirectedFrequentMetricSequence.exists_monotone_sequence_in_frequent_tendsto
      hlim (Classical.choice (inferInstance : Nonempty I))
      (S := {i | a ≤ dist (τi i) τ}) hfreq
  have hjanti : ∀ x, Antitone fun l => (ui (j l)).val x := by
    intro x l m hlm
    exact hanti x (hjmono hlm)
  have hτlim := TraceNativeDecreasingSequenceAllReaders.tendsto_native_trace_readers_of_antitone
    omega omegaV θ hbig (fun l => ui (j l)) u hjanti hjlim hι η hη
    (fun l => τi (j l)) τ (fun l => hTi (j l)) hT
  have hnear : ∀ᶠ l in (atTop : Filter ℕ), dist (τi (j l)) τ < a :=
    (Metric.tendsto_nhds.mp hτlim) a ha
  obtain ⟨l, hl⟩ := hnear.exists
  exact (not_lt_of_ge (hjbad l)) hl

end
end SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingNetAllReaders
