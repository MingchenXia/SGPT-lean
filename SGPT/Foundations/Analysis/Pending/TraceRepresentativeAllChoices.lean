import SGPT.Foundations.Analysis.Pending.TraceRepresentativeApproximationIndependence
import SGPT.Foundations.Analysis.Pending.TraceTargetAuxiliaryIndependence

set_option autoImplicit false

/-! # Actual trace comparison with every ambient and target auxiliary choice -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Every ambient and target auxiliary is arbitrary; actual transport
preserves the original literal trace candidates before comparing their classes. -/
theorem sourcePEquivalent_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : V → EReal}
    (hT₀ : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u τ₀)
    (hT₁ : IsTraceRepresentativeAlong omega₁ omegaV₁ hι u τ₁) :
    SourcePEquivalent (n := k) τ₀ τ₁ := by
  have hT₁₀ :=
    (TraceTargetAuxiliaryIndependence.isTraceRepresentativeAlong_iff_target_auxiliary_choices
      omega₁ omegaV₁ omegaV₀ hι u τ₁).mp hT₁
  exact TraceRepresentativeGlobalPEquivalenceAuxiliaries.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaV₀ hι hT₀ hT₁₀

/-- The natural genuine candidate and admissible target suffice for any
new full QEA and either auxiliary choice; every new stage and limit is produced. -/
theorem native_limit_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u τ)
    {θ : ClosedRealOneOneForm n M} {ε : ℕ → ℝ} {vSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega₁ θ u ε vSeq)
    (β : KahlerBackground k V)
    (hadm : IsAdmissibleTraceBackground hι omega₁ θ ε β.form)
    (hτ : IsThetaPshPotential β.form.val τ) :
    ∃ hv : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)),
      Tendsto (fun j => (⟨fun y => vSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV₁ β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩) ∧
      IsTraceRepresentativeAlong omega₁ omegaV₁ hι u τ := by
  have htrace₁ :=
    (TraceTargetAuxiliaryIndependence.isTraceRepresentativeAlong_iff_target_auxiliary_choices
      omega₀ omegaV₀ omegaV₁ hι u τ).mp htrace
  exact TraceRepresentativeApproximationIndependence.native_limit_of_isTraceRepresentativeAlong
    omegaV₁ hι htrace₁ happ β hadm hτ

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
