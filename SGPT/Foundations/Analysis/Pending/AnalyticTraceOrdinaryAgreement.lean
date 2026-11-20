import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin

set_option autoImplicit false

/-! # Every analytic actual trace reader agrees globally with ordinary restriction -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticTraceOrdinaryAgreement

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Full constant QEA, actual generic-infimum restriction and admissibility
internally exhibit ordinary restriction as a trace before global comparison. -/
theorem sourcePEquivalent_ordinaryRestriction_of_analytic_isTraceRepresentativeAlong
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ)
    (hA : HasManifoldAnalyticSingularityType (n := n) u) :
    SourcePEquivalent (n := k) τ (fun y => u (ι y)) := by
  have htraceOriginal := htrace
  obtain ⟨hgeneric, θ, _, _, happ, _, _, _, _, _⟩ := htrace
  have hconst := isQuasiEquisingularApproximation_const omega θ happ.target hA
  have hR : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => u (ι y)) := by
    simpa only [zero_smul, add_zero] using
      AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
        hconst hι hgeneric 0
  obtain ⟨C, hC, hadmC, _⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega omegaV θ hconst.error_antitone
  let β : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hadmβ : IsAdmissibleTraceBackground hι omega θ (fun _ => 0) β.form := hadmC
  have hdom : (β.form - ClosedRealOneOneForm.pullback hι θ).val.IsSemipositive := by
    simpa only [FormDominates, zero_smul, add_zero] using hadmβ.dominates 0
  have hRβ : IsThetaPshPotential β.form.val (fun y => u (ι y)) := by
    have hform : ClosedRealOneOneForm.pullback hι θ +
        (β.form - ClosedRealOneOneForm.pullback hι θ) = β.form := by module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hR hdom
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  let R : ThetaPshL1 β.form.val := ⟨fun y => u (ι y), hRβ⟩
  have hlimR : Tendsto (fun _ : ℕ => R) atTop (𝓝 R) := tendsto_const_nhds
  have htraceR : IsTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y)) :=
    ⟨hgeneric, θ, (fun _ => 0), (fun _ => u), hconst, β, hadmβ,
      hRβ, (fun _ => hRβ), hlimR⟩
  exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaV omegaV hι htraceOriginal htraceR

end

end SGPT.Foundations.Analysis.Pending.AnalyticTraceOrdinaryAgreement
