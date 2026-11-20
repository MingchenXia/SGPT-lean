import SGPT.Okounkov.SourceTraceChoices
import SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending SourceTraceRepresentativeDefinition
open SingularGlobalPOrder TraceRepresentativeConstruction

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Original ambient ideal order gives actual global order of genuine source
traces, through the existing whole native comparison producer. -/
theorem sourcePOrder_of_iOrder_of_sourceTraceRepresentatives (hn : n ≠ 0)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : V → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι v τv)
    (hI : IOrderOnManifold (n := n) u v) : SourcePOrder (n := k) τu τv := by
  exact TraceIdealOrderMonotonicity.sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
    omegaV₀ omegaV₁ hι
    ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaV₀ hι u τu).mp hTu)
    ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaV₁ hι v τv).mp hTv)
    hI

/-- Distinct ideal-equivalent original inputs give actual ideal-equivalent
source traces, with arbitrary genuine auxiliary backgrounds. -/
theorem iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives (hn : n ≠ 0)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : V → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι v τv)
    (hI : IEquivalentOnManifold (n := n) u v) :
    IEquivalentOnManifold (n := k) τu τv := by
  exact GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    ⟨sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hn omegaV₀ omegaV₁ hι hTu hTv hI.1,
      sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hn omegaV₁ omegaV₀ hι hTv hTu hI.2⟩

/-- Actual ambient ideal equivalence is transported all the way to the next
true smooth-divisor source coefficient, without a coefficient certificate. -/
theorem sourceGeneric_next_divisor_eq_of_iEquivalent_sourceTraceRepresentatives
    (hn : n ≠ 0)
    {q : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel (q + 1)) N] [IsComplexManifold (q + 1) N]
    [MeasurableSpace N] [BorelSpace N] [CompactSpace N] [ConnectedSpace N]
    {omega₀ omega₁ : KahlerBackground n M}
    (omegaN₀ omegaN₁ : KahlerBackground (q + 1) N)
    {ι : N → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : N → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaN₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaN₁ hι v τv)
    (hI : IEquivalentOnManifold (n := n) u v)
    {Z : Set N} (hZ : IsClosedConnectedSubmanifold (q + 1) Z q) :
    sourceGenericLelongNumber (n := q + 1) (Subtype.val : Z → N) τu =
      sourceGenericLelongNumber (n := q + 1) (Subtype.val : Z → N) τv := by
  have hTuOriginal := hTu
  have hTvOriginal := hTv
  obtain ⟨_hu0, _θu, _εu, _useq, _hqu, _βu, _hβu, hτu, _htermsu, _hlimu⟩ := hTu
  obtain ⟨_hv0, _θv, _εv, _vseq, _hqv, _βv, _hβv, hτv, _htermsv, _hlimv⟩ := hTv
  exact sourceGeneric_subtype_eq_of_iEquivalent hZ hτu.quasiPshPotential hτv.quasiPshPotential
    (iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives hn omegaN₀ omegaN₁ hι
      hTuOriginal hTvOriginal hI)

end SGPT.Okounkov
