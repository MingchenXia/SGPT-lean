import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeIGood
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices

set_option autoImplicit false

/-! # Actual normalized trace on its natural positive pullback-mass domain -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.POrder TraceRepresentativeConstruction DiagonalMass SingularGlobalPOrder
  IGoodPositiveBackgroundIndependence

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Exactly the natural domain in source Definition 8.1.2: a full trace
reader exists in the positive-mass literal pullback class. -/
def HasPositiveTraceRepresentativeAlong
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) : Prop :=
  ∃ τ : V → EReal, IsTraceRepresentativeAlong omega omegaV hι u τ ∧
    ∃ hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ,
      HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ

/-- The actual normalized potential is defined only with an actual proof
of existence in its natural positive representative domain. -/
def normalizedTraceAlong
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u) : V → EReal :=
  singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val (Classical.choose hdefined)

private theorem relativeIGood_of_positive_reader
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ)
    (η : ClosedRealOneOneForm k V) (hτ : IsThetaPshPotential η.val τ)
    (hpos : HasPositivePotentialMass η τ hτ) : IGoodWith η τ hτ := by
  obtain ⟨σ, hσ, hgood⟩ :=
    TraceRepresentativeIGood.iGood_of_isTraceRepresentativeAlong omegaV hι htrace
  exact (iGoodWith_iff_positive_common_potential omegaV σ η hσ hτ
    hgood.positiveMass hpos).mp hgood

/-- Every natural positive reader, with arbitrary other actual auxiliaries,
gives both literal envelopes of the defined normalized potential. -/
theorem normalizedTraceAlong_eq_envelopes [CompactSpace M]
    {omega₀ omega₁ : KahlerBackground n M}
    (omegaV₀ omegaV₁ : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u)
    {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega₁ omegaV₁ hι u τ)
    (hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ)
    (hpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ) :
    normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined =
        singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val τ ∧
      normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined =
        iSingularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val τ := by
  obtain ⟨hchosen, hσ, hσpos⟩ := Classical.choose_spec hdefined
  have heq := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaV₀ omegaV₁ hι hchosen htrace
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith omegaV₀
    (ClosedRealOneOneForm.pullback hι θ) hσ hτ hσpos hpos).mp heq
  have hP := pEquivalentWith_iff_envelope_eq.mp hfixed
  have hgood := relativeIGood_of_positive_reader omegaV₁ hι htrace
    (ClosedRealOneOneForm.pullback hι θ) hτ hpos
  exact ⟨hP, hP.trans hgood.envelope_eq⟩

/-- The actual defined normalized potential is literally independent of
all auxiliary forms, full approximation witnesses and positive reader choices. -/
theorem normalizedTraceAlong_eq_of_choices [CompactSpace M]
    (omega₀ omega₁ : KahlerBackground n M)
    (omegaV₀ omegaV₁ : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined₀ : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u)
    (hdefined₁ : HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι θ u) :
    normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀ =
      normalizedTraceAlong omega₁ omegaV₁ hι θ u hdefined₁ := by
  obtain ⟨hchosen, hσ, hσpos⟩ := Classical.choose_spec hdefined₁
  exact (normalizedTraceAlong_eq_envelopes omegaV₀ omegaV₁ hι θ u
    hdefined₀ hchosen hσ hσpos).1

end

end SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace
