import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeIGood
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType
import SGPT.Foundations.Analysis.Pending.RooftopDimZero
import SGPT.Okounkov.FlagLelong

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending SourceTraceRepresentativeDefinition
open SingularGlobalPOrder TraceRepresentativeConstruction

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [CompactSpace M] in
private theorem sourceTrace_background
    {omega : KahlerBackground n M} {omegaV : KahlerBackground k V}
    {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ) :
    ∃ β : KahlerBackground k V, IsThetaPshPotential β.form.val τ := by
  obtain ⟨_hzero, _θ, _ε, _uSeq, _hqea, β, _hβ, hτ, _hterms, _hlim⟩ := htrace
  exact ⟨β, hτ⟩

private theorem sameSingularity_of_zero_dim_theta_potentials
    {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
    [IsComplexManifold 0 V] [ConnectedSpace V]
    {θ σ : SmoothRealForm 0 V 2} {u v : V → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v) :
    SameSingularityTypeOn u v univ := by
  let : DiscreteTopology V := discreteTopology_iff_isOpen_singleton.mpr
    (RooftopDimZero.isOpen_singleton_of_dim_zero rfl)
  let : Subsingleton V := subsingleton_of_preconnected_totallyDisconnected
  let x : V := Classical.arbitrary V
  have huco : ((u x).toReal : EReal) = u x := EReal.coe_toReal
    (hu.1.quasiPlurisubharmonic.ne_top x)
    (RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 x)
  have hvco : ((v x).toReal : EReal) = v x := EReal.coe_toReal
    (hv.1.quasiPlurisubharmonic.ne_top x)
    (RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hv.2 x)
  constructor
  · refine ⟨(u x).toReal - (v x).toReal, ?_⟩
    intro y _hy
    rw [Subsingleton.elim y x, ← huco, ← hvco, ← EReal.coe_add]
    exact_mod_cast (by linarith : (u x).toReal ≤
      (v x).toReal + ((u x).toReal - (v x).toReal))
  · refine ⟨(v x).toReal - (u x).toReal, ?_⟩
    intro y _hy
    rw [Subsingleton.elim y x, ← huco, ← hvco, ← EReal.coe_add]
    exact_mod_cast (by linarith : (v x).toReal ≤
      (u x).toReal + ((v x).toReal - (u x).toReal))

omit [CompactSpace M] in
/-- The literal source trace predicate yields I-goodness in every original
ambient dimension; zero ambient forces the genuine zero target. -/
theorem iGood_of_sourceTraceRepresentative (hk : k ≤ n)
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ) :
    IGood (n := k) τ := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨β, hτ⟩ := sourceTrace_background htrace
    obtain ⟨_c, _ideal, hA⟩ :=
      DemaillyApproximationAnalyticType.hasAnalyticSingularities_of_dim_zero hτ
    exact AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type
      omegaV hτ.quasiPshPotential hA.hasManifoldAnalyticSingularityType
  · exact TraceRepresentativeIGood.iGood_of_isTraceRepresentativeAlong omegaV hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega omegaV hι u τ).mp htrace)

/-- Main's all-choices producer compares the original source traces with
arbitrary ambient and target auxiliary backgrounds, including ambient zero. -/
theorem sourcePEquivalent_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : V → EReal}
    (htrace₀ : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι u τ₀)
    (htrace₁ : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι u τ₁) :
    SourcePEquivalent (n := k) τ₀ τ₁ := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨β₀, hτ₀⟩ := sourceTrace_background htrace₀
    obtain ⟨β₁, hτ₁⟩ := sourceTrace_background htrace₁
    have hsame := sameSingularity_of_zero_dim_theta_potentials hτ₀ hτ₁
    exact ⟨sourcePOrder_of_moreSingularOn omegaV₀ β₀.form β₁.form hτ₀ hτ₁ hsame.1,
      sourcePOrder_of_moreSingularOn omegaV₀ β₁.form β₀.form hτ₁ hτ₀ hsame.2⟩
  · exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      omegaV₀ omegaV₁ hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaV₀ hι u τ₀).mp htrace₀)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaV₁ hι u τ₁).mp htrace₁)

/-- Actual P-equivalent source traces have all their original multiplier
ideals equal; this is the precise recursive flag input. -/
theorem iEquivalent_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : V → EReal}
    (htrace₀ : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι u τ₀)
    (htrace₁ : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι u τ₁) :
    IEquivalentOnManifold (n := k) τ₀ τ₁ :=
  GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    (sourcePEquivalent_of_sourceTraceRepresentatives hk omegaV₀ omegaV₁ hι htrace₀ htrace₁)

/-- Different genuine source traces have exactly the same next actual
smooth-divisor coefficient. No generic coefficient equality is assumed. -/
theorem sourceGeneric_next_divisor_eq_of_sourceTraceRepresentatives
    {q : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel (q + 1)) N] [IsComplexManifold (q + 1) N]
    [MeasurableSpace N] [BorelSpace N] [CompactSpace N] [ConnectedSpace N]
    (hk : q + 1 ≤ n)
    {omega₀ omega₁ : KahlerBackground n M}
    (omegaN₀ omegaN₁ : KahlerBackground (q + 1) N)
    {ι : N → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : N → EReal}
    (htrace₀ : IsSourceTraceRepresentativeAlong omega₀ omegaN₀ hι u τ₀)
    (htrace₁ : IsSourceTraceRepresentativeAlong omega₁ omegaN₁ hι u τ₁)
    {Z : Set N} (hZ : IsClosedConnectedSubmanifold (q + 1) Z q) :
    sourceGenericLelongNumber (n := q + 1) (Subtype.val : Z → N) τ₀ =
      sourceGenericLelongNumber (n := q + 1) (Subtype.val : Z → N) τ₁ := by
  obtain ⟨_β₀, hτ₀⟩ := sourceTrace_background htrace₀
  obtain ⟨_β₁, hτ₁⟩ := sourceTrace_background htrace₁
  exact sourceGeneric_subtype_eq_of_iEquivalent hZ hτ₀.quasiPshPotential hτ₁.quasiPshPotential
    (iEquivalent_of_sourceTraceRepresentatives hk omegaN₀ omegaN₁ hι htrace₀ htrace₁)

end SGPT.Okounkov
