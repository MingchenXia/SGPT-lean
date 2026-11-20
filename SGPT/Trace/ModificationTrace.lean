import SGPT.Okounkov.SourceTraceModification
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

/-!
# Generic Lelong numbers and traces under bimeromorphic pullback

Source `lma:rescommpullback` (`chapter_trace.tex`): let `π : Z → X` be a proper
bimeromorphic morphism and `Π : W → Y` its restriction, bimeromorphic. The proof starts
with "by Zariski's main theorem, `ν(π^*φ, W) = 0`, so the right-hand side makes sense".

For smooth targets (compact connected manifolds `V` and `W` with holomorphic maps to `X`
and `Z`, and a surjective map `pTail : W → V` with `π ∘ ι_W = ι_V ∘ pTail`), this file
proves that the downstairs condition `ν(φ, Y) = 0` alone forces `ν(π^*φ, W) = 0`, so the
upstairs trace exists, and combines this with the existing commuting-modification theorem
of `SGPT.Okounkov.SourceTraceModification`.

The argument does not use Zariski's main theorem: if `(φ_j)` is a quasi-equisingular
approximation of `φ`, then `(φ_j ∘ π)` is one of `π^*φ`; some restriction `φ_j ∘ ι_V` is
finite at a point `v`, hence `φ_j ∘ π` is finite at `x = ι_W(w)` for `w` over `v`, so its
Lelong number at `x` vanishes, `1 ∈ 𝓘(2c φ_j ∘ π)_x` by Skoda, hence `1 ∈ 𝓘(c π^*φ)_x` by
quasi-equisingularity and `ν(π^*φ, x) ≤ 2n/c`; let `c → ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal NNReal ContDiff

universe u

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SingularGlobalPOrder
  AnalyticModificationLocalDiscrepancy

variable {n k : ℕ} {X Z V W : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  [MeasurableSpace Z] [BorelSpace Z]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  [TopologicalSpace W] [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]
  [MeasurableSpace W] [BorelSpace W] [CompactSpace W] [ConnectedSpace W]

omit [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W] [MeasurableSpace W]
  [BorelSpace W] [CompactSpace W] in
/-- Source `lma:rescommpullback`, first step, on smooth targets: if `τ` is a trace
operator of `u` along `ι_V` (in particular `ν(u, Y) = 0`), `π` is a modification and
`π ∘ ι_W = ι_V ∘ pTail` with `pTail` surjective, then `ν(π^*u, W) = 0`. -/
theorem sourceGenericLelongNumber_comp_modification_eq_zero
    {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {pTail : W → V} (hpTail : Function.Surjective pTail)
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground n Z)
    (omegaV : KahlerBackground k V)
    {ιV : V → X} {hιV : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιV}
    {ιW : W → Z} (hcomm : ∀ w, π (ιW w) = ιV (pTail w))
    {u : X → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omegaX omegaV hιV u τ) :
    sourceGenericLelongNumber (n := n) ιW (u ∘ π) = 0 := by
  by_cases hn : n = 0
  · subst n
    exact sourceGenericLelongNumber_zero_dimension rfl ιW (u ∘ π)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨_hg, θ, ε, U, hqea, β, _hadm, _hτ, hUβ, _hlim⟩ := htrace
  obtain ⟨κ, hqeaπ⟩ := SGPT.Okounkov.exists_quasiEquisingularApproximation_modification
    hπ omegaX omegaZ θ hqea
  apply (nativeGeneric_zero_iff_source hn ιW (u ∘ π)).mp
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  let F : ℝ := (Module.finrank ℝ (ComplexModel n) : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  let c : ℝ := F / δ + 1
  have hc : 0 < c := by positivity
  have hFc : F / c ≤ δ := by
    rw [div_le_iff₀ hc]
    have : F = δ * (F / δ) := by field_simp
    nlinarith
  -- a stage of the pulled-back approximation with `𝓘(2c (U_j ∘ π)) ⊆ 𝓘(c (u ∘ π))`
  obtain ⟨j, hincl⟩ :=
    (hqeaπ.2.2.2.2.2 c (2 * c) hc (by linarith)).exists
  -- a point of `W` where `U_j ∘ π ∘ ι_W` is finite
  obtain ⟨v, -, hv⟩ := (hUβ j).2 (Classical.arbitrary V) univ isOpen_univ (mem_univ _)
  obtain ⟨w, rfl⟩ := hpTail v
  have hfin : (U j ∘ π) (ιW w) ≠ ⊥ := by
    simpa only [Function.comp_apply, hcomm w] using hv
  have hpsh := (hqeaπ.term j).1
  have hν0 : lelongNumber (n := n) (U j ∘ π) (ιW w) = 0 := by
    by_contra hne
    exact hfin (eq_bot_of_lelongNumber_pos hnpos hpsh (pos_iff_ne_zero.mpr hne))
  have hmem₀ : (multiplierIdeal (n := n) (2 * c) (U j ∘ π)).mem (ιW w) (fun _ => (1 : ℂ)) :=
    SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hpsh (by linarith)
      (by rw [hν0]; exact ENNReal.ofReal_pos.mpr (div_pos two_pos (by linarith)))
  have hmem : (multiplierIdeal (n := n) c (u ∘ π)).mem (ιW w) (fun _ => (1 : ℂ)) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded hincl _ _ hmem₀
  have hbound := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal hnpos hmem
  calc (⨅ w', lelongNumber (n := n) (u ∘ π) (ιW w'))
      ≤ lelongNumber (n := n) (u ∘ π) (ιW w) := iInf_le _ w
    _ ≤ ENNReal.ofReal (F / c) := hbound
    _ ≤ 0 + (δ : ℝ≥0∞) := by
      rw [zero_add]
      exact (ENNReal.ofReal_le_ofReal hFc).trans_eq (ENNReal.ofReal_coe_nnreal)

/-- Source `lma:rescommpullback` on smooth targets, with the original downstairs hypothesis
only: for every trace operator `τ` of `u` along `ι_V`, the pullback `τ ∘ pTail` is a trace
operator of `π^*u = u ∘ π` along `ι_W` (for a suitable auxiliary Kähler form upstairs),
and every trace operator `ρ` of `u ∘ π` along `ι_W` (with arbitrary auxiliary choices)
satisfies `τ ∘ pTail ∼_P ρ`. -/
theorem sourceTrace_modification_of_commuting (hk : k ≤ n)
    {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {pTail : W → V} (hpTail : IsAnalyticModification (n := k) pTail)
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground n Z)
    (omegaV : KahlerBackground k V) (omegaW : KahlerBackground k W)
    {ιV : V → X} (hιV : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιV)
    {ιW : W → Z} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hcomm : ∀ w, π (ιW w) = ιV (pTail w))
    {u : X → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omegaX omegaV hιV u τ) :
    sourceGenericLelongNumber (n := n) ιW (u ∘ π) = 0 ∧
      (∃ κ : KahlerBackground n Z,
        IsSourceTraceRepresentativeAlong κ omegaW hιW (u ∘ π) (τ ∘ pTail)) ∧
      ∀ (omegaZ' : KahlerBackground n Z) (omegaW' : KahlerBackground k W) (ρ : W → EReal),
        IsSourceTraceRepresentativeAlong omegaZ' omegaW' hιW (u ∘ π) ρ →
          SourcePEquivalent (n := k) (τ ∘ pTail) ρ := by
  have hzero := sourceGenericLelongNumber_comp_modification_eq_zero hπ
    (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hpTail)
    omegaX omegaZ omegaV hcomm htrace
  refine ⟨hzero, SGPT.Okounkov.exists_sourceTraceRepresentative_modification_of_commuting
    hπ hpTail omegaX omegaZ omegaV omegaW hιV hιW hcomm htrace hzero, ?_⟩
  intro omegaZ' omegaW' ρ hρ
  exact SGPT.Okounkov.sourcePEquivalent_modification_of_sourceTraceRepresentatives hk hπ hpTail
    omegaX omegaZ' omegaV omegaW omegaW' hιV hιW hcomm htrace hρ

end SGPT.Trace
