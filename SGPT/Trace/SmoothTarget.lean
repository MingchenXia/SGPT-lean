import SGPT.Trace.PointTrace
import SGPT.PSH.QuasiEquisingular
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionAnyBigBackground
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeApproximationIndependence
import SGPT.Foundations.Analysis.Pending.OrdinaryRestrictionGlobalTraceOrder
import SGPT.Foundations.Analysis.Pending.AnalyticTraceOrdinaryAgreement
import SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingNetAllReaders
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAuxiliaryDomination
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination

/-!
# Basic properties of the trace operator on a smooth target

Source: `chapter_trace.tex`, Sections "The definition of the trace operator" and
"Properties of the trace operator". The book takes the trace along an irreducible
analytic subset `Y ⊆ X` with values on the normalization `Ỹ`. Here the target is a
compact connected complex manifold `V` with a holomorphic map `ι : V → X` (for
instance a connected closed submanifold `Y`, which is its own normalization), and
the trace is the predicate `IsSourceTraceRepresentativeAlong` (source `def:traceop`,
with the source normalization of the generic Lelong number).

Main results, all including the zero-dimensional ambient case:

* `SGPT.Trace.tendsto_restricted_singularityDistance_zero`: source
  `prop:traceindquasiequisingapp` (two arbitrary source quasi-equisingular
  approximations, with possibly different backgrounds, have asymptotically
  `d_S`-equal restrictions, for any big background on the target);
* `SGPT.Trace.isSourceTraceRepresentativeAlong_of_qea`: the trace condition holds
  for every quasi-equisingular approximation and every admissible target background
  (the independence statements after source `def:traceop`);
* `SGPT.Trace.sourcePOrder_restriction_trace`: source `prop:Trdominarest`;
* `SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic`: source
  `ex:resanalyt`;
* `SGPT.Trace.tendsto_trace_of_antitone_net`: source `prop:tracedeclimit`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition TraceRepresentativeConstruction
  SquaredLogLelongSourceNormalization SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

section DimZero

variable {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
  [IsComplexManifold 0 V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [ConnectedSpace V]

/-- On a connected zero-dimensional compact target the canonical singularity distance
of any two `η`-psh potentials vanishes. -/
theorem singularityDistance_eq_zero_of_dim_zero (omegaV : KahlerBackground 0 V)
    (η : ClosedRealOneOneForm 0 V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    {a b : V → EReal} (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b) :
    singularityDistance omegaV η hη a b = 0 := by
  have hfin {c : V → EReal} (hc : IsThetaPshPotential η.val c) : ∀ y, c y ≠ ⊤ ∧ c y ≠ ⊥ :=
    fun y => ⟨hc.1.quasiPlurisubharmonic.ne_top y,
      RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hc.2 y⟩
  exact (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    omegaV η hη ha hb).mpr (sourcePEquivalent_of_finite_of_dim_zero omegaV (hfin ha) (hfin hb))

/-- On a connected zero-dimensional compact target every sequence (or net) of
`η`-psh potentials converges to every `η`-psh potential in the `d_S`-topology. -/
theorem tendsto_singularity_of_dim_zero (omegaV : KahlerBackground 0 V)
    (η : ClosedRealOneOneForm 0 V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    {I : Type*} (l : Filter I) (a : I → ThetaPshL1 η.val) (b : ThetaPshL1 η.val) :
    Tendsto a l (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace b) := by
  let := singularityPseudoMetricSpace omegaV η hη
  rw [Metric.tendsto_nhds]
  intro r hr
  refine Eventually.of_forall fun i => ?_
  rw [dist_eq_singularityDistance_toReal,
    singularityDistance_eq_zero_of_dim_zero omegaV η hη (a i).property b.property,
    EReal.toReal_zero]
  exact hr

end DimZero

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Source `prop:traceindquasiequisingapp` on a smooth target: let `φ ∈ PSH(X,θ₀)`
and `φ ∈ PSH(X,θ₁)` (the same function `u`), with source generic Lelong number `0`
along `ι`, and let `U`, `W` be source quasi-equisingular approximations of `u` (with
respect to `θ₀`, resp. `θ₁`, with their own auxiliary Kähler forms and errors). For
every closed real `(1,1)`-form `η` on the target representing a big class and
containing all restrictions, `d_{S,η}(U_j ∘ ι, W_j ∘ ι) → 0`. -/
theorem tendsto_restricted_singularityDistance_zero (hk : k ≤ n)
    (omegaV : KahlerBackground k V) {θ₀ θ₁ : ClosedRealOneOneForm n M} {u : M → EReal}
    {U W : ℕ → M → EReal}
    (hU : SourceQuasiEquisingularApproximation θ₀ u U)
    (hW : SourceQuasiEquisingularApproximation θ₁ u W)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0)
    (η : ClosedRealOneOneForm k V) (hbig : IsBigClass (RealBottChern.ofRepresentative η))
    (hUη : ∀ j, IsThetaPshPotential η.val (fun y => U j (ι y)))
    (hWη : ∀ j, IsThetaPshPotential η.val (fun y => W j (ι y))) :
    Tendsto (fun j => singularityDistance omegaV η hbig
      (fun y => U j (ι y)) (fun y => W j (ι y))) atTop (𝓝 0) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    refine tendsto_const_nhds.congr fun j => ?_
    exact (singularityDistance_eq_zero_of_dim_zero omegaV η hbig (hUη j) (hWη j)).symm
  obtain ⟨ω₀, ε, hU'⟩ := native_of_sourceQuasiEquisingularApproximation hU
  obtain ⟨ω₁, δ, hW'⟩ := native_of_sourceQuasiEquisingularApproximation hW
  obtain ⟨κ, h₀, h₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background ω₀ ω₁
  have hUκ := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hU' h₀
  have hWκ := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hW' h₁
  obtain ⟨β, hUβ, hWβ⟩ :=
    QuasiEquisingularBackgroundDomination.exists_common_kahler_background hUκ hWκ
  exact ((QuasiEquisingularRestrictionAnyBigBackground.restricted_distance_tendsto_zero_in_any_big_background
    omegaV hUβ hWβ hι ((nativeGeneric_zero_iff_source hn ι u).mpr hgeneric) η hbig hUη hWη).2)

/-- The independence statements after source `def:traceop`: if `τ` is a trace
operator of `u` along `ι` (witnessed by one quasi-equisingular approximation), then
for EVERY quasi-equisingular approximation `(vSeq)` of `u` (with any auxiliary Kähler
form `omega₁`, background `θ` and errors `ε`) and every admissible Kähler background
`β` on the target with `τ ∈ PSH(V, β)`, the restrictions `vSeq j ∘ ι` are `β`-psh and
converge to `τ` in `d_{S,β}`. -/
theorem isSourceTraceRepresentativeAlong_of_qea (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega₀ omegaV hι u τ)
    {θ : ClosedRealOneOneForm n M} {ε : ℕ → ℝ} {vSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega₁ θ u ε vSeq)
    (β : KahlerBackground k V) (hadm : IsAdmissibleTraceBackground hι omega₁ θ ε β.form)
    (hτ : IsThetaPshPotential β.form.val τ) :
    ∃ hv : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)),
      Tendsto (fun j => (⟨fun y => vSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩) ∧
      IsSourceTraceRepresentativeAlong omega₁ omegaV hι u τ := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    have hg := htrace.1
    have hvβ (j : ℕ) : IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)) := by
      have hfin : ∀ y, vSeq j (ι y) ≠ ⊤ ∧ vSeq j (ι y) ≠ ⊥ := fun y =>
        ⟨(happ.term j).1.quasiPlurisubharmonic.ne_top (ι y),
          RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl (happ.term j).2 (ι y)⟩
      exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
        (LocalPotentials.closedRealOneOne_hasLocalPotentials β.form)
        (fun y => (hfin y).1) (fun y => (hfin y).2)
    have hlim := tendsto_singularity_of_dim_zero omegaV β.form (isBigClass_kahler β) atTop
      (fun j => (⟨fun y => vSeq j (ι y), hvβ j⟩ : ThetaPshL1 β.form.val)) ⟨τ, hτ⟩
    exact ⟨hvβ, hlim, hg, θ, ε, vSeq, happ, β, hadm, hτ, hvβ, hlim⟩
  have hnat := (isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaV hι u τ).mp htrace
  obtain ⟨hv, hlim, hT⟩ :=
    TraceRepresentativeApproximationIndependence.native_limit_of_isTraceRepresentativeAlong
      omegaV hι hnat happ β hadm hτ
  exact ⟨hv, hlim, (isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaV hι u τ).mpr hT⟩

omit [CompactSpace M] in
/-- Source `prop:Trdominarest` on a smooth target: if `τ` is a trace operator of `u`
along `ι` and the ordinary restriction `u ∘ ι` is not identically `-∞`, then
`u ∘ ι ⪯_P τ`. -/
theorem sourcePOrder_restriction_trace (hk : k ≤ n)
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ)
    (hne : ∃ y : V, u (ι y) ≠ ⊥) :
    SourcePOrder (n := k) (fun y => u (ι y)) τ := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨_hg, θ, _ε, _U, happ, β, _hadm, hτ, _hterms, _hlim⟩ := htrace
    have hu := happ.target
    have hfinR : ∀ y, u (ι y) ≠ ⊤ ∧ u (ι y) ≠ ⊥ := fun y =>
      ⟨hu.1.quasiPlurisubharmonic.ne_top (ι y),
        RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 (ι y)⟩
    have hfinτ : ∀ y, τ y ≠ ⊤ ∧ τ y ≠ ⊥ := fun y =>
      ⟨hτ.1.quasiPlurisubharmonic.ne_top y,
        RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hτ.2 y⟩
    exact (sourcePEquivalent_of_finite_of_dim_zero omegaV hfinR hfinτ).1
  exact OrdinaryRestrictionGlobalTraceOrder.sourcePOrder_ordinaryRestriction_of_isTraceRepresentativeAlong
    omegaV hι ((isSourceTraceRepresentativeAlong_iff_native hn omega omegaV hι u τ).mp htrace) hne

/-- Source `ex:resanalyt` on a smooth target: if `u` has analytic singularities and
`τ` is a trace operator of `u` along `ι`, then `τ ∼_P u ∘ ι`. -/
theorem sourcePEquivalent_trace_restriction_of_analytic (hk : k ≤ n)
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ)
    (hA : HasManifoldAnalyticSingularityType (n := n) u) :
    SourcePEquivalent (n := k) τ (fun y => u (ι y)) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨_hg, θ, _ε, _U, happ, β, _hadm, hτ, _hterms, _hlim⟩ := htrace
    have hu := happ.target
    have hfinR : ∀ y, u (ι y) ≠ ⊤ ∧ u (ι y) ≠ ⊥ := fun y =>
      ⟨hu.1.quasiPlurisubharmonic.ne_top (ι y),
        RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 (ι y)⟩
    have hfinτ : ∀ y, τ y ≠ ⊤ ∧ τ y ≠ ⊥ := fun y =>
      ⟨hτ.1.quasiPlurisubharmonic.ne_top y,
        RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hτ.2 y⟩
    exact sourcePEquivalent_of_finite_of_dim_zero omegaV hfinτ hfinR
  exact AnalyticTraceOrdinaryAgreement.sourcePEquivalent_ordinaryRestriction_of_analytic_isTraceRepresentativeAlong
    omegaV hι ((isSourceTraceRepresentativeAlong_iff_native hn omega omegaV hι u τ).mp htrace) hA

/-- Source `prop:tracedeclimit` on a smooth target: let `(u_i)_{i ∈ I}` be a decreasing
net in `PSH(X,θ)` (`θ` big) converging in `d_S` to `u`, and let `τ_i`, `τ` be trace
operators of `u_i`, `u` along `ι` (all of them in `PSH(V,η)` for a big `η` on the
target). Then `τ_i → τ` in `d_{S,η}`. -/
theorem tendsto_trace_of_antitone_net [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]
    (hk : k ≤ n) (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun i => (ui i).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (η : ClosedRealOneOneForm k V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τi : I → ThetaPshL1 η.val) (τ : ThetaPshL1 η.val)
    {omegai : I → KahlerBackground n M} {omegaVi : I → KahlerBackground k V}
    {omega₀ : KahlerBackground n M} {omegaV₀ : KahlerBackground k V}
    (hTi : ∀ i, IsSourceTraceRepresentativeAlong (omegai i) (omegaVi i) hι (ui i).val (τi i).val)
    (hT : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ hι u.val τ.val) :
    Tendsto τi atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace τ) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact tendsto_singularity_of_dim_zero omegaV η hη atTop τi τ
  exact TraceNativeDecreasingNetAllReaders.tendsto_native_trace_readers_of_antitone_net
    omega omegaV θ hbig ui u hanti hlim hι η hη τi τ
    (fun i => (isSourceTraceRepresentativeAlong_iff_native hn _ _ hι _ _).mp (hTi i))
    ((isSourceTraceRepresentativeAlong_iff_native hn _ _ hι _ _).mp hT)

end SGPT.Trace
