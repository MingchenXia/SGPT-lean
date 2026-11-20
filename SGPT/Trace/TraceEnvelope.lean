import SGPT.Trace.SmoothTarget
import SGPT.Okounkov.SourceTraceChoices
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
import SGPT.Foundations.Analysis.Pending.PositiveTraceDomainAuxiliaryIndependence
import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass

/-!
# The normalized trace `Tr^θ_Y(φ)`

Source `def:traceop2` (`chapter_trace.tex`): we write `Tr_Y(φ)` for any trace operator
of `φ` along `Y`; given a closed smooth real `(1,1)`-form `θ` on `X`, when `Tr_Y(φ)` can
be chosen in `PSH(Ỹ, θ|_Ỹ)_{>0}`,
`Tr^θ_Y(φ) := P_{θ|_Ỹ}[Tr_Y(φ)] = P_{θ|_Ỹ}[Tr_Y(φ)]_𝓘`.
After the definition the book observes that `Tr^{θ+ω}_Y(φ)` is always defined when
`φ ∈ PSH(X,θ)` and `ω` is Kähler, and that `Tr^θ_Y(φ)` is always defined when `θ_φ` is
a Kähler current.

As in `SGPT.Trace.SmoothTarget`, the target is a compact connected complex manifold
`V` with a holomorphic map `ι : V → X`, and `θ|_Ỹ` is the pullback `ι^*θ`. The
definitions below use the source trace predicate `IsSourceTraceRepresentativeAlong`
(source normalization of the generic Lelong number, so that the zero-dimensional
ambient case is the book's one); in positive ambient dimension they agree with the
native `PositiveNormalizedTrace.HasPositiveTraceRepresentativeAlong` and
`PositiveNormalizedTrace.normalizedTraceAlong`
(`hasPositiveSourceTraceAlong_iff_native`, `sourceTraceEnvelope_eq_native`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.FirstPass.POrder
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition TraceRepresentativeConstruction
  SingularGlobalPOrder DiagonalMass PositiveNormalizedTrace
  IGoodPositiveBackgroundIndependence

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Source `def:traceop2`, the domain of `Tr^θ_Y(φ)`: some trace operator of `u` along
`ι` lies in `PSH(V, ι^*θ)_{>0}`. -/
def HasPositiveSourceTraceAlong (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) : Prop :=
  ∃ τ : V → EReal, IsSourceTraceRepresentativeAlong omega omegaV hι u τ ∧
    ∃ hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ,
      HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ

/-- Source `def:traceop2`: `Tr^θ_Y(φ) := P_{θ|_Y}[Tr_Y(φ)]`, the ordinary singularity
envelope in the pulled-back background of a positive-mass trace operator. By
`sourceTraceEnvelope_eq_envelopes` it does not depend on the chosen trace operator,
and equals `P_{θ|_Y}[Tr_Y(φ)]_𝓘`. -/
def sourceTraceEnvelope (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveSourceTraceAlong omega omegaV hι θ u) : V → EReal :=
  singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val (Classical.choose hdefined)

/-- In positive ambient dimension the source domain is the native one. -/
theorem hasPositiveSourceTraceAlong_iff_native (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    HasPositiveSourceTraceAlong omega omegaV hι θ u ↔
      HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
  unfold HasPositiveSourceTraceAlong HasPositiveTraceRepresentativeAlong
  simp_rw [isSourceTraceRepresentativeAlong_iff_native hn]

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- In dimension `0` every potential has positive mass. -/
theorem hasPositivePotentialMass_of_dim_zero [MeasurableSpace V] [BorelSpace V]
    [CompactSpace V] (hk : k = 0) (η : ClosedRealOneOneForm k V) {τ : V → EReal}
    (hτ : IsThetaPshPotential η.val τ) : HasPositivePotentialMass η τ hτ := by
  subst hk
  have hcount := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
    (M := V) (fun _ => η) (fun _ => τ) (fun _ => hτ.1)).2.1
  have hmass : diagonalPotentialMass η τ hτ = (Nat.card V : ℝ≥0∞) := hcount
  have hfin := (ZeroDimensionalGlobalMixedMass.compact_zero_dim_finite_discrete (M := V)).2
  have hcard : 0 < Nat.card V := Nat.card_pos
  unfold HasPositivePotentialMass
  rw [hmass]
  exact_mod_cast hcard

/-- In ambient dimension `0` (so the target is a point) every trace operator lies in
`PSH(V, ι^*θ)_{>0}` for every `θ`. -/
theorem hasPositiveSourceTraceAlong_of_dim_zero (hk : k ≤ n) (hn : n = 0)
    {omega : KahlerBackground n M} {omegaV : KahlerBackground k V} {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ) :
    HasPositiveSourceTraceAlong omega omegaV hι θ u := by
  have hk0 : k = 0 := by omega
  subst hk0
  have hkeep := htrace
  obtain ⟨_hg, _θ, _ε, _U, _happ, β, _hadm, hτβ, _hterms, _hlim⟩ := hkeep
  have hfin : ∀ y, τ y ≠ ⊤ ∧ τ y ≠ ⊥ := fun y =>
    ⟨hτβ.1.quasiPlurisubharmonic.ne_top y,
      RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hτβ.2 y⟩
  have hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
      (fun y => (hfin y).1) (fun y => (hfin y).2)
  exact ⟨τ, htrace, hτ, hasPositivePotentialMass_of_dim_zero rfl _ hτ⟩

variable [CompactSpace M]

/-- Source `def:traceop2`, well-definedness: for EVERY trace operator `τ` of `u` along
`ι` (with arbitrary auxiliary choices) lying in `PSH(V, ι^*θ)_{>0}`,
`Tr^θ_Y(u) = P_{ι^*θ}[τ] = P_{ι^*θ}[τ]_𝓘`. -/
theorem sourceTraceEnvelope_eq_envelopes (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveSourceTraceAlong omega₀ omegaV₀ hι θ u) {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι u τ)
    (hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ)
    (hpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ) :
    sourceTraceEnvelope omega₀ omegaV₀ hι θ u hdefined =
        singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val τ ∧
      sourceTraceEnvelope omega₀ omegaV₀ hι θ u hdefined =
        iSingularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val τ := by
  obtain ⟨hchosen, hσ, hσpos⟩ := Classical.choose_spec hdefined
  have heq := SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives hk
    omegaV₀ omegaV₁ hι hchosen htrace
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith omegaV₀
    (ClosedRealOneOneForm.pullback hι θ) hσ hτ hσpos hpos).mp heq
  have hP := pEquivalentWith_iff_envelope_eq.mp hfixed
  obtain ⟨σ', hσ', hgood'⟩ := SGPT.Okounkov.iGood_of_sourceTraceRepresentative hk omegaV₁ hι htrace
  have hgood : IGoodWith (ClosedRealOneOneForm.pullback hι θ) τ hτ :=
    (iGoodWith_iff_positive_common_potential omegaV₁ σ' (ClosedRealOneOneForm.pullback hι θ)
      hσ' hτ hgood'.1 hpos).mp hgood'
  exact ⟨hP, hP.trans hgood.envelope_eq⟩

/-- Source `def:traceop2`: `Tr^θ_Y(u)` does not depend on the auxiliary forms, the
approximation, or the chosen positive trace operator. -/
theorem sourceTraceEnvelope_eq_of_choices (hk : k ≤ n)
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined₀ : HasPositiveSourceTraceAlong omega₀ omegaV₀ hι θ u)
    (hdefined₁ : HasPositiveSourceTraceAlong omega₁ omegaV₁ hι θ u) :
    sourceTraceEnvelope omega₀ omegaV₀ hι θ u hdefined₀ =
      sourceTraceEnvelope omega₁ omegaV₁ hι θ u hdefined₁ := by
  obtain ⟨hchosen, hσ, hσpos⟩ := Classical.choose_spec hdefined₁
  exact (sourceTraceEnvelope_eq_envelopes hk omegaV₀ omegaV₁ hι θ u
    hdefined₀ hchosen hσ hσpos).1

/-- In positive ambient dimension the source normalized trace is the native one. -/
theorem sourceTraceEnvelope_eq_native (hk : k ≤ n) (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveSourceTraceAlong omega omegaV hι θ u) :
    sourceTraceEnvelope omega omegaV hι θ u hdefined =
      normalizedTraceAlong omega omegaV hι θ u
        ((hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mp hdefined) := by
  obtain ⟨τ, hT, hτ, hpos⟩ :=
    (hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mp hdefined
  rw [(sourceTraceEnvelope_eq_envelopes hk omegaV omegaV hι θ u hdefined
    ((isSourceTraceRepresentativeAlong_iff_native hn _ _ hι u τ).mpr hT) hτ hpos).1]
  exact ((normalizedTraceAlong_eq_envelopes omegaV omegaV hι θ u _ hT hτ hpos).1).symm

/-- Source `def:traceop2`: whether `Tr^θ_Y(u)` is defined does not depend on the
auxiliary Kähler forms. -/
theorem hasPositiveSourceTraceAlong_iff_auxiliary_choices (hk : k ≤ n)
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    HasPositiveSourceTraceAlong omega₀ omegaV₀ hι θ u ↔
      HasPositiveSourceTraceAlong omega₁ omegaV₁ hι θ u := by
  by_cases hn : n = 0
  · have change (a b : KahlerBackground n M) (aV bV : KahlerBackground k V)
        (h : HasPositiveSourceTraceAlong a aV hι θ u) :
        HasPositiveSourceTraceAlong b bV hι θ u := by
      obtain ⟨τ, hT, -, -⟩ := h
      have hg := hT.1
      obtain ⟨_hg, θ', _ε, _U, happ, _⟩ := hT
      obtain ⟨τ', hT'⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk
        b bV happ.target.quasiPshPotential hι hg
      exact hasPositiveSourceTraceAlong_of_dim_zero hk hn θ hT'
    exact ⟨change omega₀ omega₁ omegaV₀ omegaV₁, change omega₁ omega₀ omegaV₁ omegaV₀⟩
  rw [hasPositiveSourceTraceAlong_iff_native hn, hasPositiveSourceTraceAlong_iff_native hn]
  exact PositiveTraceDomainAuxiliaryIndependence.hasPositiveTraceRepresentativeAlong_iff_auxiliary_choices
    omega₀ omega₁ omegaV₀ omegaV₁ hι θ u

/-- The observation after source `def:traceop2`: if `θ_u` is a Kähler current
(`θ - δω + dd^c u ≥ 0` for some `δ > 0` and a Kähler form `ω` whose pullback to the
target is Kähler) and `ν(u, Y) = 0`, then `Tr^θ_Y(u)` is defined. -/
theorem hasPositiveSourceTraceAlong_of_kahlerCurrent (hk : k ≤ n)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    HasPositiveSourceTraceAlong omega₀ omegaV hι θ u := by
  by_cases hn : n = 0
  · obtain ⟨τ, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk
      omega₀ omegaV hu.quasiPshPotential hι hgeneric
    exact hasPositiveSourceTraceAlong_of_dim_zero hk hn θ hT
  apply (hasPositiveSourceTraceAlong_iff_auxiliary_choices hk omega omega₀ omegaV omegaV hι θ u).mp
  apply (hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mpr
  exact PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin
    omega omegaV hι hpull hδ hu ((nativeGeneric_zero_iff_source hn ι u).mpr hgeneric)

/-- The observation after source `def:traceop2`: if `u ∈ PSH(X,θ)` with `ν(u, Y) = 0`,
then for every Kähler form `ω` on `X` (whose pullback to the target is Kähler)
`Tr^{θ+ω}_Y(u)` is defined. -/
theorem hasPositiveSourceTraceAlong_add_kahler (hk : k ≤ n)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    HasPositiveSourceTraceAlong omega₀ omegaV hι (θ + omega.form) u := by
  apply hasPositiveSourceTraceAlong_of_kahlerCurrent hk omega₀ omega omegaV hι hpull
    zero_lt_one _ hgeneric
  simpa only [one_smul, add_sub_cancel_right] using hu

end SGPT.Trace
