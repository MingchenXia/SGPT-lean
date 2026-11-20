import SGPT.Trace.TYReadings

/-!
# The trace operator on the normalization `Ỹ`

Source: `chapter_trace.tex`, `prop:traceindquasiequisingapp`, `def:traceop`, `prop:traceunique`,
`def:traceop2`, `prop:Trdominarest`, `ex:resanalyt`, `ex:tracedefinedposmass`, `rmk:movingSes`,
`prop:tracelinear`, `prop:tracedeclimit`; Appendix B, `cor:PSH`, `sec:unib_ext`.

The book takes the trace of `φ ∈ QPSH(X)` along an irreducible analytic `Y ⊆ X` with values in
`QPSH(Ỹ)`, `Ỹ` the normalization of `Y`. For `T : TildeY Y` (`Ỹ`, `TYDescentInterface`):

* `IsTrace φ ψ` (**`def:traceop` on `Ỹ`**): `ψ ∈ QPSH(Ỹ)` and on every resolution `ν : V → Ỹ`
  the reading `ψ ∘ ν` is the `d_S`-limit of a quasi-equisingular approximation of `φ` restricted to
  `V` (`d_S` on `Ỹ` is read on resolutions, `TYReadings`).
* `HasPositiveTrace θ φ` and `traceEnvelope θ φ` (**`def:traceop2` on `Ỹ`**): `Tr_Y(φ)` can be
  chosen in `PSH(Ỹ, θ|_Ỹ)_{>0}`, and `Tr^θ_Y(φ) := P_{θ|_Ỹ}[Tr_Y(φ)]` (the `P`-envelope on `Ỹ`).
* `traceMass θ φ` (**`ex:tracedefinedposmass`**): `∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y(φ))^{dim Y}`, `0` if
  undefined.
* `movingSeshadri` (**`rmk:movingSes`**), with the trace volumes on the normalizations `Ṽ`.

The theorems take `cor:PSH` for the resolutions of `Ỹ` (`TildeY.CorPSH`) as an explicit hypothesis
where it is used (descent of a trace read on a resolution to `Ỹ`, and the identification of the
`P`-envelope on `Ỹ` with the one on a resolution); the other statements are read on every
resolution of `Ỹ` and follow from `Trace2Resolution`/`P5Wire`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Trace.Trace2Resolution SGPT.Unibranch

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  {Y : ClosedIrreducibleAnalyticSubvariety n X}

namespace TildeY

variable {T : TildeY Y}

/-! ### `def:traceop` on `Ỹ` -/

/-- **Source `def:traceop` on `Ỹ`**: `ψ ∈ QPSH(Ỹ)` is a trace operator of `φ` along `Y`: on every
resolution `ν : V → Ỹ` there are a quasi-equisingular approximation `(φ_j)` of `φ` (with
`ν(φ, Y) = 0`) and admissible Kähler backgrounds such that `φ_j|_Ỹ ∘ ν = φ_j ∘ ι → ψ ∘ ν` in
`d_S` (the footnote's condition `φ_j|_Ỹ → ψ` in `d_{S, ω̃}`, read on the resolution). -/
def IsTrace (T : TildeY Y) (φ : X → EReal) (ψ : T.space.obj.left → EReal) : Prop :=
  T.IsQPSH ψ ∧ ∀ N : T.Resolution, IsTraceOn N φ (ψ ∘ N.ν)

/-- **`def:traceop` on `Ỹ`: independence of the resolution.** For `ψ ∈ PSH(Ỹ, θ|_Ỹ)`, `ψ` is a
trace operator of `φ` as soon as its reading on ONE resolution of `Ỹ` is (forward half of
`cor:PSH`). -/
theorem isTrace_iff_exists (hfwd : ∀ N : T.Resolution, T.CorPSHForward N)
    {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} {ψ : T.space.obj.left → EReal} (hψ : T.space.IsThetaPSH (T.restrict θ) ψ) :
    T.IsTrace φ ψ ↔ ∃ N : T.Resolution, IsTraceOn N φ (ψ ∘ N.ν) := by
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨N⟩ := T.nonempty_resolution
    exact ⟨N, h N⟩
  · rintro ⟨N₀, h₀⟩
    exact ⟨isQPSH_of_isThetaPSH hψ, fun N => transfer N₀ N h₀ (hfwd N θ ψ hψ)⟩

/-- **`def:traceop` on `Ỹ`: existence** ("Indeed ... it converges by `cor:completenessdS`"). Let
`φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` and `ω` a Kähler form on `X`. Then `φ` has a trace operator
along `Y` in `PSH(Ỹ, (θ + ω)|_Ỹ)` (`cor:PSH`). -/
theorem exists_isTrace (hcor : ∀ N : T.Resolution, T.CorPSH N) {θ : ClosedRealOneOneForm n X}
    (om : KahlerBackground n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    ∃ ψ : T.space.obj.left → EReal,
      T.space.IsThetaPSH (T.restrict (θ + om.form)) ψ ∧ T.IsTrace φ ψ := by
  obtain ⟨N₀⟩ := T.nonempty_resolution
  obtain ⟨τ, hτ, hτpsh, -⟩ :=
    SGPT.Trace.RIsoB.hasPositiveSourceTraceAlong_add_kahler N₀.R om om N₀.R.kahler hφ hν
  obtain ⟨ψ, hψ, hψτ⟩ := (hcor N₀).descend hτpsh
  refine ⟨ψ, hψ, (isTrace_iff_exists (fun N => (hcor N).forward) hψ).mpr ⟨N₀, om, N₀.R.kahler, ?_⟩⟩
  rw [hψτ]
  exact hτ

/-- **`def:traceop` on `Ỹ`: the generic condition** of the trace predicate is the book's
`ν(φ, Y) = 0`. -/
theorem IsTrace.sourceGenericLelong_eq_zero {φ : X → EReal} {ψ : T.space.obj.left → EReal}
    (h : T.IsTrace φ ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0 := by
  obtain ⟨N⟩ := T.nonempty_resolution
  obtain ⟨om, omV, ht⟩ := h.2 N
  exact sourceGenericLelong_eq_zero_of_trace N.R ht

/-- **`def:traceop` on `Ỹ`: independence of the choices** (footnote; `prop:traceindquasiequisingapp`
and `cor:dSconv_changetheta`): if `ψ` is a trace operator of `φ`, then on every resolution
`ν : V → Ỹ`, for EVERY quasi-equisingular approximation `(φ_j)` of `φ` and every admissible Kähler
background `β` on `V` containing `ψ ∘ ν`, `φ_j|_Ỹ ∘ ν → ψ ∘ ν` in `d_{S,β}`. -/
theorem IsTrace.tendsto_of_qea {φ : X → EReal} {ψ : T.space.obj.left → EReal}
    (h : T.IsTrace φ ψ) (N : T.Resolution) {om₁ : KahlerBackground n X}
    {θ : ClosedRealOneOneForm n X} {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : QuasiEquisingularApproximation.IsQuasiEquisingularApproximation om₁ θ φ ε φSeq)
    (β : KahlerBackground Y.dim N.R.V)
    (hadm : TraceBackground.IsAdmissibleTraceBackground N.R.contMDiff om₁ θ ε β.form)
    (hψ : IsThetaPshPotential β.form.val (ψ ∘ N.ν)) :
    ∃ hv : ∀ j, IsThetaPshPotential β.form.val (T.restrictFun (φSeq j) ∘ N.ν),
      Tendsto (fun j => (⟨T.restrictFun (φSeq j) ∘ N.ν, hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace N.R.kahler β.form
            (PluripolarCapacityDichotomy.isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
            ⟨ψ ∘ N.ν, hψ⟩) := by
  have ht' := (h.2 N).retarget om₁ N.R.kahler
  obtain ⟨hv, hlim, -⟩ := trace_independent_of_qea N.R ht' happ β hadm hψ
  simp only [Resolution.restrictFun_comp]
  exact ⟨hv, hlim⟩

/-! ### `prop:traceindquasiequisingapp` on `Ỹ` -/

/-- **Source `prop:traceindquasiequisingapp` on `Ỹ`.** For `φ ∈ QPSH(X)` with `ν(φ, Y) = 0` and
two quasi-equisingular approximations `(φ_i)`, `(ψ_i)` of `φ`,
`d_S(φ_i|_Ỹ, ψ_i|_Ỹ) → 0`, for `d_S = d_{S,η}` with any background `η` of big class containing the
restrictions (read on every resolution of `Ỹ`). -/
theorem tendsto_restrictedDistance_zero {θ₀ θ₁ : ClosedRealOneOneForm n X} {φ : X → EReal}
    {U W : ℕ → X → EReal}
    (hU : SGPT.PSH.SourceQuasiEquisingularApproximation θ₀ φ U)
    (hW : SGPT.PSH.SourceQuasiEquisingularApproximation θ₁ φ W)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    T.DistTendstoZero (fun j => T.restrictFun (U j)) (fun j => T.restrictFun (W j)) := by
  intro N η hbig hUη hWη
  simp only [Resolution.restrictFun_comp] at hUη hWη ⊢
  exact Trace2Resolution.tendsto_restrictedDistance_zero N.R hU hW hν η hbig hUη hWη

/-! ### `prop:traceunique` on `Ỹ` -/

/-- **Source `prop:traceunique` on `Ỹ`.** Two trace operators `ψ`, `ψ'` of `φ` along `Y` are
`𝓘`-good and `ψ ∼_P ψ'` (on `Ỹ`). -/
theorem IsTrace.unique {φ : X → EReal} {ψ ψ' : T.space.obj.left → EReal} (h : T.IsTrace φ ψ)
    (h' : T.IsTrace φ ψ') : T.IGood ψ ∧ T.IGood ψ' ∧ T.PEquivalent ψ ψ' := by
  have key : ∀ N : T.Resolution, SGPT.Foundations.Analysis.Pending.IGood (n := Y.dim) (ψ ∘ N.ν) ∧
      SGPT.Foundations.Analysis.Pending.IGood (n := Y.dim) (ψ' ∘ N.ν) ∧
      SourcePEquivalent (n := Y.dim) (ψ ∘ N.ν) (ψ' ∘ N.ν) := by
    intro N
    obtain ⟨om, omV, ht⟩ := h.2 N
    obtain ⟨om', omV', ht'⟩ := h'.2 N
    exact trace_unique N.R ht ht'
  exact ⟨fun N => (key N).1, fun N => (key N).2.1, fun N => (key N).2.2.1,
    fun N => (key N).2.2.2⟩

/-! ### `prop:Trdominarest` and `ex:resanalyt` on `Ỹ` -/

/-- **Source `prop:Trdominarest` on `Ỹ`.** If `φ|_Y ≢ -∞`, then `φ|_Ỹ ⪯_P Tr_Y(φ)`. -/
theorem IsTrace.restrict_pOrder {φ : X → EReal} {ψ : T.space.obj.left → EReal}
    (h : T.IsTrace φ ψ) (hne : ∃ x ∈ Y.carrier, φ x ≠ ⊥) : T.POrder (T.restrictFun φ) ψ := by
  intro N
  obtain ⟨om, omV, ht⟩ := h.2 N
  rw [Resolution.restrictFun_comp]
  exact trace_dominates_restriction N.R ht hne

/-- **Source `ex:resanalyt` on `Ỹ`.** If `φ` has analytic singularities, `Tr_Y(φ) ∼_P φ|_Ỹ`. -/
theorem IsTrace.pEquivalent_restrict_of_analytic {φ : X → EReal} {ψ : T.space.obj.left → EReal}
    (h : T.IsTrace φ ψ) (hA : QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) φ) :
    T.PEquivalent ψ (T.restrictFun φ) := by
  have key : ∀ N : T.Resolution,
      SourcePEquivalent (n := Y.dim) (ψ ∘ N.ν) (T.restrictFun φ ∘ N.ν) := by
    intro N
    obtain ⟨om, omV, ht⟩ := h.2 N
    rw [Resolution.restrictFun_comp]
    exact trace_equiv_restriction_of_analytic N.R ht hA
  exact ⟨fun N => (key N).1, fun N => (key N).2⟩

/-! ### `prop:tracelinear` on `Ỹ` -/

/-- **Source `prop:tracelinear` on `Ỹ`.** For trace operators `τ_φ`, `τ_ψ`, `τ_{φ+ψ}`, `τ_{λφ}`,
`τ_{φ∨ψ}` (on `Ỹ`) of `φ`, `ψ`, `φ + ψ`, `λφ` (`λ > 0`), `φ ∨ ψ`: (1) `φ ⪯_𝓘 ψ` implies
`τ_φ ⪯_P τ_ψ`; (2) `τ_{φ+ψ} ∼_P τ_φ + τ_ψ`; (3) `τ_{λφ} ∼_P λ τ_φ`; (4) `τ_{φ∨ψ} ∼_P τ_φ ∨ τ_ψ`. -/
theorem trace_linear {φ ψ : X → EReal} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {τφ τψ τs τℓ τm : T.space.obj.left → EReal}
    (hφ : T.IsTrace φ τφ) (hψ : T.IsTrace ψ τψ) (hs : T.IsTrace (fun x => φ x + ψ x) τs)
    (hl : T.IsTrace (fun x => (ℓ : EReal) * φ x) τℓ)
    (hm : T.IsTrace (fun x => max (φ x) (ψ x)) τm) :
    (IOrderOnManifold (n := n) φ ψ → T.POrder τφ τψ) ∧
      T.PEquivalent τs (fun y => τφ y + τψ y) ∧
      T.PEquivalent τℓ (fun y => (ℓ : EReal) * τφ y) ∧
      T.PEquivalent τm (fun y => max (τφ y) (τψ y)) := by
  have key : ∀ N : T.Resolution,
      (IOrderOnManifold (n := n) φ ψ → SourcePOrder (n := Y.dim) (τφ ∘ N.ν) (τψ ∘ N.ν)) ∧
      SourcePEquivalent (n := Y.dim) (τs ∘ N.ν) (fun v => τφ (N.ν v) + τψ (N.ν v)) ∧
      SourcePEquivalent (n := Y.dim) (τℓ ∘ N.ν) (fun v => (ℓ : EReal) * τφ (N.ν v)) ∧
      SourcePEquivalent (n := Y.dim) (τm ∘ N.ν) (fun v => max (τφ (N.ν v)) (τψ (N.ν v))) := by
    intro N
    obtain ⟨_, _, h₀⟩ := hφ.2 N
    obtain ⟨_, _, h₁⟩ := hψ.2 N
    obtain ⟨_, _, h₂⟩ := hs.2 N
    obtain ⟨_, _, h₃⟩ := hl.2 N
    obtain ⟨_, _, h₄⟩ := hm.2 N
    exact Trace2Resolution.trace_linear N.R hℓ h₀ h₁ h₂ h₃ h₄
  refine ⟨fun hI N => (key N).1 hI, ⟨fun N => (key N).2.1.1, fun N => (key N).2.1.2⟩,
    ⟨fun N => (key N).2.2.1.1, fun N => (key N).2.2.1.2⟩,
    ⟨fun N => (key N).2.2.2.1, fun N => (key N).2.2.2.2⟩⟩

/-! ### `prop:tracedeclimit` on `Ỹ` -/

/-- **Source `prop:tracedeclimit` on `Ỹ`.** Let `(u_i)` be a decreasing net in `PSH(X, θ)`
(`θ` big) with `u_i → u` in `d_S` and `ν(u, Y) = 0`. Then every `u_i` has `ν(u_i, Y) = 0`, and
for trace operators `τ_i` of `u_i` and `τ` of `u` (on `Ỹ`), `τ_i → τ` in `d_S` on `Ỹ`. -/
theorem tendsto_trace_of_antitone_net (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun i => (ui i).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u.val Y.carrier = 0) :
    (∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong (ui i).val
        Y.carrier = 0) ∧
      ∀ (τi : I → T.space.obj.left → EReal) (τ : T.space.obj.left → EReal),
        (∀ i, T.IsTrace (ui i).val (τi i)) → T.IsTrace u.val τ → T.TendstoDS atTop τi τ := by
  obtain ⟨N₀⟩ := T.nonempty_resolution
  refine ⟨fun i => ?_, ?_⟩
  · have hgen : sourceGenericLelongNumber (n := n) N₀.R.ι u.val = 0 :=
      (sourceGenericLelongNumber_eq_sourceGenericLelong N₀.R.isResolutionOf.range_eq _).trans hν
    have h := (SGPT.Trace.exists_trace_of_antitone_net Y.dim_le omega θ hbig ui u hanti hlim
      N₀.R.contMDiff hgen i).1
    exact (sourceGenericLelongNumber_eq_sourceGenericLelong N₀.R.isResolutionOf.range_eq _).symm.trans h
  · intro τi τ hTi hT N η hη hτi hτ
    have hTi' : ∀ i, ∃ (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V),
        IsSourceTraceRepresentativeAlong om omV N.R.contMDiff (ui i).val (τi i ∘ N.ν) :=
      fun i => (hTi i).2 N
    choose omegai omegaVi hTi'' using hTi'
    obtain ⟨om₀, omV₀, hT'⟩ := hT.2 N
    exact Trace2Resolution.tendsto_trace_of_antitone_net N.R omega θ hbig ui u hanti hlim η hη
      (fun i => ⟨τi i ∘ N.ν, hτi i⟩) ⟨τ ∘ N.ν, hτ⟩ hTi'' hT'

/-! ### `def:traceop2` on `Ỹ` -/

/-- **Source `def:traceop2` on `Ỹ`: the domain.** `Tr_Y(φ)` can be chosen in
`PSH(Ỹ, θ|_Ỹ)_{>0}`. -/
def HasPositiveTrace (T : TildeY Y) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) : Prop :=
  ∃ ψ : T.space.obj.left → EReal, T.IsTrace φ ψ ∧ T.IsPositive θ ψ

/-- **Source `def:traceop2` on `Ỹ`**: `Tr^θ_Y(φ) := P_{θ|_Ỹ}[Tr_Y(φ)]`, the `P`-envelope on `Ỹ`
(of a trace operator in `PSH(Ỹ, θ|_Ỹ)_{>0}`; by `traceEnvelope_eq` it does not depend on it). -/
def traceEnvelope (T : TildeY Y) (θ : ClosedRealOneOneForm n X) (φ : X → EReal)
    (h : T.HasPositiveTrace θ φ) : T.space.obj.left → EReal :=
  T.pEnvelope (T.restrict θ) (Classical.choose h)

/-- **`def:traceop2` on `Ỹ`: the domain is read on any resolution** (`cor:PSH`): `Tr^θ_Y(φ)` is
defined iff some trace operator read on (any) resolution of `Ỹ` lies in `PSH(V, ι^*θ)_{>0}`. -/
theorem hasPositiveTrace_iff (hcor : ∀ N : T.Resolution, T.CorPSH N) (N : T.Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) :
    T.HasPositiveTrace θ φ ↔ HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ := by
  constructor
  · rintro ⟨ψ, ⟨-, hT⟩, hψ, hpos⟩
    obtain ⟨om', omV', ht⟩ := hT N
    have hψN := (hcor N).comp hψ
    rw [mass_eq N θ hψN] at hpos
    exact (Trace2Resolution.hasPositiveSourceTraceAlong_iff N.R om' om omV' omV θ φ).mp
      ⟨ψ ∘ N.ν, ht, hψN, hpos⟩
  · rintro ⟨τ, ht, hτ, hpos⟩
    obtain ⟨ψ, hψ, rfl⟩ := (hcor N).descend hτ
    refine ⟨ψ, (isTrace_iff_exists (fun N => (hcor N).forward) hψ).mpr ⟨N, om, omV, ht⟩, hψ, ?_⟩
    rw [mass_eq N θ hτ]
    exact hpos

private theorem choose_spec_traceEnvelope {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (h : T.HasPositiveTrace θ φ) :
    T.IsTrace φ (Classical.choose h) ∧ T.IsPositive θ (Classical.choose h) :=
  Classical.choose_spec h

/-- **`def:traceop2` on `Ỹ`, read on a resolution**: the reading of `Tr^θ_Y(φ)` on a resolution
of `Ỹ` is the normalized trace `P_{ι^*θ}[τ]` read there (`cor:PSH`). -/
theorem traceEnvelope_comp (hcor : ∀ N : T.Resolution, T.CorPSH N) (N : T.Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} (h : T.HasPositiveTrace θ φ)
    (h' : HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ) :
    T.traceEnvelope θ φ h ∘ N.ν = sourceTraceEnvelope om omV N.R.contMDiff θ φ h' := by
  obtain ⟨⟨-, hT⟩, hψ, hpos⟩ := choose_spec_traceEnvelope h
  set ψ := Classical.choose h
  obtain ⟨om', omV', ht⟩ := hT N
  have hψN := (hcor N).comp hψ
  rw [mass_eq N θ hψN] at hpos
  rw [traceEnvelope, (pEnvelope_comp (hcor N) θ hψN).1]
  exact ((sourceTraceEnvelope_eq N.R om om' omV omV' θ φ h' ht hψN hpos).1).symm

/-- **`def:traceop2` on `Ỹ`: `Tr^θ_Y(φ) ∈ PSH(Ỹ, θ|_Ỹ)`.** -/
theorem traceEnvelope_isThetaPSH (hcor : ∀ N : T.Resolution, T.CorPSH N)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (h : T.HasPositiveTrace θ φ) :
    T.space.IsThetaPSH (T.restrict θ) (T.traceEnvelope θ φ h) := by
  obtain ⟨⟨-, -⟩, hψ, -⟩ := choose_spec_traceEnvelope h
  obtain ⟨N⟩ := T.nonempty_resolution
  exact (pEnvelope_comp (hcor N) θ ((hcor N).comp hψ)).2

/-- **`def:traceop2` on `Ỹ`: independence of the trace operator**, and
`Tr^θ_Y(φ) = P_{θ|_Ỹ}[Tr_Y(φ)] = P_{θ|_Ỹ}[Tr_Y(φ)]_𝓘`: for EVERY trace operator `ψ` of `φ` in
`PSH(Ỹ, θ|_Ỹ)_{>0}`, `Tr^θ_Y(φ) = P_{θ|_Ỹ}[ψ]`, and `Tr^θ_Y(φ)` is the `𝓘`-envelope of `ψ` on `Ỹ`
(`def:unibranch:L212`). -/
theorem traceEnvelope_eq (hcor : ∀ N : T.Resolution, T.CorPSH N) {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} (h : T.HasPositiveTrace θ φ) {ψ : T.space.obj.left → EReal}
    (hψT : T.IsTrace φ ψ) (hψ : T.IsPositive θ ψ) :
    T.traceEnvelope θ φ h = T.pEnvelope (T.restrict θ) ψ ∧
      T.IsIEnvelope θ ψ (T.traceEnvelope θ φ h) := by
  have hread : ∀ N : T.Resolution, ∃ (hψN : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)),
      T.traceEnvelope θ φ h ∘ N.ν =
        singularityEnvelope (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν) ∧
      T.traceEnvelope θ φ h ∘ N.ν =
        iSingularityEnvelope (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν) := by
    intro N
    obtain ⟨om, omV, ht⟩ := hψT.2 N
    have hψN := (hcor N).comp hψ.1
    have hpos := hψ.2
    rw [mass_eq N θ hψN] at hpos
    have h' : HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ := ⟨ψ ∘ N.ν, ht, hψN, hpos⟩
    have e := sourceTraceEnvelope_eq N.R om om omV omV θ φ h' ht hψN hpos
    rw [traceEnvelope_comp hcor N om omV h h']
    exact ⟨hψN, e.1, e.2⟩
  obtain ⟨N₀⟩ := T.nonempty_resolution
  refine ⟨?_, traceEnvelope_isThetaPSH hcor h, fun N => ?_⟩
  · obtain ⟨hψN, e₁, -⟩ := hread N₀
    exact N₀.comp_injective (e₁.trans (pEnvelope_comp (hcor N₀) θ hψN).1.symm)
  · obtain ⟨-, -, e₂⟩ := hread N
    exact e₂

/-- **`def:traceop2` on `Ỹ`, first observation**: for `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` and any
Kähler form `ω` on `X`, `Tr^{θ+ω}_Y(φ)` is defined. -/
theorem hasPositiveTrace_add_kahler (hcor : ∀ N : T.Resolution, T.CorPSH N)
    {θ : ClosedRealOneOneForm n X} (om : KahlerBackground n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    T.HasPositiveTrace (θ + om.form) φ := by
  obtain ⟨N⟩ := T.nonempty_resolution
  exact (hasPositiveTrace_iff hcor N om N.R.kahler _ φ).mpr
    (SGPT.Trace.RIsoB.hasPositiveSourceTraceAlong_add_kahler N.R om om N.R.kahler hφ hν)

/-- **`def:traceop2` on `Ỹ`, second observation**: if `θ_φ` is a Kähler current
(`φ ∈ PSH(X, θ - δω)`, `δ > 0`) and `ν(φ, Y) = 0`, `Tr^θ_Y(φ)` is defined. -/
theorem hasPositiveTrace_of_kahlerCurrent (hcor : ∀ N : T.Resolution, T.CorPSH N)
    {θ : ClosedRealOneOneForm n X} (om : KahlerBackground n X) {φ : X → EReal} {δ : ℝ}
    (hδ : 0 < δ) (hφ : IsThetaPshPotential (θ - δ • om.form).val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    T.HasPositiveTrace θ φ := by
  obtain ⟨N⟩ := T.nonempty_resolution
  exact (hasPositiveTrace_iff hcor N om N.R.kahler _ φ).mpr
    (SGPT.Trace.RIsoB.hasPositiveSourceTraceAlong_of_kahlerCurrent N.R om om N.R.kahler hδ hφ hν)

/-! ### `ex:tracedefinedposmass` on `Ỹ` -/

/-- The mass `∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y(φ))^{dim Y}` of the normalized trace on `Ỹ`, `0` if
`Tr^θ_Y(φ)` is not defined. -/
def traceMass (T : TildeY Y) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) : ℝ≥0∞ := by
  classical
  exact if h : T.HasPositiveTrace θ φ then T.mass θ (T.traceEnvelope θ φ h) else 0

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
private theorem mass_congr' {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [MeasurableSpace V] [CompactSpace V]
    {η : ClosedRealOneOneForm k V} {a b : V → EReal}
    (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b) (hab : a = b) :
    diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
  subst hab
  rfl

/-- **The trace mass on `Ỹ` is the trace mass read on any resolution** (`cor:PSH`). -/
theorem traceMass_eq (hcor : ∀ N : T.Resolution, T.CorPSH N) (N : T.Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) : T.traceMass θ φ = sourceTraceMass om omV N.R.contMDiff θ φ := by
  classical
  unfold traceMass sourceTraceMass
  by_cases h : T.HasPositiveTrace θ φ
  · have h' := (hasPositiveTrace_iff hcor N om omV θ φ).mp h
    rw [dif_pos h, dif_pos h']
    have hc := traceEnvelope_comp hcor N om omV h h'
    have hpsh : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val
        (T.traceEnvelope θ φ h ∘ N.ν) := by
      rw [hc]
      exact isThetaPshPotential_sourceTraceEnvelope om omV N.R.contMDiff θ φ h'
    rw [mass_eq N θ hpsh]
    exact mass_congr' _ _ hc
  · have h' : ¬ HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ :=
      fun h' => h ((hasPositiveTrace_iff hcor N om omV θ φ).mpr h')
    rw [dif_neg h, dif_neg h']

/-- **Source `ex:tracedefinedposmass` on `Ỹ`, the formula**: for `φ ∈ PSH(X, θ)` with
`ν(φ, Y) = 0` and any Kähler form `ω` on `X`,
`∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y φ)^{dim Y} = lim_{ε → 0+} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y φ)^{dim Y}`
(the left-hand side `0` if `Tr^θ_Y(φ)` is undefined). -/
theorem tendsto_traceMass_add_smul (hcor : ∀ N : T.Resolution, T.CorPSH N)
    (om : KahlerBackground n X) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    Tendsto (fun ε : ℝ => T.traceMass (θ + ε • om.form) φ) (𝓝[>] 0) (𝓝 (T.traceMass θ φ)) := by
  obtain ⟨N⟩ := T.nonempty_resolution
  simp_rw [traceMass_eq hcor N om N.R.kahler]
  exact SGPT.Trace.RIsoB.tendsto_sourceTraceMass_add_smul_right N.R om om N.R.kahler θ hφ hν

/-- **Source `ex:tracedefinedposmass` on `Ỹ`**: if the limit
`lim_{ε → 0+} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y φ)^{dim Y}` is positive, then `Tr^θ_Y(φ)` is
defined and its mass is that limit. -/
theorem hasPositiveTrace_of_tendsto_pos (hcor : ∀ N : T.Resolution, T.CorPSH N)
    (om : KahlerBackground n X) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    {L : ℝ≥0∞} (hL : Tendsto (fun ε : ℝ => T.traceMass (θ + ε • om.form) φ) (𝓝[>] 0) (𝓝 L))
    (hLpos : 0 < L) : T.HasPositiveTrace θ φ ∧ T.traceMass θ φ = L := by
  obtain ⟨N⟩ := T.nonempty_resolution
  simp_rw [traceMass_eq hcor N om N.R.kahler] at hL ⊢
  obtain ⟨h₁, h₂⟩ :=
    SGPT.Trace.RIsoB.hasPositiveSourceTraceAlong_of_tendsto_pos N.R om om N.R.kahler θ hφ hν hL hLpos
  exact ⟨(hasPositiveTrace_iff hcor N om N.R.kahler θ φ).mpr h₁, h₂⟩

end TildeY

/-! ### `rmk:movingSes` with the trace volumes on the normalizations -/

/-- **Source `rmk:movingSes`, on the normalizations**: for `T = θ + dd^c φ` and `x ∈ X`,
`ε(T, x) = inf_{V ∋ x} (vol Tr_V^{θ|_Ṽ} T / mult_x V)^{1/dim V}` over the positive-dimensional
closed irreducible analytic `V ∋ x`, where `vol Tr_V^{θ|_Ṽ} T` is the mass on the normalization
`Ṽ` of the normalized trace (`TildeY.traceMass`, `0` if undefined) and `mult_x V` is
`TraceRes.subvarietyMultiplicity`. -/
def movingSeshadri (Tt : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, TildeY V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  ⨅ (V : ClosedIrreducibleAnalyticSubvariety n X) (_ : x ∈ V.carrier) (_ : 0 < V.dim),
    ((Tt V).traceMass θ φ / TraceRes.subvarietyMultiplicity V x) ^ ((V.dim : ℝ)⁻¹)

/-- **`rmk:movingSes`: the moving Seshadri constant on the normalizations is the one read on any
family of resolution targets** (`cor:PSH` for the normalizations; `P5Wire`). -/
theorem movingSeshadri_eq (Tt : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, TildeY V)
    (hcor : ∀ (V : ClosedIrreducibleAnalyticSubvariety n X) (N : (Tt V).Resolution),
      (Tt V).CorPSH N)
    (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (x : X) :
    movingSeshadri Tt θ φ x = TraceRes.movingSeshadri omega₀ R θ φ x := by
  unfold movingSeshadri TraceRes.movingSeshadri
  refine iInf_congr fun V => ?_
  obtain ⟨N⟩ := (Tt V).nonempty_resolution
  have h : (Tt V).traceMass θ φ = TraceRes.resolutionTraceVolume omega₀ (R V) θ φ :=
    (TildeY.traceMass_eq (hcor V) N omega₀ N.R.kahler θ φ).trans
      (P5Wire.resolutionTraceVolume_independent omega₀ N.R (R V) θ hφ)
  rw [h]

end SGPT.Trace.TY
