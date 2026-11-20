import SGPT.Trace.TY2TraceCurrent
import SGPT.Unibranch.PD2ThetaDescent

/-!
# The trace on the normalization `Ỹ`, unconditionally

Source: `chapter_trace.tex`, Section "The definition of the trace operator": `def:traceop`,
`def:traceop2`, `rmk:tracecurrent`, `ex:tracedefinedposmass`, `rmk:movingSes`; Appendix B,
`cor:PSH`.

Lane PD2 proved `cor:PSH` for general `θ` (`SGPT.Unibranch.PD.corPSH_bijective`: for a proper
bimeromorphic `π : Y → X` onto a unibranch complex space and a smooth closed real `(1,1)`-form `θ`
on `X` in the sense of `PD.IsLocallyClosedOneOne`, `π^* : PSH(X, θ) → PSH(Y, π^*θ)` is
bijective). This is exactly `CorPSHStatement` (`TY2CorPSH`), so:

* `corPSHStatement : CorPSHStatement`;
* `Normalization.corPSH_all`: `cor:PSH` for every resolution `ν : V → Ỹ` of the normalization and
  the forms `θ|_Ỹ` (`TildeY.CorPSH`), unconditionally;
* the theorems of lane TY on `Ỹ` which used `cor:PSH` hold unconditionally on the normalization:
  `def:traceop` (existence of a trace operator in `PSH(Ỹ, (θ + ω)|_Ỹ)`), `def:traceop2` (domain and
  normalized trace read on any resolution, `Tr^θ_Y(φ) ∈ PSH(Ỹ, θ|_Ỹ)`, independence of the trace
  operator and `P[Tr] = P[Tr]_𝓘`, the two observations), `ex:tracedefinedposmass` (the formula and
  the positivity criterion), `rmk:movingSes` (the moving Seshadri constant with the trace volumes on
  the normalizations `Ṽ`), `rmk:tracecurrent` (existence of `Tr^β_Y(T)` in the class
  `β = {(θ + ω)|_Ỹ} ∈ H^{1,1}(Ỹ, ℝ)`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.PSH.BookCurrent SGPT.Trace.TraceCurrent

/-- **`cor:PSH` for general `θ`**, in the form used by the trace theory. -/
theorem corPSHStatement : CorPSHStatement :=
  fun _ _ π hπ hX θ hθ => PD.corPSH_bijective π hπ hX θ hθ

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Normalization

/-- **`cor:PSH` for the normalization `Ỹ`** (unconditional): for every resolution `ν : V → Ỹ` and
every smooth closed real `(1,1)`-form `θ` on `X`, `ψ ↦ ψ ∘ ν` is a bijection
`PSH(Ỹ, θ|_Ỹ) ≅ PSH(V, ι^*θ)`. -/
theorem corPSH_all (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∀ N : (normalizationTildeY omega Y).Resolution, (normalizationTildeY omega Y).CorPSH N :=
  corPSH_all_of_statement corPSHStatement omega Y

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-! ### `def:traceop` -/

/-- **Source `def:traceop` on `Ỹ`, existence** ("Indeed ... it converges"): for `φ ∈ PSH(X, θ)`
with `ν(φ, Y) = 0` and any Kähler form `ω` on `X`, `φ` has a trace operator along `Y` in
`PSH(Ỹ, (θ + ω)|_Ỹ)`. -/
theorem exists_isTrace (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X}
    (om : KahlerBackground n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    ∃ ψ : (normalizationTildeY omega Y).space.obj.left → EReal,
      (normalizationTildeY omega Y).space.IsThetaPSH
        ((normalizationTildeY omega Y).restrict (θ + om.form)) ψ ∧
      (normalizationTildeY omega Y).IsTrace φ ψ :=
  exists_isTrace_of_corPSH corPSHStatement omega Y om hφ hν

/-! ### `def:traceop2` -/

/-- **Source `def:traceop2` on `Ỹ`: the domain is read on any resolution**: `Tr^θ_Y(φ)` is
defined iff the normalized trace is defined on (any) resolution of `Ỹ`. -/
theorem hasPositiveTrace_iff (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ ↔
      SGPT.Trace.HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ :=
  hasPositiveTrace_iff_of_corPSH corPSHStatement omega Y N om omV θ φ

/-- **Source `def:traceop2` on `Ỹ`: `Tr^θ_Y(φ)` read on a resolution** of `Ỹ` is the normalized
trace `P_{ι^*θ}[τ]` read there. -/
theorem traceEnvelope_comp (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ)
    (h' : SGPT.Trace.HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ) :
    (normalizationTildeY omega Y).traceEnvelope θ φ h ∘ N.ν =
      SGPT.Trace.sourceTraceEnvelope om omV N.R.contMDiff θ φ h' :=
  traceEnvelope_comp_of_corPSH corPSHStatement omega Y N om omV h h'

/-- **Source `def:traceop2` on `Ỹ`: `Tr^θ_Y(φ) ∈ PSH(Ỹ, θ|_Ỹ)`.** -/
theorem traceEnvelope_isThetaPSH (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ) :
    (normalizationTildeY omega Y).space.IsThetaPSH ((normalizationTildeY omega Y).restrict θ)
      ((normalizationTildeY omega Y).traceEnvelope θ φ h) :=
  traceEnvelope_isThetaPSH_of_corPSH corPSHStatement omega Y h

/-- **Source `def:traceop2` on `Ỹ`**: `Tr^θ_Y(φ) = P_{θ|_Ỹ}[ψ]` and it is the `𝓘`-envelope
`P_{θ|_Ỹ}[ψ]_𝓘` (`def:unibranch:L212`), for EVERY trace operator `ψ` of `φ` in
`PSH(Ỹ, θ|_Ỹ)_{>0}` (independence of the choice of `Tr_Y(φ)`). -/
theorem traceEnvelope_eq (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψT : (normalizationTildeY omega Y).IsTrace φ ψ)
    (hψ : (normalizationTildeY omega Y).IsPositive θ ψ) :
    (normalizationTildeY omega Y).traceEnvelope θ φ h =
        (normalizationTildeY omega Y).pEnvelope ((normalizationTildeY omega Y).restrict θ) ψ ∧
      (normalizationTildeY omega Y).IsIEnvelope θ ψ
        ((normalizationTildeY omega Y).traceEnvelope θ φ h) :=
  traceEnvelope_eq_of_corPSH corPSHStatement omega Y h hψT hψ

/-- **Source `def:traceop2` on `Ỹ`, first observation**: for `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0`
and any Kähler form `ω` on `X`, `Tr^{θ+ω}_Y(φ)` is defined. -/
theorem hasPositiveTrace_add_kahler (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X}
    (om : KahlerBackground n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    (normalizationTildeY omega Y).HasPositiveTrace (θ + om.form) φ :=
  hasPositiveTrace_add_kahler_of_corPSH corPSHStatement omega Y om hφ hν

/-- **Source `def:traceop2` on `Ỹ`, second observation**: if `θ_φ` is a Kähler current
(`φ ∈ PSH(X, θ - δω)`, `δ > 0`) and `ν(φ, Y) = 0`, `Tr^θ_Y(φ)` is defined. -/
theorem hasPositiveTrace_of_kahlerCurrent (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X}
    (om : KahlerBackground n X) {φ : X → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hφ : IsThetaPshPotential (θ - δ • om.form).val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ :=
  hasPositiveTrace_of_kahlerCurrent_of_corPSH corPSHStatement omega Y om hδ hφ hν

/-! ### `ex:tracedefinedposmass` -/

/-- **The trace mass on `Ỹ` is the trace mass read on any resolution.** -/
theorem traceMass_eq (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    (N : (normalizationTildeY omega Y).Resolution) (om : KahlerBackground n X)
    (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) :
    (normalizationTildeY omega Y).traceMass θ φ =
      SGPT.Trace.sourceTraceMass om omV N.R.contMDiff θ φ :=
  traceMass_eq_of_corPSH corPSHStatement omega Y N om omV θ φ

/-- **Source `ex:tracedefinedposmass` on `Ỹ`, the formula**: for `φ ∈ PSH(X, θ)` with
`ν(φ, Y) = 0` and any Kähler form `ω` on `X`,
`∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y φ)^{dim Y} = lim_{ε → 0+} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y φ)^{dim Y}`
(the left-hand side `0` if `Tr^θ_Y(φ)` is undefined). -/
theorem tendsto_traceMass_add_smul (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (om : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    Tendsto (fun ε : ℝ => (normalizationTildeY omega Y).traceMass (θ + ε • om.form) φ) (𝓝[>] 0)
      (𝓝 ((normalizationTildeY omega Y).traceMass θ φ)) :=
  tendsto_traceMass_add_smul_of_corPSH corPSHStatement omega Y om θ hφ hν

/-- **Source `ex:tracedefinedposmass` on `Ỹ`**: if
`lim_{ε → 0+} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y φ)^{dim Y} > 0`, then `Tr^θ_Y(φ)` is defined
and its mass is exactly that limit. -/
theorem hasPositiveTrace_of_tendsto_pos (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (om : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    {L : ℝ≥0∞}
    (hL : Tendsto (fun ε : ℝ => (normalizationTildeY omega Y).traceMass (θ + ε • om.form) φ)
      (𝓝[>] 0) (𝓝 L))
    (hLpos : 0 < L) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ ∧
      (normalizationTildeY omega Y).traceMass θ φ = L :=
  hasPositiveTrace_of_tendsto_pos_of_corPSH corPSHStatement omega Y om θ hφ hν hL hLpos

end Normalization

/-! ### `rmk:movingSes` -/

/-- **Source `rmk:movingSes`, on the normalizations** (unconditional): the moving Seshadri
constant `ε(T, x) = inf_{V ∋ x} (vol Tr_V^{θ|_Ṽ} T / mult_x V)^{1/dim V}` with the trace volumes
on the normalizations `Ṽ` (`movingSeshadri (fun V => normalizationTildeY omega V)`) equals the one
read on any family of resolution targets of the `V`. -/
theorem movingSeshadri_normalization_eq [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (omega omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (x : X) :
    movingSeshadri (fun V => normalizationTildeY omega V) θ φ x =
      TraceRes.movingSeshadri omega₀ R θ φ x :=
  movingSeshadri_normalization_eq_of_corPSH corPSHStatement omega omega₀ R θ hφ x

/-! ### `rmk:tracecurrent` -/

namespace Normalization

/-- **Source `rmk:tracecurrent` on the normalization, existence** (unconditional): if
`ν(Tc, Y) = 0` and `Tc = θ + dd^c φ`, then for every Kähler form `ω` on `X` some closed positive
`(1,1)`-current on `Ỹ` in the class `{(θ + ω)|_Ỹ} ∈ H^{1,1}(Ỹ, ℝ)` represents `Tr_Y(Tc)`, i.e.
`Tr^{{(θ+ω)|_Ỹ}}_Y(Tc)` exists. -/
theorem exists_isTraceCurrentIn {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (omega : KahlerBackground (m + 1) X) (Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X)
    (Tc : ClosedPositiveCurrent m X) {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal}
    (hp : IsPresentation Tc θ φ) (om : KahlerBackground (m + 1) X)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0) :
    ∃ ψ : (normalizationTildeY omega Y).space.obj.left → EReal,
      (normalizationTildeY omega Y).IsTraceCurrentIn Tc
        (H11.ofForm ⟨_, restrict_isLocallyClosedOneOne omega Y (θ + om.form)⟩)
        ((normalizationTildeY omega Y).restrict (θ + om.form)) ψ :=
  exists_isTraceCurrentIn_of_corPSH corPSHStatement omega Y Tc hp om hν

end Normalization

end SGPT.Trace.TY
