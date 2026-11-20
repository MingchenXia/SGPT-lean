import SGPT.Trace.TY2ThetaForms
import SGPT.Trace.TYCorPSH
import SGPT.Trace.TYTraceCurrent
import SGPT.Unibranch.PDThetaLimsup

/-!
# `cor:PSH` for the normalization `Ỹ` from `cor:PSH` for general `θ`

Source: `appendix_unibranch.tex`, `cor:PSH`: for a proper bimeromorphic morphism `π : Y → X` with
`X` unibranch and a smooth closed real `(1,1)`-form `θ` on `X`, `π^* : PSH(X, θ) → PSH(Y, π^*θ)`
is a bijection; `chapter_trace.tex`, Section "The definition of the trace operator":
`def:traceop`, `def:traceop2`, `rmk:tracecurrent`, `ex:tracedefinedposmass`, `rmk:movingSes`.

Lane TY proved these five entries on the normalization `Ỹ` (`normalizationTildeY`) assuming the
descent half of `cor:PSH` along one resolution morphism `F : (V, 𝒪_V) → Ỹ` for the forms `θ|_Ỹ`
(`TYCorPSH.corPSH_all_of_descent`). Lane PD2 proves `cor:PSH` for general `θ` in the form

  `Function.Bijective (PD.thetaPSHPullback θ π hπ hX)` for `hθ : PD.IsLocallyClosedOneOne θ`

(`PD.thetaPSHPullback` and `PD.IsLocallyClosedOneOne` are lane PD's). This file:

* `CorPSHStatement`: that statement, for all complex spaces, as a proposition;
* `CorPSHStatement.descentAlong`: it gives the descent half `CorPSHDescentAlong π θ`;
* `Normalization.corPSH_all_of_statement`: with `TY2ThetaForms.restrict_isLocallyClosedOneOne`
  (every `θ|_Ỹ` satisfies PD2's hypothesis) it gives `TildeY.CorPSH N` for every resolution `N` of
  the normalization;
* the five entries on the normalization with `CorPSHStatement` as their only hypothesis
  (`*_of_corPSH`); the unconditional versions are obtained by instantiating `CorPSHStatement` with
  the theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification

/-- **`cor:PSH` for general `θ`** (the statement): for every proper bimeromorphic morphism
`π : Y → X` of complex spaces with `X` unibranch and every smooth closed real `(1,1)`-form `θ` on
`X` (`PD.IsLocallyClosedOneOne θ`), the pull-back `π^* : PSH(X, θ) → PSH(Y, π^*θ)` is bijective. -/
def CorPSHStatement : Prop :=
  ∀ ⦃X Y : SourceReducedComplexSpace⦄ (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    (hX : X.IsUnibranch) (θ : SpaceForm X 2), PD.IsLocallyClosedOneOne θ →
      Function.Bijective (PD.thetaPSHPullback θ π hπ hX)

/-- `cor:PSH` gives its descent half: every `π^*θ`-psh function on `Y` is the pull-back of a
`θ`-psh function on `X`. -/
theorem CorPSHStatement.descentAlong (h : CorPSHStatement) {X Y : SourceReducedComplexSpace}
    {π : Y ⟶ X} (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) {θ : SpaceForm X 2}
    (hθ : PD.IsLocallyClosedOneOne θ) : KSUnibranchIEnvelope.CorPSHDescentAlong π θ :=
  (PD.thetaPSHPullback_bijective_iff θ π hπ hX).mp (h π hπ hX θ hθ)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Normalization

/-- **`cor:PSH` for the normalization `Ỹ`**: given `cor:PSH` for general `θ`, for every
resolution `ν : V → Ỹ` of the normalization and every smooth closed real `(1,1)`-form `θ` on `X`,
`ψ ↦ ψ ∘ ν` is a bijection `PSH(Ỹ, θ|_Ỹ) ≅ PSH(V, ι^*θ)` (`TildeY.CorPSH`). -/
theorem corPSH_all_of_statement (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∀ N : (normalizationTildeY omega Y).Resolution, (normalizationTildeY omega Y).CorPSH N := by
  obtain ⟨_N, F, hF, _hFN, h⟩ := corPSH_all_of_descent omega Y
  exact h fun θ => hPD.descentAlong hF
    (KSNormalizedSubvariety.normalization_isUnibranch Y.carrier Y.analytic)
    (restrict_isLocallyClosedOneOne omega Y θ)

end Normalization

/-! ### The five entries on the normalization, given `cor:PSH` -/

namespace Normalization

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- **Source `def:traceop` on `Ỹ`, existence**: for `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` and any
Kähler form `ω` on `X`, `φ` has a trace operator along `Y` in `PSH(Ỹ, (θ + ω)|_Ỹ)`. -/
theorem exists_isTrace_of_corPSH (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X}
    (om : KahlerBackground n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    ∃ ψ : (normalizationTildeY omega Y).space.obj.left → EReal,
      (normalizationTildeY omega Y).space.IsThetaPSH
        ((normalizationTildeY omega Y).restrict (θ + om.form)) ψ ∧
      (normalizationTildeY omega Y).IsTrace φ ψ :=
  TildeY.exists_isTrace (corPSH_all_of_statement hPD omega Y) om hφ hν

/-- **Source `def:traceop2` on `Ỹ`: the domain is read on any resolution.** -/
theorem hasPositiveTrace_iff_of_corPSH (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ ↔
      SGPT.Trace.HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ :=
  TildeY.hasPositiveTrace_iff (corPSH_all_of_statement hPD omega Y) N om omV θ φ

/-- **Source `def:traceop2` on `Ỹ`: `Tr^θ_Y(φ)` read on a resolution** is the normalized trace
there. -/
theorem traceEnvelope_comp_of_corPSH (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) {θ : ClosedRealOneOneForm n X}
    {φ : X → EReal} (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ)
    (h' : SGPT.Trace.HasPositiveSourceTraceAlong om omV N.R.contMDiff θ φ) :
    (normalizationTildeY omega Y).traceEnvelope θ φ h ∘ N.ν =
      SGPT.Trace.sourceTraceEnvelope om omV N.R.contMDiff θ φ h' :=
  TildeY.traceEnvelope_comp (corPSH_all_of_statement hPD omega Y) N om omV h h'

/-- **Source `def:traceop2` on `Ỹ`: `Tr^θ_Y(φ) ∈ PSH(Ỹ, θ|_Ỹ)`.** -/
theorem traceEnvelope_isThetaPSH_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ) :
    (normalizationTildeY omega Y).space.IsThetaPSH ((normalizationTildeY omega Y).restrict θ)
      ((normalizationTildeY omega Y).traceEnvelope θ φ h) :=
  TildeY.traceEnvelope_isThetaPSH (corPSH_all_of_statement hPD omega Y) h

/-- **Source `def:traceop2` on `Ỹ`**: `Tr^θ_Y(φ) = P_{θ|_Ỹ}[ψ] = P_{θ|_Ỹ}[ψ]_𝓘` for EVERY trace
operator `ψ` of `φ` in `PSH(Ỹ, θ|_Ỹ)_{>0}`. -/
theorem traceEnvelope_eq_of_corPSH (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (h : (normalizationTildeY omega Y).HasPositiveTrace θ φ)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψT : (normalizationTildeY omega Y).IsTrace φ ψ)
    (hψ : (normalizationTildeY omega Y).IsPositive θ ψ) :
    (normalizationTildeY omega Y).traceEnvelope θ φ h =
        (normalizationTildeY omega Y).pEnvelope ((normalizationTildeY omega Y).restrict θ) ψ ∧
      (normalizationTildeY omega Y).IsIEnvelope θ ψ
        ((normalizationTildeY omega Y).traceEnvelope θ φ h) :=
  TildeY.traceEnvelope_eq (corPSH_all_of_statement hPD omega Y) h hψT hψ

/-- **Source `def:traceop2` on `Ỹ`, first observation**: `Tr^{θ+ω}_Y(φ)` is defined for
`φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` and every Kähler form `ω` on `X`. -/
theorem hasPositiveTrace_add_kahler_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    {θ : ClosedRealOneOneForm n X} (om : KahlerBackground n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    (normalizationTildeY omega Y).HasPositiveTrace (θ + om.form) φ :=
  TildeY.hasPositiveTrace_add_kahler (corPSH_all_of_statement hPD omega Y) om hφ hν

/-- **Source `def:traceop2` on `Ỹ`, second observation**: if `θ_φ` is a Kähler current and
`ν(φ, Y) = 0`, `Tr^θ_Y(φ)` is defined. -/
theorem hasPositiveTrace_of_kahlerCurrent_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    {θ : ClosedRealOneOneForm n X} (om : KahlerBackground n X) {φ : X → EReal} {δ : ℝ}
    (hδ : 0 < δ) (hφ : IsThetaPshPotential (θ - δ • om.form).val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ :=
  TildeY.hasPositiveTrace_of_kahlerCurrent (corPSH_all_of_statement hPD omega Y) om hδ hφ hν

/-- **The trace mass on `Ỹ` is the trace mass read on any resolution.** -/
theorem traceMass_eq_of_corPSH (hPD : CorPSHStatement) (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) :
    (normalizationTildeY omega Y).traceMass θ φ =
      SGPT.Trace.sourceTraceMass om omV N.R.contMDiff θ φ :=
  TildeY.traceMass_eq (corPSH_all_of_statement hPD omega Y) N om omV θ φ

/-- **Source `ex:tracedefinedposmass` on `Ỹ`, the formula**:
`∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y φ)^{dim Y} = lim_{ε → 0+} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y φ)^{dim Y}`
(the left-hand side `0` if `Tr^θ_Y(φ)` is undefined). -/
theorem tendsto_traceMass_add_smul_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    (om : KahlerBackground n X) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0) :
    Tendsto (fun ε : ℝ => (normalizationTildeY omega Y).traceMass (θ + ε • om.form) φ) (𝓝[>] 0)
      (𝓝 ((normalizationTildeY omega Y).traceMass θ φ)) :=
  TildeY.tendsto_traceMass_add_smul (corPSH_all_of_statement hPD omega Y) om θ hφ hν

/-- **Source `ex:tracedefinedposmass` on `Ỹ`**: if the limit of the masses is positive,
`Tr^θ_Y(φ)` is defined and its mass is that limit. -/
theorem hasPositiveTrace_of_tendsto_pos_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    (om : KahlerBackground n X) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    {L : ℝ≥0∞}
    (hL : Tendsto (fun ε : ℝ => (normalizationTildeY omega Y).traceMass (θ + ε • om.form) φ)
      (𝓝[>] 0) (𝓝 L))
    (hLpos : 0 < L) :
    (normalizationTildeY omega Y).HasPositiveTrace θ φ ∧
      (normalizationTildeY omega Y).traceMass θ φ = L :=
  TildeY.hasPositiveTrace_of_tendsto_pos (corPSH_all_of_statement hPD omega Y) om θ hφ hν hL hLpos

end Normalization

/-- **Source `rmk:movingSes` on the normalizations**: the moving Seshadri constant
`ε(T, x) = inf_{V ∋ x} (vol Tr_V^{θ|_Ṽ} T / mult_x V)^{1/dim V}`, with the trace volumes on the
normalizations `Ṽ` (`normalizationTildeY`), equals the one read on any family of resolution
targets of the `V`. -/
theorem movingSeshadri_normalization_eq_of_corPSH [MeasurableSpace X] [BorelSpace X]
    [ConnectedSpace X] (hPD : CorPSHStatement) (omega omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (x : X) :
    movingSeshadri (fun V => normalizationTildeY omega V) θ φ x =
      TraceRes.movingSeshadri omega₀ R θ φ x :=
  movingSeshadri_eq (fun V => normalizationTildeY omega V)
    (fun V => Normalization.corPSH_all_of_statement hPD omega V) omega₀ R θ hφ x

end SGPT.Trace.TY
