import SGPT.Trace.TY2H11

/-!
# `rmk:tracecurrent` on the normalization: `Tr^β_Y(T)` for `β ∈ H^{1,1}(Ỹ, ℝ)`

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "As in `rmk:qpshtocurrents`, the trace operator
could also be applied to closed positive `(1,1)`-currents on `X`. If `T ∈ 𝒵₊(X, α)` for some
pseudo-effective class `α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if
exists) closed positive `(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

Currents on `X` are the book's `𝒵₊(X)` (`SGPT.PSH.BookCurrent.ClosedPositiveCurrent`, every
`T ∈ 𝒵₊(X)` lies in `𝒵₊(X, {T})`). A closed positive `(1,1)`-current on `Ỹ` is given by a
presentation `S = θ̃ + dd^c ψ` (`θ̃` a smooth closed real `(1,1)`-form on `Ỹ`,
`PD.IsLocallyClosedOneOne`; `ψ ∈ PSH(Ỹ, θ̃)`), its class is `{θ̃} ∈ H^{1,1}(Ỹ, ℝ)`
(`SGPT.Unibranch.H11`, `TY2H11`).

* `TildeY.IsTraceCurrentIn T Tc β θ̃ ψ` (**`Tr^β_Y(Tc)`**): the current `θ̃ + dd^c ψ` lies in `β`
  and represents `Tr_Y(Tc)`: `ψ` is a trace operator of the potential of `Tc` (of every potential:
  `IsTraceCurrentIn.isTrace`; this forces `ν(Tc, Y) = 0`: `IsTraceCurrentIn.sourceGenericLelong_eq_zero`).
* `IsTraceCurrentIn.pEquivalent`: two currents representing `Tr_Y(Tc)` have `𝓘`-good,
  `P`-equivalent potentials (`Tr_Y(T)` is defined up to `P`-equivalence).
* `IsTraceCurrentIn.of_rel`: the notion only depends on the class: replacing `θ̃` by
  `θ̃ + dd^c f` (`f` smooth on `Ỹ`) does not change `β`.
* `Normalization.exists_isTraceCurrentIn_of_corPSH`: on the normalization `Ỹ`, if `ν(Tc, Y) = 0`
  and `Tc = θ + dd^c φ`, then for every Kähler form `ω` on `X` some current in the class
  `{(θ + ω)|_Ỹ} ∈ H^{1,1}(Ỹ, ℝ)` represents `Tr_Y(Tc)` (`cor:PSH`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.PSH.BookCurrent SGPT.Trace.TraceCurrent

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] {Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X}

namespace TildeY

variable {T : TildeY Y}

/-- **Source `rmk:tracecurrent` on `Ỹ`: `Tr^β_Y(Tc)`.** The closed positive `(1,1)`-current
`θ̃ + dd^c ψ` on `Ỹ` (`θ̃` a smooth closed real `(1,1)`-form on `Ỹ`, `ψ ∈ PSH(Ỹ, θ̃)`) lies in the
class `β ∈ H^{1,1}(Ỹ, ℝ)` and represents `Tr_Y(Tc)`: `ψ` is a trace operator of the potential of
`Tc`. -/
def IsTraceCurrentIn (T : TildeY Y) (Tc : ClosedPositiveCurrent m X) (β : H11 T.space)
    (θ : SpaceForm T.space 2) (ψ : T.space.obj.left → EReal) : Prop :=
  ∃ hθ : PD.IsLocallyClosedOneOne θ, H11.ofForm ⟨θ, hθ⟩ = β ∧ T.space.IsThetaPSH θ ψ ∧
    T.IsTrace (presentationPotential Tc) ψ

/-- A current in a class representing `Tr_Y(Tc)` represents `Tr_Y(Tc)` (`TYTraceCurrent`). -/
theorem IsTraceCurrentIn.isTraceCurrent {Tc : ClosedPositiveCurrent m X} {β : H11 T.space}
    {θ : SpaceForm T.space 2} {ψ : T.space.obj.left → EReal} (h : T.IsTraceCurrentIn Tc β θ ψ) :
    T.IsTraceCurrent Tc θ ψ := by
  obtain ⟨hθ, -, hψ, hT⟩ := h
  exact ⟨hθ.isClosed, hθ.isOneOne, hψ, hT⟩

/-- **Independence of the presentation of `Tc`**: `ψ` is a trace operator of EVERY potential of
`Tc`. -/
theorem IsTraceCurrentIn.isTrace {Tc : ClosedPositiveCurrent m X} {β : H11 T.space}
    {θ' : SpaceForm T.space 2} {ψ : T.space.obj.left → EReal} (h : T.IsTraceCurrentIn Tc β θ' ψ)
    {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal} (hp : IsPresentation Tc θ φ) :
    T.IsTrace φ ψ :=
  h.isTraceCurrent.isTrace hp

/-- `Tr^β_Y(Tc)` exists only when `ν(Tc, Y) = 0`. -/
theorem IsTraceCurrentIn.sourceGenericLelong_eq_zero {Tc : ClosedPositiveCurrent m X}
    {β : H11 T.space} {θ' : SpaceForm T.space 2} {ψ : T.space.obj.left → EReal}
    (h : T.IsTraceCurrentIn Tc β θ' ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0 :=
  h.isTraceCurrent.sourceGenericLelong_eq_zero

/-- **Two currents on `Ỹ` representing `Tr_Y(Tc)`** (in any classes) have `𝓘`-good,
`P`-equivalent potentials. -/
theorem IsTraceCurrentIn.pEquivalent {Tc : ClosedPositiveCurrent m X} {β₁ β₂ : H11 T.space}
    {θ₁ θ₂ : SpaceForm T.space 2} {ψ₁ ψ₂ : T.space.obj.left → EReal}
    (h₁ : T.IsTraceCurrentIn Tc β₁ θ₁ ψ₁) (h₂ : T.IsTraceCurrentIn Tc β₂ θ₂ ψ₂) :
    T.IGood ψ₁ ∧ T.IGood ψ₂ ∧ T.PEquivalent ψ₁ ψ₂ :=
  h₁.isTraceCurrent.pEquivalent h₂.isTraceCurrent

/-- **The class of the current only depends on its class**: if `θ̃ + dd^c ψ` lies in `β`, so does
every `θ̃'` with `θ̃' = θ̃ + dd^c f`, `f` smooth on `Ỹ`. -/
theorem IsTraceCurrentIn.ofForm_eq {Tc : ClosedPositiveCurrent m X} {β : H11 T.space}
    {θ : SpaceForm T.space 2} {ψ : T.space.obj.left → EReal} (h : T.IsTraceCurrentIn Tc β θ ψ)
    {θ' : SpaceForm T.space 2} (hθ' : PD.IsLocallyClosedOneOne θ')
    {f : T.space.obj.left → ℝ} (hf : T.space.IsSmoothFunction f)
    (hrel : SpaceForm.SameForm (θ.add (SpaceForm.ddcOf f hf)) θ') :
    H11.ofForm ⟨θ', hθ'⟩ = β := by
  obtain ⟨hθ, hβ, -, -⟩ := h
  rw [← hβ]
  exact (H11.ofForm_eq_of_rel hf hrel).symm

end TildeY

namespace Normalization

/-- **Source `rmk:tracecurrent` on the normalization, existence** (`cor:PSH`): if `ν(Tc, Y) = 0`
and `Tc = θ + dd^c φ`, then for every Kähler form `ω` on `X` some closed positive current on `Ỹ`
in the class `{(θ + ω)|_Ỹ} ∈ H^{1,1}(Ỹ, ℝ)` represents `Tr_Y(Tc)`. -/
theorem exists_isTraceCurrentIn_of_corPSH (hPD : CorPSHStatement)
    (omega : KahlerBackground (m + 1) X) (Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X)
    (Tc : ClosedPositiveCurrent m X) {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal}
    (hp : IsPresentation Tc θ φ) (om : KahlerBackground (m + 1) X)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0) :
    ∃ ψ : (normalizationTildeY omega Y).space.obj.left → EReal,
      (normalizationTildeY omega Y).IsTraceCurrentIn Tc
        (H11.ofForm ⟨_, restrict_isLocallyClosedOneOne omega Y (θ + om.form)⟩)
        ((normalizationTildeY omega Y).restrict (θ + om.form)) ψ := by
  obtain ⟨ψ, -, -, hψ, hT⟩ :=
    TildeY.exists_isTraceCurrent (corPSH_all_of_statement hPD omega Y) Tc hp om hν
  exact ⟨ψ, restrict_isLocallyClosedOneOne omega Y (θ + om.form), rfl, hψ, hT⟩

end Normalization

end SGPT.Trace.TY
