import SGPT.Trace.TY3Footnote

/-!
# `rmk:tracecurrent` on the normalization: dependence on the potential only through its
`P`-class

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "If `T ∈ 𝒵₊(X, α)` for some pseudo-effective class
`α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if exists) closed positive
`(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

Lanes TY/TY2 handle closed positive `(1,1)`-currents on `Ỹ` through presentations `θ̃ + dd^c ψ`
(`TildeY.IsTraceCurrent`, `TildeY.IsTraceCurrentIn`). With the closure of trace operators under
`P`-equivalence in `QPSH(Ỹ)` (`TY3Footnote.IsTrace.of_pEquivalent`) we get:

* `Normalization.IsTraceCurrent.of_pEquivalent`, `IsTraceCurrentIn.of_pEquivalent`: whether a
  presented current represents `Tr_Y(T)` depends on its potential only through the
  `P`-equivalence class of the potential (any other presentation in `β` with a `P`-equivalent
  potential, e.g. a potential differing by a bounded function, also represents `Tr_Y(T)`);
* `Normalization.isTraceCurrentIn_iff`: given one current `θ̃ + dd^c ψ ∈ β` representing
  `Tr_Y(T)`, the presented currents in `β` representing `Tr_Y(T)` are exactly the `θ̃' + dd^c ψ'`
  with `θ̃' ∈ β`, `ψ' ∈ PSH(Ỹ, θ̃')` and `ψ' ∼_P ψ` ("any closed positive current in `β`
  representing `Tr_Y(T)`").

Not formalized (the remaining point of `rmk:tracecurrent`): closed positive currents on the
singular space `Ỹ` as objects, and the fact that two presentations of the SAME current on `Ỹ`
have forms differing by `dd^c f` with `f` smooth on `Ỹ` (regularity of pluriharmonic functions on
the normal space `Ỹ`), which makes the class of a current independent of its presentation.
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
  [ConnectedSpace X]

namespace Normalization

variable (omega : KahlerBackground (m + 1) X) (Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X)

/-- **A presented current on `Ỹ` representing `Tr_Y(Tc)`: only the `P`-class of the potential
matters.** If `θ̃ + dd^c ψ` represents `Tr_Y(Tc)` and `ψ' ∈ PSH(Ỹ, θ̃')` (`θ̃'` closed, `(1,1)`) is
`P`-equivalent to `ψ`, then `θ̃' + dd^c ψ'` represents `Tr_Y(Tc)`. -/
theorem IsTraceCurrent.of_pEquivalent {Tc : ClosedPositiveCurrent m X}
    {θ θ' : SpaceForm (normalizationTildeY omega Y).space 2}
    {ψ ψ' : (normalizationTildeY omega Y).space.obj.left → EReal}
    (h : (normalizationTildeY omega Y).IsTraceCurrent Tc θ ψ) (hc : θ'.IsClosed)
    (h11 : θ'.IsOneOne) (hψ' : (normalizationTildeY omega Y).space.IsThetaPSH θ' ψ')
    (hP : (normalizationTildeY omega Y).PEquivalent ψ ψ') :
    (normalizationTildeY omega Y).IsTraceCurrent Tc θ' ψ' :=
  ⟨hc, h11, hψ', IsTrace.of_pEquivalent omega Y h.2.2.2 ⟨θ', hc, h11, hψ'⟩ hP⟩

/-- **`Tr^β_Y(Tc)`: only the `P`-class of the potential matters.** -/
theorem IsTraceCurrentIn.of_pEquivalent {Tc : ClosedPositiveCurrent m X}
    {β : H11 (normalizationTildeY omega Y).space}
    {θ θ' : SpaceForm (normalizationTildeY omega Y).space 2}
    {ψ ψ' : (normalizationTildeY omega Y).space.obj.left → EReal}
    (h : (normalizationTildeY omega Y).IsTraceCurrentIn Tc β θ ψ)
    (hθ' : PD.IsLocallyClosedOneOne θ') (hβ : H11.ofForm ⟨θ', hθ'⟩ = β)
    (hψ' : (normalizationTildeY omega Y).space.IsThetaPSH θ' ψ')
    (hP : (normalizationTildeY omega Y).PEquivalent ψ ψ') :
    (normalizationTildeY omega Y).IsTraceCurrentIn Tc β θ' ψ' := by
  obtain ⟨-, -, -, hT⟩ := h
  exact ⟨hθ', hβ, hψ', IsTrace.of_pEquivalent omega Y hT ⟨θ', hθ'.isClosed, hθ'.isOneOne, hψ'⟩
    hP⟩

/-- **The currents `Tr^β_Y(Tc)`.** Given one presented current `θ̃ + dd^c ψ ∈ β` representing
`Tr_Y(Tc)`, a presented current `θ̃' + dd^c ψ'` (`θ̃'` a smooth closed real `(1,1)`-form on `Ỹ`)
lies in `β` and represents `Tr_Y(Tc)` iff `{θ̃'} = β`, `ψ' ∈ PSH(Ỹ, θ̃')` and `ψ' ∼_P ψ`. -/
theorem isTraceCurrentIn_iff {Tc : ClosedPositiveCurrent m X}
    {β : H11 (normalizationTildeY omega Y).space}
    {θ : SpaceForm (normalizationTildeY omega Y).space 2}
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (h : (normalizationTildeY omega Y).IsTraceCurrentIn Tc β θ ψ)
    (θ' : SpaceForm (normalizationTildeY omega Y).space 2)
    (ψ' : (normalizationTildeY omega Y).space.obj.left → EReal) :
    (normalizationTildeY omega Y).IsTraceCurrentIn Tc β θ' ψ' ↔
      ∃ hθ' : PD.IsLocallyClosedOneOne θ', H11.ofForm ⟨θ', hθ'⟩ = β ∧
        (normalizationTildeY omega Y).space.IsThetaPSH θ' ψ' ∧
        (normalizationTildeY omega Y).PEquivalent ψ ψ' := by
  constructor
  · intro h'
    have hP := (h.pEquivalent h').2.2
    obtain ⟨hθ', hβ', hψ', -⟩ := h'
    exact ⟨hθ', hβ', hψ', hP⟩
  · rintro ⟨hθ', hβ', hψ', hP⟩
    exact IsTraceCurrentIn.of_pEquivalent omega Y h hθ' hβ' hψ' hP

end Normalization

end SGPT.Trace.TY
