import SGPT.Trace.TYTrace
import SGPT.Trace.TraceCurrent

/-!
# `rmk:tracecurrent` on the normalization `Ỹ` (presentations)

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "If `T ∈ 𝒵₊(X, α)` for some pseudo-effective class
`α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if exists) closed positive
`(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

Currents on `X` are the book's `𝒵₊(X)` (`SGPT.PSH.BookCurrent.ClosedPositiveCurrent`) with their
presentations `T = θ + dd^c φ`. A closed positive `(1,1)`-current on `Ỹ` is given here by a
presentation `S = θ̃ + dd^c ψ` with `θ̃` a smooth closed real `(1,1)`-form on `Ỹ` and
`ψ ∈ PSH(Ỹ, θ̃)` (`rmk:qpshtocurrents` on `Ỹ`); its class is that of `θ̃`.

* `IsTraceCurrent T Tc θ̃ ψ`: the current `θ̃ + dd^c ψ` on `Ỹ` represents `Tr_Y(Tc)`: `ψ` is a
  trace operator of a potential of `Tc`;
* `IsTraceCurrent.isTrace`: then `ψ` is a trace operator of EVERY potential of `Tc` (independence
  of the presentation of `Tc`), and `ν(Tc, Y) = 0`;
* `IsTraceCurrent.pEquivalent`: two currents on `Ỹ` representing `Tr_Y(Tc)` have `P`-equivalent
  potentials on `Ỹ`;
* `exists_isTraceCurrent`: if `ν(Tc, Y) = 0`, then for every Kähler form `ω` on `X` some current
  in the class of `(θ + ω)|_Ỹ` represents `Tr_Y(Tc)` (`cor:PSH`).

Not formalized: the cohomology `H^{1,1}(Ỹ, ℝ)` (equality of classes of two forms on `Ỹ`) and the
identification of two presentations of the same current on `Ỹ`.
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
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.PSH.BookCurrent SGPT.Trace.TraceCurrent

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] {Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X}

namespace TildeY

variable {T : TildeY Y}

/-- **`rmk:tracecurrent` on `Ỹ`: `θ̃ + dd^c ψ` represents `Tr_Y(Tc)`.** `θ̃` is a smooth closed real
`(1,1)`-form on `Ỹ`, `ψ ∈ PSH(Ỹ, θ̃)` (so `θ̃ + dd^c ψ` is a closed positive `(1,1)`-current on `Ỹ`
in the class of `θ̃`), and `ψ` is a trace operator of the potential of `Tc` (of every potential,
`IsTraceCurrent.isTrace`). -/
def IsTraceCurrent (T : TildeY Y) (Tc : ClosedPositiveCurrent m X) (θ : SpaceForm T.space 2)
    (ψ : T.space.obj.left → EReal) : Prop :=
  θ.IsClosed ∧ θ.IsOneOne ∧ T.space.IsThetaPSH θ ψ ∧ T.IsTrace (presentationPotential Tc) ψ

/-- Trace operators of two potentials of the same current agree. -/
theorem isTrace_of_isPresentation {Tc : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {φ φ' : X → EReal} (h₁ : IsPresentation Tc θ φ)
    (h₂ : IsPresentation Tc θ' φ') {ψ : T.space.obj.left → EReal} (h : T.IsTrace φ ψ) :
    T.IsTrace φ' ψ := by
  refine ⟨h.1, fun N => ?_⟩
  obtain ⟨om, omV, ht⟩ := h.2 N
  have hgen : sourceGenericLelongNumber (n := m + 1) N.R.ι φ' = 0 := by
    rw [← currentGenericLelongNumber_eq_of_isPresentation h₂,
      currentGenericLelongNumber_eq_of_isPresentation h₁]
    exact ht.1
  obtain ⟨τ', ht'⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential Y.dim_le
    om omV h₂.isThetaPsh.quasiPshPotential N.R.contMDiff hgen
  have hI := iEquivalentOnManifold_of_isPresentation h₁ h₂
  have hP : SourcePEquivalent (n := Y.dim) τ' (ψ ∘ N.ν) :=
    ⟨SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives Y.dim_le omV omV
        N.R.contMDiff ht' ht hI.2,
      SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives Y.dim_le omV omV
        N.R.contMDiff ht ht' hI.1⟩
  obtain ⟨-, -, -, -, -, β, -, hβ, -⟩ := ht
  exact ⟨om, omV, SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent
    N.R.contMDiff om omV ht' hβ hP⟩

/-- **Independence of the presentation of `Tc`**: if `θ̃ + dd^c ψ` represents `Tr_Y(Tc)`, then `ψ`
is a trace operator of every potential `φ` of `Tc` (`Tc = θ + dd^c φ`). -/
theorem IsTraceCurrent.isTrace {Tc : ClosedPositiveCurrent m X} {θ' : SpaceForm T.space 2}
    {ψ : T.space.obj.left → EReal} (h : T.IsTraceCurrent Tc θ' ψ)
    {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal} (hp : IsPresentation Tc θ φ) :
    T.IsTrace φ ψ :=
  isTrace_of_isPresentation (isPresentation_presentation Tc) hp h.2.2.2

/-- A current on `Ỹ` representing `Tr_Y(Tc)` forces `ν(Tc, Y) = 0`. -/
theorem IsTraceCurrent.sourceGenericLelong_eq_zero {Tc : ClosedPositiveCurrent m X}
    {θ' : SpaceForm T.space 2} {ψ : T.space.obj.left → EReal} (h : T.IsTraceCurrent Tc θ' ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0 :=
  h.2.2.2.sourceGenericLelong_eq_zero

/-- **Two currents on `Ỹ` representing `Tr_Y(Tc)` have `P`-equivalent potentials** (and the
potentials are `𝓘`-good). -/
theorem IsTraceCurrent.pEquivalent {Tc : ClosedPositiveCurrent m X} {θ₁ θ₂ : SpaceForm T.space 2}
    {ψ₁ ψ₂ : T.space.obj.left → EReal} (h₁ : T.IsTraceCurrent Tc θ₁ ψ₁)
    (h₂ : T.IsTraceCurrent Tc θ₂ ψ₂) : T.IGood ψ₁ ∧ T.IGood ψ₂ ∧ T.PEquivalent ψ₁ ψ₂ :=
  h₁.2.2.2.unique h₂.2.2.2

/-- **Existence** (`cor:PSH`): if `ν(Tc, Y) = 0` and `Tc = θ + dd^c φ`, then for every Kähler form
`ω` on `X` some closed positive current on `Ỹ` in the class of `(θ + ω)|_Ỹ` represents
`Tr_Y(Tc)`. -/
theorem exists_isTraceCurrent (hcor : ∀ N : T.Resolution, T.CorPSH N)
    (Tc : ClosedPositiveCurrent m X) {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal}
    (hp : IsPresentation Tc θ φ) (om : KahlerBackground (m + 1) X)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0) :
    ∃ ψ : T.space.obj.left → EReal, T.IsTraceCurrent Tc (T.restrict (θ + om.form)) ψ := by
  have hpres := isPresentation_presentation Tc
  have hν' : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong φ
      Y.carrier = 0 := by
    obtain ⟨N⟩ := T.nonempty_resolution
    rw [← sourceGenericLelongNumber_eq_sourceGenericLelong N.R.isResolutionOf.range_eq,
      ← currentGenericLelongNumber_eq_of_isPresentation hp,
      currentGenericLelongNumber_eq_of_isPresentation hpres,
      sourceGenericLelongNumber_eq_sourceGenericLelong N.R.isResolutionOf.range_eq]
    exact hν
  obtain ⟨ψ, hψ, hT⟩ := exists_isTrace hcor om hp.isThetaPsh hν'
  exact ⟨ψ, T.restrict_isClosed _, T.restrict_isOneOne _, hψ,
    isTrace_of_isPresentation hp hpres hT⟩

end TildeY

end SGPT.Trace.TY
