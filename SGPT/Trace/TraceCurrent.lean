import SGPT.Trace.BertiniGeneralTrace
import SGPT.PSH.BookCurrentSpace
import SGPT.Okounkov.ThetaPotentialCurrentReader
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder

/-!
# Traces of closed positive currents

Source: `chapter_trace.tex`, `rmk:tracecurrent` (blueprint `claude-bertini:tracecurrent`): "As in
`rmk:qpshtocurrents`, the trace operator could also be applied to closed positive
`(1,1)`-currents on `X`. If `T ∈ 𝒵₊(X, α)` for some pseudo-effective class `α` and
`β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if exists) closed positive
`(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

As for `def:traceop` (`SGPT.Trace.SmoothTarget`), the target is a compact connected complex
manifold `Y` with a holomorphic map `ι : Y → X` (for instance a connected submanifold, its own
normalization); singular targets (normalizations of singular `Y`) are not covered. Currents are
the book's `𝒵₊(X)` (`SGPT.PSH.BookCurrent.ClosedPositiveCurrent`, `def:spaceofcurrents`), with
presentations `T = θ + dd^c φ` (`IsPresentation`), and `rmk:qpshtocurrents` identifies currents
with quasi-psh functions modulo bounded smooth differences.

* `currentGenericLelongNumber T ι` (`ν(T, Y)`): the generic Lelong number of any potential of
  `T` along `ι` (`currentGenericLelongNumber_eq_of_isPresentation`: independent of the
  presentation).
* `IsTraceCurrent ω ω_Y hι T S` (`S` represents `Tr_Y(T)`): a potential of `S` is a trace
  operator of a potential of `T`. This does not depend on the presentations
  (`IsTraceCurrent.isSourceTraceRepresentativeAlong`: EVERY potential of `S` is a trace operator
  of EVERY potential of `T`).
* `IsTraceCurrentIn β T S` for `S ∈ 𝒵₊(Y, β)`: the book's `Tr^β_Y(T)`.
* `IsTraceCurrent.sourcePEquivalent`: two currents representing `Tr_Y(T)` have `P`-equivalent
  potentials (`Tr_Y(T)` is well defined up to `P`-equivalence, `prop:traceunique`).
* `exists_isTraceCurrent`: if `ν(T, Y) = 0`, some current (in a Kähler class) represents
  `Tr_Y(T)`; `isTraceCurrentIn_of_hasPositiveSourceTraceAlong`: if `Tr^θ_Y(φ)` is defined
  (`def:traceop2`), `ι^*θ + dd^c Tr` is a `Tr^{ι^*\{θ\}}_Y(T)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.TraceCurrent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
  SGPT.PSH.BookCurrent

variable {m k : ℕ} {X Y : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (k + 1)) Y] [IsComplexManifold (k + 1) Y]
  {ι : Y → X}

/-- `ν(T, Y)`: the generic Lelong number along `ι` of a potential of `T` (the convention
`ν(T, x) = ν(φ, x)` of `ex:Lelongcurrent`). -/
def currentGenericLelongNumber (T : ClosedPositiveCurrent m X) (ι : Y → X) : ℝ≥0∞ :=
  sourceGenericLelongNumber (n := m + 1) ι (presentationPotential T)

omit [TopologicalSpace Y] in
/-- `ν(T, Y)` does not depend on the presentation of `T`. -/
theorem currentGenericLelongNumber_eq_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal} (h : IsPresentation T θ φ) :
    currentGenericLelongNumber T ι = sourceGenericLelongNumber (n := m + 1) ι φ := by
  obtain ⟨hφ, hT⟩ := h
  obtain ⟨hφ₀, hT₀⟩ := isPresentation_presentation T
  exact SGPT.Okounkov.sourceGeneric_eq_of_thetaPotentialCurrent_eq hφ₀ hφ (hT₀.symm.trans hT) ι

/-- Potentials of the same current have the same multiplier ideals. -/
theorem iEquivalentOnManifold_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ θ' : ClosedRealOneOneForm (m + 1) X} {φ φ' : X → EReal} (h : IsPresentation T θ φ)
    (h' : IsPresentation T θ' φ') : IEnvelope.IOrderOnManifold (n := m + 1) φ φ' ∧
      IEnvelope.IOrderOnManifold (n := m + 1) φ' φ := by
  obtain ⟨⟨C, hC⟩, ⟨C', hC'⟩⟩ := singularityEquiv_of_isPresentation h h'
  exact ⟨iOrderOnManifold_of_le_add h'.isThetaPsh.1.quasiPlurisubharmonic
      (C := C) fun x => hC x (mem_univ x),
    iOrderOnManifold_of_le_add h.isThetaPsh.1.quasiPlurisubharmonic
      (C := C') fun x => hC' x (mem_univ x)⟩

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  (hι : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

/-- **`S` represents `Tr_Y(T)`** (`rmk:tracecurrent`): for presentations `T = θ + dd^c φ` and
`S = η + dd^c τ`, `τ` is a trace operator of `φ` along `ι` (`def:traceop`; this includes
`ν(T, Y) = 0`). -/
def IsTraceCurrent (omega : KahlerBackground (m + 1) X) (omegaY : KahlerBackground (k + 1) Y)
    (T : ClosedPositiveCurrent m X) (S : ClosedPositiveCurrent k Y) : Prop :=
  ∃ (θ : ClosedRealOneOneForm (m + 1) X) (φ : X → EReal) (η : ClosedRealOneOneForm (k + 1) Y)
    (τ : Y → EReal), IsPresentation T θ φ ∧ IsPresentation S η τ ∧
      IsSourceTraceRepresentativeAlong omega omegaY hι φ τ

/-- **`Tr^β_Y(T)`** (`rmk:tracecurrent`): a closed positive `(1,1)`-current `S ∈ 𝒵₊(Y, β)` in the
class `β` representing `Tr_Y(T)`. -/
def IsTraceCurrentIn (omega : KahlerBackground (m + 1) X) (omegaY : KahlerBackground (k + 1) Y)
    (T : ClosedPositiveCurrent m X) {β : RealBottChern (k + 1) Y}
    (S : ClosedPositiveCurrentIn k Y β) : Prop :=
  IsTraceCurrent hι omega omegaY T S.1

/-- **Independence of the presentations.** If `S` represents `Tr_Y(T)`, then for EVERY
presentation `T = θ + dd^c φ` and EVERY presentation `S = η + dd^c τ`, `τ` is a trace operator of
`φ` along `ι`; in particular `ν(T, Y) = 0`. -/
theorem IsTraceCurrent.isSourceTraceRepresentativeAlong (hk : k + 1 ≤ m + 1)
    {omega : KahlerBackground (m + 1) X} {omegaY : KahlerBackground (k + 1) Y}
    {T : ClosedPositiveCurrent m X} {S : ClosedPositiveCurrent k Y}
    (hTS : IsTraceCurrent hι omega omegaY T S) {θ : ClosedRealOneOneForm (m + 1) X}
    {φ : X → EReal} {η : ClosedRealOneOneForm (k + 1) Y} {τ : Y → EReal}
    (hT : IsPresentation T θ φ) (hS : IsPresentation S η τ) :
    IsSourceTraceRepresentativeAlong omega omegaY hι φ τ := by
  obtain ⟨θ₀, φ₀, η₀, τ₀, hT₀, hS₀, htr₀⟩ := hTS
  have hgen : sourceGenericLelongNumber (n := m + 1) ι φ = 0 := by
    rw [← currentGenericLelongNumber_eq_of_isPresentation hT,
      currentGenericLelongNumber_eq_of_isPresentation hT₀]
    exact htr₀.1
  obtain ⟨τ₁, htr₁⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
    omegaY hT.isThetaPsh.quasiPshPotential hι hgen
  have hI := iEquivalentOnManifold_of_isPresentation hT hT₀
  have h₁₀ : SourcePEquivalent (n := k + 1) τ₁ τ₀ :=
    ⟨SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaY omegaY hι
        htr₁ htr₀ hI.1,
      SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaY omegaY hι
        htr₀ htr₁ hI.2⟩
  obtain ⟨hle, hge⟩ := singularityEquiv_of_isPresentation hS₀ hS
  have h₀ : SourcePEquivalent (n := k + 1) τ₀ τ :=
    ⟨sourcePOrder_of_moreSingularOn omegaY η₀ η hS₀.isThetaPsh hS.isThetaPsh hle,
      sourcePOrder_of_moreSingularOn omegaY η η₀ hS.isThetaPsh hS₀.isThetaPsh hge⟩
  have heq : SourcePEquivalent (n := k + 1) τ₁ τ :=
    ⟨SourcePOrder.trans omegaY h₁₀.1 h₀.1, SourcePOrder.trans omegaY h₀.2 h₁₀.2⟩
  exact SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent hι omega
    omegaY htr₁ hS.isThetaPsh heq

/-- `S` represents `Tr_Y(T)` as soon as one potential of `S` is a trace operator of one
potential of `T`, and then `ν(T, Y) = 0`. -/
theorem IsTraceCurrent.currentGenericLelongNumber_eq_zero {omega : KahlerBackground (m + 1) X}
    {omegaY : KahlerBackground (k + 1) Y} {T : ClosedPositiveCurrent m X}
    {S : ClosedPositiveCurrent k Y} (hTS : IsTraceCurrent hι omega omegaY T S) :
    currentGenericLelongNumber T ι = 0 := by
  obtain ⟨_, _, _, _, hT, -, htr⟩ := hTS
  rw [currentGenericLelongNumber_eq_of_isPresentation hT]
  exact htr.1

/-- **`Tr_Y(T)` is well defined up to `P`-equivalence** (`prop:traceunique` for currents): if
`S` and `S'` both represent `Tr_Y(T)` (with arbitrary auxiliary choices), then all their
potentials are `P`-equivalent. -/
theorem IsTraceCurrent.sourcePEquivalent (hk : k + 1 ≤ m + 1)
    {omega omega' : KahlerBackground (m + 1) X} {omegaY omegaY' : KahlerBackground (k + 1) Y}
    {T : ClosedPositiveCurrent m X} {S S' : ClosedPositiveCurrent k Y}
    (hS : IsTraceCurrent hι omega omegaY T S) (hS' : IsTraceCurrent hι omega' omegaY' T S')
    {η η' : ClosedRealOneOneForm (k + 1) Y} {τ τ' : Y → EReal}
    (hpS : IsPresentation S η τ) (hpS' : IsPresentation S' η' τ') :
    SourcePEquivalent (n := k + 1) τ τ' := by
  have hT := isPresentation_presentation T
  exact SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives hk omegaY omegaY' hι
    (hS.isSourceTraceRepresentativeAlong hι hk hT hpS)
    (hS'.isSourceTraceRepresentativeAlong hι hk hT hpS')

/-- **Existence.** If `ν(T, Y) = 0`, some closed positive current (in a Kähler class of `Y`)
represents `Tr_Y(T)`. -/
theorem exists_isTraceCurrent (hk : k + 1 ≤ m + 1) (omega : KahlerBackground (m + 1) X)
    (omegaY : KahlerBackground (k + 1) Y) (T : ClosedPositiveCurrent m X)
    (hν : currentGenericLelongNumber T ι = 0) :
    ∃ (β : KahlerBackground (k + 1) Y) (S : ClosedPositiveCurrentIn k Y
      (RealBottChern.ofRepresentative β.form)), IsTraceCurrentIn hι omega omegaY T S := by
  have hT := isPresentation_presentation T
  rw [currentGenericLelongNumber_eq_of_isPresentation hT] at hν
  obtain ⟨τ, htr⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
    omegaY hT.isThetaPsh.quasiPshPotential hι hν
  have hcopy := htr
  obtain ⟨_, _, _, _, _, β, _, hτ, _, _⟩ := hcopy
  exact ⟨β, ⟨thetaPositiveCurrent β.form τ hτ, currentClass_thetaPositiveCurrent _ _ _⟩,
    _, _, _, _, hT, isPresentation_thetaPositiveCurrent _ _ hτ, htr⟩

omit [CompactSpace X] in
/-- **`Tr^θ_Y` for currents.** If `T = θ + dd^c φ` and `Tr^θ_Y(φ)` is defined
(`def:traceop2`: a trace operator `τ ∈ PSH(Y, ι^*θ)_{>0}`), then `ι^*θ + dd^c τ ∈ 𝒵₊(Y, {ι^*θ})`
is a `Tr^{\{ι^*θ\}}_Y(T)`. -/
theorem exists_isTraceCurrentIn_of_hasPositiveSourceTraceAlong
    (omega : KahlerBackground (m + 1) X) (omegaY : KahlerBackground (k + 1) Y)
    {T : ClosedPositiveCurrent m X} {θ : ClosedRealOneOneForm (m + 1) X} {φ : X → EReal}
    (hT : IsPresentation T θ φ) (hdef : HasPositiveSourceTraceAlong omega omegaY hι θ φ) :
    ∃ S : ClosedPositiveCurrentIn k Y
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hι θ)),
      IsTraceCurrentIn hι omega omegaY T S := by
  obtain ⟨τ, htr, hτ, -⟩ := hdef
  exact ⟨⟨thetaPositiveCurrent _ τ hτ, currentClass_thetaPositiveCurrent _ _ _⟩,
    _, _, _, _, hT, isPresentation_thetaPositiveCurrent _ _ hτ, htr⟩

end SGPT.Trace.TraceCurrent
