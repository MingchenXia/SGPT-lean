import SGPT.Trace.TY2Footnote
import SGPT.Trace.TY3Potential

/-!
# `def:traceop` on the normalization: the trace predicate is the book's, for all `ψ ∈ QPSH(Ỹ)`


Source: `chapter_trace.tex`, `def:traceop` and its footnote: "Let `φ ∈ QPSH(X)` be a function such
that `ν(φ, Y) = 0`. We say a potential `ψ ∈ QPSH(Ỹ)` is a trace operator of `φ` along `Y` if there
is a quasi-equisingular approximation `(φ_j)` of `φ` such that `φ_j|_Ỹ → ψ` in `d_S`", where
(footnote) "We can find a closed smooth real `(1,1)`-form `θ` on `X` such that `φ ∈ PSH(X, θ)`.
Then there is a Kähler form such that `ω + θ + dd^c φ_j ≥ 0` for all `j ≥ 1`. Take a Kähler form
`ω̃` on `Ỹ` so that `ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)`. Then our condition means that
`φ_j|_Ỹ → ψ` in `d_{S, ω̃}`. This condition is independent of the choices of `θ`, `ω` and `ω̃`."

The trace predicate of lane TY on the normalization, `TildeY.IsTrace`, asks `ψ ∈ QPSH(Ỹ)` and the
trace condition on EVERY resolution `ν : V → Ỹ`. Lane TY2 formalized the footnote
(`Normalization.FootnoteCondition`: `d_{S, ω̃}` on `Ỹ` read on a resolution `F : (V, 𝒪_V) → Ỹ`
with the background `F^*ω̃`) and proved `IsTrace ↔ FootnoteCondition` for `ψ ∈ PSH(Ỹ, θ'|_Ỹ)`,
`θ'` a form on `X`. With the readings of all quasi-psh functions on `Ỹ` quasi-psh on every
resolution (`TY3Potential.isThetaPshPotential_comp_of_isQPSH`), this file removes that restriction:

* `isQPSH_comp_of_isQPSH`: readings of `ψ ∈ QPSH(Ỹ)` are quasi-psh on every resolution;
* `isTrace_iff_isTraceOn_of_isQPSH`, `isTrace_iff_exists_of_isQPSH`: **for every `ψ ∈ QPSH(Ỹ)`,
  `ψ` is a trace operator iff its reading on ONE (any) resolution of `Ỹ` is** (so the
  quantification over all resolutions in `IsTrace` is no stronger than the reading on one);
* `isTrace_iff_footnoteCondition_of_isThetaPSH`: **`def:traceop` with its footnote for every
  `ψ ∈ QPSH(Ỹ)`**: for every choice of `θ`, `(φ_j)`, `ω`, `ω̃` (`ω̃ ≥ (θ + ω)|_Ỹ`,
  `ψ ∈ PSH(Ỹ, ω̃)`) and every resolution of `Ỹ` given by a proper bimeromorphic morphism `F`,
  `ψ` is a trace operator of `φ` iff `φ_j|_Ỹ → ψ` in `d_{S, ω̃}` (TY2's theorem had the extra
  hypothesis `ψ ∈ PSH(Ỹ, θ'|_Ỹ)`);
* `IsBookTrace`, `isTrace_iff_isBookTrace`: **the book's definition verbatim** (`ψ ∈ QPSH(Ỹ)` and
  there are `θ`, a quasi-equisingular approximation `(φ_j)` of `φ ∈ PSH(X, θ)`, a Kähler form `ω`
  with `ω + θ + dd^c φ_j ≥ 0`, a Kähler form `ω̃ ≥ (θ + ω)|_Ỹ` with `ψ ∈ PSH(Ỹ, ω̃)` and a
  resolution `F` of `Ỹ` on which `φ_j|_Ỹ → ψ` in `d_{S, ω̃}`) is equivalent, under the book's
  standing hypothesis `ν(φ, Y) = 0`, to `TildeY.IsTrace`;
* `pOrder_iff_of_isQPSH`, `pEquivalent_iff_of_isQPSH`: for quasi-psh functions on `Ỹ`, the
  `P`-order and `P`-equivalence on `Ỹ` (read on every resolution) are their readings on any one
  resolution.

Together with `TY3Holomorphic` (every resolution `ν : V → Ỹ` is holomorphic in the local
embeddings of `Ỹ`), this removes the caveat of TY2 on `def:traceop`: `TildeY.IsTrace` is the book's
trace predicate for all `ψ ∈ QPSH(Ỹ)`, hence so are the trace predicates in the statements of lane
TY (`prop:traceindquasiequisingapp`, `prop:traceunique`, `prop:Trdominarest`, `ex:resanalyt`,
`prop:tracelinear`, `prop:tracedeclimit`, `lma:rescommpullback`) and lane TY2 (`def:traceop2`,
`ex:tracedefinedposmass`, `rmk:movingSes`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

namespace Normalization

variable (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)

/-- **Readings of quasi-psh functions on `Ỹ` are quasi-psh** (in the sense of the variable atlas
of `V`), on every resolution `ν : V → Ỹ`. -/
theorem isQPSH_comp_of_isQPSH {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).IsQPSH ψ) (N : (normalizationTildeY omega Y).Resolution) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel Y.dim N.R.V).IsQPSH (ψ ∘ N.ν) := by
  obtain ⟨σ, hσ⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hψ N
  exact ⟨SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas σ,
    (SGPT.PSH.VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential _ _).mpr
      (by rw [SGPT.PSH.VariableComplexAtlas.sourceNativeAtlasForm_roundTrip]; exact hσ)⟩

/-- **`def:traceop` on `Ỹ`: any one resolution decides.** For every `ψ ∈ QPSH(Ỹ)` and every
resolution `ν : V → Ỹ`, `ψ` is a trace operator of `φ` along `Y` iff `ψ ∘ ν` is a trace operator
of `φ` on `V`. -/
theorem isTrace_iff_isTraceOn_of_isQPSH {φ : X → EReal}
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).IsQPSH ψ) (N : (normalizationTildeY omega Y).Resolution) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔ TildeY.IsTraceOn N φ (ψ ∘ N.ν) := by
  constructor
  · exact fun h => h.2 N
  · intro h
    refine ⟨hψ, fun N' => ?_⟩
    obtain ⟨σ, hσ⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hψ N'
    exact TildeY.transfer N N' h hσ

/-- **`def:traceop` on `Ỹ`: independence of the resolution, for every `ψ ∈ QPSH(Ỹ)`.** -/
theorem isTrace_iff_exists_of_isQPSH {φ : X → EReal}
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).IsQPSH ψ) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔
      ∃ N : (normalizationTildeY omega Y).Resolution, TildeY.IsTraceOn N φ (ψ ∘ N.ν) := by
  constructor
  · intro h
    obtain ⟨N⟩ := (normalizationTildeY omega Y).nonempty_resolution
    exact ⟨N, h.2 N⟩
  · rintro ⟨N, h⟩
    exact (isTrace_iff_isTraceOn_of_isQPSH omega Y hψ N).mpr h

/-- **`def:traceop` with the footnote, for every `ψ ∈ QPSH(Ỹ)`.** Let `F : (V, 𝒪_V) → Ỹ` be a
resolution of the normalization given by a proper bimeromorphic morphism, `φ ∈ PSH(X, θ)` with
`ν(φ, Y) = 0`, `(φ_j)` a quasi-equisingular approximation of `φ`, `ω` a Kähler form on `X` with
`ω + θ + dd^c φ_j ≥ 0` for all `j`, and `ω̃` a Kähler form on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ` and
`ψ ∈ PSH(Ỹ, ω̃)`. Then `ψ` is a trace operator of `φ` along `Y` iff `φ_j|_Ỹ → ψ` in
`d_{S, ω̃}`. -/
theorem isTrace_iff_footnoteCondition_of_isThetaPSH {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔ FootnoteCondition omega Y F hK φSeq ψ := by
  have hq : (normalizationTildeY omega Y).IsQPSH ψ := ⟨omt, hK.isClosed, hK.isOneOne, hψ⟩
  rw [isTrace_iff_isTraceOn_of_isQPSH omega Y hq N]
  exact isTraceOn_iff_footnoteCondition omega Y F hF hFN happ hν om hom hK hdom hψ

/-- **Source `def:traceop`, verbatim with its footnote, on the normalization `Ỹ`.** `ψ ∈ QPSH(Ỹ)`,
and there are a closed real `(1,1)`-form `θ` on `X` and a quasi-equisingular approximation
`(φ_j)` of `φ ∈ PSH(X, θ)`, a Kähler form `ω` on `X` with `ω + θ + dd^c φ_j ≥ 0` for all `j`, a
Kähler form `ω̃` on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)`, such that
`φ_j|_Ỹ → ψ` in `d_{S, ω̃}` (`d_{S, ω̃}` on `Ỹ` computed on a resolution `F : (V, 𝒪_V) → Ỹ`,
`sec:unib_ext`; it does not depend on `F`, `footnoteCondition_resolution_congr`). -/
def IsBookTrace (φ : X → EReal) (ψ : (normalizationTildeY omega Y).space.obj.left → EReal) :
    Prop :=
  (normalizationTildeY omega Y).IsQPSH ψ ∧
    ∃ (θ : ClosedRealOneOneForm n X) (omega' : KahlerBackground n X) (ε : ℕ → ℝ)
      (φSeq : ℕ → X → EReal), IsQuasiEquisingularApproximation omega' θ φ ε φSeq ∧
      ∃ om : KahlerBackground n X, (∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j)) ∧
        ∃ (omt : SpaceForm (normalizationTildeY omega Y).space 2) (hK : omt.IsKahler),
          omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)) ∧
          (normalizationTildeY omega Y).space.IsThetaPSH omt ψ ∧
          ∃ (N : (normalizationTildeY omega Y).Resolution)
            (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space),
            IsProperBimeromorphic F ∧ (∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v) ∧
            FootnoteCondition omega Y F hK φSeq ψ

/-- **`TildeY.IsTrace` is the book's `def:traceop`.** Under the book's standing hypothesis
`ν(φ, Y) = 0`, `ψ` is a trace operator of `φ` along `Y` in the sense of `TildeY.IsTrace` iff it is
one in the sense of the book's definition and footnote (`IsBookTrace`), for every `ψ` on `Ỹ`. -/
theorem isTrace_iff_isBookTrace {φ : X → EReal}
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    (ψ : (normalizationTildeY omega Y).space.obj.left → EReal) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔ IsBookTrace omega Y φ ψ := by
  constructor
  · intro h
    have hq := h.1
    obtain ⟨η, -, -, hη⟩ := hq
    obtain ⟨N₀⟩ := (normalizationTildeY omega Y).nonempty_resolution
    obtain ⟨om₀, omV, ht⟩ := h.2 N₀
    obtain ⟨-, θ, ε, φSeq, happ, -⟩ := ht
    obtain ⟨om, hom, omt, hK, hdom, -, hψ⟩ := exists_footnote_choices omega Y happ η hη
    obtain ⟨N, F, hF, hFN⟩ := exists_resolution_morphism omega Y
    exact ⟨h.1, θ, om₀, ε, φSeq, happ, om, hom, omt, hK, hdom, hψ, N, F, hF, hFN,
      IsTrace.footnoteCondition omega Y F hF hFN happ om hom hK hdom hψ h⟩
  · rintro ⟨-, θ, omega', ε, φSeq, happ, om, hom, omt, hK, hdom, hψ, N, F, hF, hFN, hfoot⟩
    exact (isTrace_iff_footnoteCondition_of_isThetaPSH omega Y F hF hFN happ hν om hom hK hdom
      hψ).mpr hfoot

/-- **Every trace operator satisfies the footnote's condition for EVERY choice** of `θ`, `(φ_j)`,
`ω`, `ω̃` and of the resolution `F` (the footnote's "This condition is independent of the choices
of `θ`, `ω` and `ω̃`"), and conversely one choice suffices (`isTrace_iff_isBookTrace`). -/
theorem IsBookTrace.footnoteCondition_of_choices {φ : X → EReal}
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal} (h : IsBookTrace omega Y φ ψ)
    {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {θ : ClosedRealOneOneForm n X} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ) :
    FootnoteCondition omega Y F hK φSeq ψ :=
  IsTrace.footnoteCondition omega Y F hF hFN happ om hom hK hdom hψ
    ((isTrace_iff_isBookTrace omega Y hν ψ).mpr h)

/-- **`P`-order on `Ỹ` for quasi-psh functions is decided on any one resolution.** -/
theorem pOrder_iff_of_isQPSH {u v : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hu : (normalizationTildeY omega Y).IsQPSH u) (hv : (normalizationTildeY omega Y).IsQPSH v)
    (N : (normalizationTildeY omega Y).Resolution) :
    (normalizationTildeY omega Y).POrder u v ↔
      SourcePOrder (n := Y.dim) (u ∘ N.ν) (v ∘ N.ν) := by
  rw [TildeY.pOrder_iff_exists (fun N' => isQPSH_comp_of_isQPSH omega Y hu N')
    (fun N' => isQPSH_comp_of_isQPSH omega Y hv N')]
  constructor
  · rintro ⟨N₁, h₁⟩
    exact (TildeY.pOrder_iff_exists (fun N' => isQPSH_comp_of_isQPSH omega Y hu N')
      (fun N' => isQPSH_comp_of_isQPSH omega Y hv N')).mpr ⟨N₁, h₁⟩ N
  · exact fun h => ⟨N, h⟩

/-- **`P`-equivalence on `Ỹ` for quasi-psh functions is decided on any one resolution.** -/
theorem pEquivalent_iff_of_isQPSH {u v : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hu : (normalizationTildeY omega Y).IsQPSH u) (hv : (normalizationTildeY omega Y).IsQPSH v)
    (N : (normalizationTildeY omega Y).Resolution) :
    (normalizationTildeY omega Y).PEquivalent u v ↔
      SourcePOrder (n := Y.dim) (u ∘ N.ν) (v ∘ N.ν) ∧
        SourcePOrder (n := Y.dim) (v ∘ N.ν) (u ∘ N.ν) := by
  unfold TildeY.PEquivalent
  rw [pOrder_iff_of_isQPSH omega Y hu hv N, pOrder_iff_of_isQPSH omega Y hv hu N]

/-- **Trace operators are closed under `P`-equivalence in `QPSH(Ỹ)`** (`prop:ds0char`): if `ψ` is
a trace operator of `φ` and `ψ' ∈ QPSH(Ỹ)` is `P`-equivalent to `ψ`, then `ψ'` is a trace
operator of `φ`. -/
theorem IsTrace.of_pEquivalent {φ : X → EReal}
    {ψ ψ' : (normalizationTildeY omega Y).space.obj.left → EReal}
    (h : (normalizationTildeY omega Y).IsTrace φ ψ) (hψ' : (normalizationTildeY omega Y).IsQPSH ψ')
    (hP : (normalizationTildeY omega Y).PEquivalent ψ ψ') :
    (normalizationTildeY omega Y).IsTrace φ ψ' := by
  refine ⟨hψ', fun N => ?_⟩
  obtain ⟨om, omV, ht⟩ := h.2 N
  obtain ⟨σ, hσ⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hψ' N
  exact ⟨om, omV, SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent
    N.R.contMDiff om omV ht hσ ⟨hP.1 N, hP.2 N⟩⟩

/-- **`Tr_Y(φ)` is well defined exactly up to `P`-equivalence** (`def:traceop2`: "The trace
operator `Tr_Y(φ)` is therefore well-defined only up to `P`-equivalence by `prop:traceunique`"): if
`ψ` is a trace operator of `φ`, the trace operators of `φ` are exactly the `ψ' ∈ QPSH(Ỹ)` with
`ψ ∼_P ψ'`. -/
theorem IsTrace.isTrace_iff {φ : X → EReal}
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (h : (normalizationTildeY omega Y).IsTrace φ ψ)
    (ψ' : (normalizationTildeY omega Y).space.obj.left → EReal) :
    (normalizationTildeY omega Y).IsTrace φ ψ' ↔
      (normalizationTildeY omega Y).IsQPSH ψ' ∧ (normalizationTildeY omega Y).PEquivalent ψ ψ' :=
  ⟨fun h' => ⟨h'.1, (TildeY.IsTrace.unique h h').2.2⟩,
    fun h' => IsTrace.of_pEquivalent omega Y h h'.1 h'.2⟩

end Normalization

end SGPT.Trace.TY
