import SGPT.Trace.OTExtGlobalReduction
import SGPT.Trace.TraceEnvelope
import SGPT.Trace.SmoothTarget
import SGPT.PSH.GlobalL2BergmanLower
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

/-!
# The global Ohsawa--Takegoshi extension theorem for the trace operator `thm:OT_ext_global`

Blueprint `claude-ot2.tex`, nodes `claude-ot2:statement-def`, `claude-ot2:trace-order`,
`claude-ot2:main`, `claude-ot2:point`, `claude-ot2:OT-ext-global`.  Source `thm:OT_ext_global`
(`chapter_trace.tex` 527--532):

> Let `L` be a big line bundle on `X` and let `θ` be a closed real smooth `(1,1)`-form on `X`
> representing `c₁(L)`. Suppose that `φ ∈ PSH(X,θ)` and `θ_φ` is a Kähler current. Assume that
> `Y` is smooth and `ν(φ,Y) = 0`. Let `T` be a holomorphic line bundle on `X`. Then there exists
> `k₀` such that for all `k ≥ k₀` and `s ∈ H⁰(Y, T|_Y ⊗ L|_Y^k ⊗ 𝓘(k Tr_Y^θ(φ)))`, there exists
> an extension `s̃ ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`.

## Formalization

* `X` is a compact Kähler manifold (`KahlerBackground ωb`); `L`, `T` are holomorphic line bundles
  with smooth Hermitian metrics, `θ = c₁(L, h_L)` (`IsOwnFirstChernForm`).  This is how the
  project states "`θ` represents `c₁(L)`" (as in `thm:OT_ext`, `prop:Bergman_approx`,
  `thm:DXmain1`): every representative is the curvature of some smooth metric by the
  `∂∂̄`-lemma, and the conclusion does not involve the metrics.
* `θ_φ` is a Kähler current: `IsKahlerCurrentPotential θ φ` (this implies `φ ∈ PSH(X, θ)`).
  Bigness of `L` is implied by the existence of such `φ` and is not assumed.
* `Y` smooth: a closed connected complex submanifold `W` (`IsClosedConnectedSubmanifold n W m`, as
  in `prop:OT2`, `SGPT.Trace.multiplierIdeal_trace_le_restrictIdeal`), with the induced complex
  structure and Kähler form; `ν(φ, Y) = 0` is `sourceGenericLelongNumber Subtype.val φ = 0`.
* `Tr_Y^θ(φ)` is `sourceTraceEnvelope` (`def:traceop2`); it is defined under these hypotheses
  (`hasPositiveSourceTraceAlong_of_hyps`); the statement quantifies over the (unique) proof of
  definedness.
* `H⁰(Y, T|_Y ⊗ L|_Y^k ⊗ 𝓘(k Tr))` is `IsAlongMultiplierSection` and
  `H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` is `fullHolomorphicIdealSections _ (sourceDegreeMultiplierIdeal k φ)`,
  as in `thm:OT_ext` (`SGPT.Trace.TwistedL2.OTExtAlong`).

## Results

* `OTExtGlobalAlong`, `OTExtGlobalStatement`: the statement.
* `iOrderOnManifold_traceEnvelope_stage`: `Tr_Y^θ(φ) ≼_𝓘 Φ_q|_Y` for every stage of every
  quasi-equisingular approximation of `φ` (the book's `Tr_Y^θ(φ) ⪯_P φ_j|_Y` and
  `cor:PimpliesI`).
* `otExtGlobalAlong_of_existence`: **the book's proof** — `thm:OT_ext_global` for the data
  `(ωb, L, T, θ, W, φ)` follows from the margin existence part of `thm:OT_ext`
  (`OTExtMarginExistenceAlong`, analytic singularities, exponent `kt → k`, `t > 1`) for
  `(ωb, L, T, θ, W)` and every `δ > 0`.
* `otExtGlobalStatement_of_marginExistence`: `OTExtMarginExistenceStatement ⇒ thm:OT_ext_global`;
  `otExtGlobalStatement_of_otExtStatement`: `thm:OT_ext ⇒ thm:OT_ext_global`.
* `otExtGlobalAlong_of_dim_zero`: `thm:OT_ext_global` when `dim Y = 0`, unconditionally.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.TraceBackground
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-! ### The statement -/

/-- **The conclusion of `thm:OT_ext_global`** for fixed `ω`, `(L, h)`, `(T, h_T)`, `θ`, `Y = W`
and `φ`: there is `k₀` such that for all `k ≥ k₀` every
`s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ 𝓘(k Tr_W^θ(φ)))` extends to some `s̃ ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`.
`Tr_W^θ(φ)` is `sourceTraceEnvelope`, for the (unique) proof that it is defined. -/
def OTExtGlobalAlong (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (θ : ClosedRealOneOneForm n X) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (φ : X → EReal) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∀ hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2) θ φ,
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ s : (y : W) → (twistedPower L T k).Fiber y,
    IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) (k : ℝ)
      (SGPT.Trace.sourceTraceEnvelope ωb
          (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) θ φ hdefined) s →
    ∃ s' : twistedSections L T k,
      s' ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ) ∧
      ∀ y : W, s' y = s y

variable (n X) in
/-- **`thm:OT_ext_global`** (`chapter_trace.tex` 527--532): on a compact Kähler manifold `X`, for
holomorphic line bundles `L`, `T` with smooth Hermitian metrics, `θ = c₁(L, h_L)`, every `φ` with
`θ_φ` a Kähler current, and every closed connected submanifold `Y` with `ν(φ, Y) = 0`, the
conclusion `OTExtGlobalAlong` holds. -/
def OTExtGlobalStatement : Prop :=
  ∀ (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∀ φ : X → EReal, IsKahlerCurrentPotential θ φ →
  ∀ (W : Set X) (m : ℕ) (hW : IsClosedConnectedSubmanifold n W m),
    sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0 →
    OTExtGlobalAlong ωb L T θ hW φ

/-- Under the hypotheses of `thm:OT_ext_global` the trace `Tr_W^θ(φ)` is defined (the observation
after `def:traceop2`), so `OTExtGlobalAlong` is not vacuous. -/
theorem hasPositiveSourceTraceAlong_of_hyps (ωb : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    SGPT.Trace.HasPositiveSourceTraceAlong ωb
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2) θ φ :=
    by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨δ, hδ, hφδ⟩ :=
    SGPT.PSH.GlobalL2.exists_isThetaPshPotential_sub_smul_of_kahlerCurrent ωb hφ
  exact SGPT.Trace.hasPositiveSourceTraceAlong_of_kahlerCurrent hk ωb ωb
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2)
    (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 ωb.form ωb.isKahler) hδ hφδ hν

/-! ### The trace is `𝓘`-below every stage of a quasi-equisingular approximation -/

/-- **`Tr_W^θ(φ) ≼_𝓘 Φ_q|_W`** for every stage `Φ_q` of every quasi-equisingular approximation
of `φ` (any background `θ'`, errors `ε`), and these restrictions are `β`-psh for a closed real
`(1,1)`-form `β` on `W` (in particular not identically `-∞`).
Source: proof of `thm:OT_ext_global`, "`Tr_Y^θ(φ) ⪯_P φ_j|_Y`, and `cor:PimpliesI`". -/
theorem iOrderOnManifold_traceEnvelope_stage (ωb : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) {θ' : ClosedRealOneOneForm n X} {ε : ℕ → ℝ}
    {Φ : ℕ → X → EReal} (hqea : IsQuasiEquisingularApproximation ωb θ' φ ε Φ) :
    let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    ∀ hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) (contMDiff_val hk hW.2.2) θ φ,
      ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback (contMDiff_val hk hW.2.2) θ).val
        (SGPT.Trace.sourceTraceEnvelope ωb
          (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
          (contMDiff_val hk hW.2.2) θ φ hdefined) ∧
      (∀ q, IOrderOnManifold (n := m)
        (SGPT.Trace.sourceTraceEnvelope ωb
          (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
          (contMDiff_val hk hW.2.2) θ φ hdefined) (fun y : W => Φ q y.1)) ∧
      ∀ q, ∃ β : ClosedRealOneOneForm m W, IsThetaPshPotential β.val (fun y : W => Φ q y.1) := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have : Nonempty W := ⟨⟨_, hW.2.1.nonempty.some_mem⟩⟩
  intro hdefined
  set ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb with hωW
  set hι := contMDiff_val hk hW.2.2 with hhι
  set θW := ClosedRealOneOneForm.pullback hι θ with hθW
  obtain ⟨htrace, hσ, -⟩ := Classical.choose_spec hdefined
  set σ := Classical.choose hdefined with hσdef
  have hτdef : SGPT.Trace.sourceTraceEnvelope ωb ωW hι θ φ hdefined =
      singularityEnvelope θW.val σ := rfl
  -- the envelope is `θ|_W`-psh and `𝓘`-below `σ`
  have hτpsh : IsThetaPshPotential θW.val (singularityEnvelope θW.val σ) :=
    FirstPass.singularityEnvelope_isThetaPshPotential θW.val θW.property.1 θW.property.2
      hσ.1.hasSmoothLocalPotentials σ hσ
  have hτσ : IOrderOnManifold (n := m) (singularityEnvelope θW.val σ) σ :=
    PositiveCurrentTraceMultiplier.iOrderOnManifold_of_le_singularityEnvelope_add
      θW.property.1 θW.property.2 hσ (C := 0) fun x => by rw [EReal.coe_zero, add_zero]
  -- an admissible background on `W` for which `σ` is psh
  obtain ⟨C₁, hC₁, hadm₁, -⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι ωb ωW θ' hqea.error_antitone
  obtain ⟨D, hD, hDsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωW (-θW)
  have hC₁semi : (C₁ • ωW.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul ωW.isSemipositive hC₁.le
  let β : KahlerBackground m W :=
    ⟨C₁ • ωW.form + D • ωW.form,
      NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive ωW hC₁semi hD⟩
  have hadm : IsAdmissibleTraceBackground hι ωb θ' ε β.form := by
    refine ⟨β.isKahler, fun j => ?_⟩
    have h1 := hadm₁.2 j
    have hsplit : β.form - ClosedRealOneOneForm.pullback hι (θ' + ε j • ωb.form) =
        (C₁ • ωW.form - ClosedRealOneOneForm.pullback hι (θ' + ε j • ωb.form)) + D • ωW.form := by
      change C₁ • ωW.form + D • ωW.form - _ = _
      abel
    change (β.form - ClosedRealOneOneForm.pullback hι (θ' + ε j • ωb.form)).val.IsSemipositive
    rw [hsplit]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add h1
      (KahlerDomination.isSemipositive_smul ωW.isSemipositive hD.le)
  have hσβ : IsThetaPshPotential β.form.val σ := by
    have hsemi : (β.form - θW).val.IsSemipositive := by
      have hsplit : β.form - θW = C₁ • ωW.form + (-θW + D • ωW.form) := by
        change C₁ • ωW.form + D • ωW.form - θW = _
        abel
      rw [hsplit]
      exact UniformPerturbedKahlerLowerBound.isSemipositive_add hC₁semi hDsemi
    have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive hσ hsemi
    rwa [add_sub_cancel] at h2
  -- the restricted stages converge to `σ` in `d_S`, hence dominate it
  obtain ⟨hv, hlim, -⟩ :=
    SGPT.Trace.isSourceTraceRepresentativeAlong_of_qea hk ωW hι htrace hqea β hadm hσβ
  let A : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y : W => Φ j y.1, hv j⟩
  have hanti : Antitone (fun j => (A j).val) := fun i j hij y => hqea.term_antitone y.1 hij
  refine ⟨?_, fun q => ?_, fun q => ?_⟩
  · rw [hτdef]
    exact hτpsh.1
  · rw [hτdef]
    exact hτσ.trans (GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
      (TraceRepresentativeStageGlobalPOrder.sourcePOrder_le_stage_of_antitone_native_limit
        ωW β.form (PluripolarCapacityDichotomy.isBigClass_kahler β) A ⟨σ, hσβ⟩ hanti hlim q))
  · exact ⟨β.form, hv q⟩

/-! ### The book's proof -/

/-- **`thm:OT_ext_global` from the existence part of `thm:OT_ext`** (the book's proof,
`chapter_trace.tex` 537--558).  If for every `δ > 0` the existence part of `thm:OT_ext` holds for
`(ωb, L, T, θ, W, δ)`, then `thm:OT_ext_global` holds for `(ωb, L, T, θ, W, φ)` whenever `θ_φ` is a
Kähler current. -/
theorem otExtGlobalAlong_of_existence (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (θ : ClosedRealOneOneForm n X)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (hOT : ∀ δ : ℝ, 0 < δ → OTExtMarginExistenceAlong ωb L T θ hW δ)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    OTExtGlobalAlong ωb L T θ hW φ := by
  obtain ⟨δ₀, hδ₀, hφδ₀⟩ :=
    SGPT.PSH.GlobalL2.exists_isThetaPshPotential_sub_smul_of_kahlerCurrent ωb hφ
  set δ : ℝ := δ₀ / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have hφ3 : IsThetaPshPotential (θ - (3 * δ) • ωb.form).val φ := by
    have : 3 * δ = δ₀ := by rw [hδdef]; ring
    rwa [this]
  obtain ⟨ε, Φ, hqea⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation ωb _ hφ3
  intro hdefined
  obtain ⟨hτpsh, hI, hβ⟩ := iOrderOnManifold_traceEnvelope_stage ωb hW hqea hdefined
  exact exists_extension_of_iOrder ωb L T θ hW hδ (hOT δ hδ) hqea hβ hτpsh hI

/-- **`thm:OT_ext_global` from its open analytic input**: the margin version of the existence part
of `thm:OT_ext` (`OTExtMarginExistenceStatement`) implies `thm:OT_ext_global`. -/
theorem otExtGlobalStatement_of_marginExistence (h : OTExtMarginExistenceStatement n X) :
    OTExtGlobalStatement n X := by
  intro ωb L T hL hT θ hθ φ hφ W m hW _hν
  exact otExtGlobalAlong_of_existence ωb L T θ hW
    (fun δ hδ => h ωb L T hL hT θ hθ W m hW δ hδ) hφ

/-- **`thm:OT_ext ⇒ thm:OT_ext_global`**: the book derives `thm:OT_ext_global` from `thm:OT_ext`
(it uses only the existence of extensions). -/
theorem otExtGlobalStatement_of_otExtStatement (h : OTExtStatement n X) :
    OTExtGlobalStatement n X :=
  otExtGlobalStatement_of_marginExistence (otExtMarginExistenceStatement_of_otExtStatement h)

/-- **`thm:OT_ext_global` when `dim Y = 0`**, unconditionally (from `otExtAlong_of_dim_zero`, the
uniform point extension of lane S62). -/
theorem otExtGlobalAlong_of_dim_zero (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    {W : Set X} (hW : IsClosedConnectedSubmanifold n W 0) :
    OTExtGlobalAlong ωb L T θ hW φ :=
  otExtGlobalAlong_of_existence ωb L T θ hW
    (fun _ hδ => OTExtExistenceAlong.margin
      (otExtExistenceAlong_of_dim_zero ωb L T hL hT θ hθ hW hδ)) hφ

end SGPT.Trace.OTExt
