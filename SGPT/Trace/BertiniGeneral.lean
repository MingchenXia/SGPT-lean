import SGPT.Trace.BertiniGeneralTrace
import SGPT.Trace.BertiniRestriction
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition

/-!
# Restrictions to general members of a linear system

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems": `lma:posmasscurrres`,
`prop:varphiP_rest_gen`, `lma:Igoodrest`, `cor:tracegeneralwelldef`,
`cor:rest_gen_very_good` (blueprint `claude-bertini.tex`, Subsection "Corollaries on general
members", and `claude-bertini-d.tex`).

Setting (`SGPT.Trace.Bertini`): `X` is a compact connected complex manifold of dimension `n` with
a Kähler form `ω` (a connected projective manifold in the book), `p : X → ℙᴺ` is holomorphic and
`Λ = |𝒪_{ℙᴺ}(1)| = HyperplaneSpace N`; the members are `H = p⁻¹(H_ℓ)` (`member p ℓ`). "Quasi-every
`H ∈ Λ`" means: for `ℓ` outside a pluripolar subset of `Λ` (`def:pluripolarsets`,
`VariableComplexAtlas.CoPluripolar`). For a connected smooth member `H`
(`IsConnectedSmoothMember`), `H` is a compact connected submanifold of dimension `n - 1`
(`isClosedConnectedSubmanifold_member`) with its own complex structure
(`SubmanifoldChartedSpace`); restrictions are compositions with the inclusion, `θ|_H` is the
pullback, and traces along `H` are `IsNaturalSourceTraceRepresentative` (`def:traceop` with the
natural geometry of `H`).

Hypotheses. The linear system is base-point free: `p` is nondegenerate (`IsNondegenerate p`, the
morphism of a base-point-free linear system) and `N ≥ 1`. The book also assumes, before
`cor:qpshgeneralres`, that the set of connected smooth members is co-pluripolar; we assume the
weaker `hconn`: `{ℓ | p⁻¹(H_ℓ) connected}` is co-pluripolar (smoothness of quasi-every member is
proved by package B). `cor:qpshgeneralres` (package C,
`SGPT.Trace.Bertini.coPluripolar_restriction_strong`) enters through
`qpshGeneralRestriction`.

Main results (the book assumes `n ≥ 2`; we need at most `n ≠ 0`):

* `coPluripolar_restrictionHasPositiveMass` (**`lma:posmasscurrres`**);
* `coPluripolar_restrictionPOrder` (**`prop:varphiP_rest_gen`**);
* `coPluripolar_restrictionTendsto` (**`lma:Igoodrest`**);
* `coPluripolar_hasPositiveVolumeNaturalTrace` (**`cor:tracegeneralwelldef`**);
* `coPluripolar_isVeryGoodRestriction`, `coPluripolar_isVeryGoodRestriction_positive`
  (**`cor:rest_gen_very_good`**, including the final assertion).

The route for the last two differs from the book's (which uses `cor:ABTfortrace`, hence the
multiplier-ideal clause of `thm:Bert`): both follow from `lma:Igoodrest` applied to a
quasi-equisingular approximation of an `𝓘`-good potential.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.BertiniGeneral

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
  SGPT.PSH.VariableComplexAtlas

/-! ### Restrictions to a closed connected submanifold -/

section Submanifold

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {W : Set X}

/-- `φ|_W ∈ PSH(W, θ|_W)_{>0}`: the restriction of `φ` to the closed connected submanifold `W`
(with its own complex structure) is a `θ|_W`-psh potential, in particular `φ|_W ≢ -∞`, and
`∫_W (θ|_W + dd^c φ|_W)^{dim W} > 0`. -/
def RestrictionHasPositiveMass (hW : IsClosedConnectedSubmanifold n W k)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  ∃ hφ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ).val
      (fun y : W => φ y),
    HasPositivePotentialMass
      (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ)
      (fun y : W => φ y) hφ

/-- `φ|_W ⪯_P ψ|_W` on the closed connected submanifold `W` (`SourcePOrder`, the book's
`⪯_P` between quasi-psh functions: both are potentials of positive mass in a common background
and their envelopes compare). -/
def RestrictionPOrder (hW : IsClosedConnectedSubmanifold n W k) (φ ψ : X → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  SourcePOrder (n := k) (fun y : W => φ y) (fun y : W => ψ y)

/-- `φ_j|_W, φ|_W ∈ PSH(W, θ|_W)` (in particular not identically `-∞`) and `φ_j|_W → φ|_W` in
`d_S` (for every big background on `W` containing them, `TendstoSingularityType`). -/
def RestrictionTendsto (omega : KahlerBackground n X) (hW : IsClosedConnectedSubmanifold n W k)
    (θ : ClosedRealOneOneForm n X) (φs : ℕ → X → EReal) (φ : X → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  (∀ j, IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ).val
      (fun y : W => φs j y)) ∧
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ).val
      (fun y : W => φ y) ∧
    TendstoSingularityType (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
      (fun j (y : W) => φs j y) (fun y : W => φ y)

/-- `Tr^θ_W(φ)` is defined (`def:traceop2`, with the natural geometry of `W`): some trace
operator of `φ` along `W` lies in `PSH(W, θ|_W)_{>0}`. -/
def HasPositiveNaturalTrace (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) :
    Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  HasPositiveSourceTraceAlong omega (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
    (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ

/-- `Tr^θ_W(φ)` is defined and has positive volume: it is defined, its mass
`∫_W (θ|_W + dd^c Tr^θ_W(φ))^{dim W}` is positive, and so is its volume
`vol(θ|_W, Tr^θ_W(φ))` (`def:volqpsh`). -/
def HasPositiveVolumeNaturalTrace (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) :
    Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  ∃ hdef : HasPositiveSourceTraceAlong omega
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
      (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ,
    0 < sourceTraceMass omega (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
      (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ ∧
    0 < iVolume (ClosedRealOneOneForm.pullback (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ)
      (isThetaPshPotential_sourceTraceEnvelope omega
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
        (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ hdef).1.hasSmoothLocalPotentials
      (sourceTraceEnvelope omega (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
        (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ hdef)
      (isThetaPshPotential_sourceTraceEnvelope omega
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega)
        (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) θ φ hdef)

/-- Items (ii)-(iv) of `cor:rest_gen_very_good` on `W`: `φ|_W` is `𝓘`-good, `ν(φ, W) = 0`, and
`Tr_W φ ∼_P φ|_W`: `φ|_W` is itself a trace operator of `φ` along `W`, and every trace operator
(for every auxiliary Kähler form `ω'` of the approximation) is `P`-equivalent to `φ|_W`. -/
def IsVeryGoodRestriction (omega : KahlerBackground n X) (hW : IsClosedConnectedSubmanifold n W k)
    (φ : X → EReal) : Prop :=
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  IGood (n := k) (fun y : W => φ y) ∧
    sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0 ∧
    IsNaturalSourceTraceRepresentative omega hW φ (fun y : W => φ y) ∧
    ∀ (omega' : KahlerBackground n X) (τ : W → EReal),
      IsNaturalSourceTraceRepresentative omega' hW φ τ →
        SourcePEquivalent (n := k) τ (fun y : W => φ y)

/-! #### The single-member statements -/

/-- `lma:posmasscurrres` on one submanifold. -/
theorem restrictionHasPositiveMass_of_le (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {δ : ℝ}
    (hδ : 0 < δ) {φ s : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hs : IsThetaPshPotential (θ - δ • omega.form).val s) (hsφ : s ≤ φ)
    (hne : ∃ x ∈ W, s x ≠ ⊥) : RestrictionHasPositiveMass hW θ φ := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  have : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨x, hx, hsx⟩ := hne
  exact hasPositivePotentialMass_comp_of_le (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) omega
    (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 omega.form omega.isKahler) hδ hφ hs
    hsφ ⟨⟨x, hx⟩, hsx⟩

/-- `prop:varphiP_rest_gen` on one submanifold. -/
theorem restrictionPOrder_of_barriers [MeasurableSpace X] [BorelSpace X]
    (omega : KahlerBackground n X) (hW : IsClosedConnectedSubmanifold n W k)
    {θ : ClosedRealOneOneForm n X} {φ ψ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) (hP : FirstPass.POrder.POrderWith θ φ ψ)
    {e : ℕ → X → EReal} (he : ∀ m, IsThetaPshPotential θ.val (e m))
    (hbar : ∀ m : ℕ, ThetaPshConvexCombination.convexComb (1 - ((m : ℝ) + 2)⁻¹)
      (singularityEnvelope θ.val ψ) (e m) ≤ ψ)
    (hφne : ∃ x ∈ W, φ x ≠ ⊥) (hψne : ∃ x ∈ W, ψ x ≠ ⊥) (hene : ∀ m, ∃ x ∈ W, e m x ≠ ⊥) :
    RestrictionPOrder hW φ ψ := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  have : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hsub {u : X → EReal} (h : ∃ x ∈ W, u x ≠ ⊥) : ∃ y : W, u y ≠ ⊥ := by
    obtain ⟨x, hx, hux⟩ := h
    exact ⟨⟨x, hx⟩, hux⟩
  exact sourcePOrder_comp_of_barriers (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) omega
    (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 omega.form omega.isKahler) hφ hψ hP
    he hbar (hsub hφne) (hsub hψne) fun m => hsub (hene m)

/-- `lma:Igoodrest` on one submanifold. -/
theorem restrictionTendsto_of_barriers (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X}
    {φs : ℕ → X → EReal} {φ : X → EReal}
    (hφs : ∀ j, IsThetaPshPotential θ.val (φs j)) (hφ : IsThetaPshPotential θ.val φ)
    (hle : ∀ j, φ ≤ φs j) (hanti : ∀ x, Antitone fun j => φs j x)
    {η : ℕ → X → EReal} (hη : ∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m))
    (hbar : ∀ m : ℕ, ∃ j, ThetaPshConvexCombination.convexComb (1 - ((m : ℝ) + 2)⁻¹) (φs j)
      (η m) ≤ φ)
    (hne : ∃ x ∈ W, φ x ≠ ⊥) (hηne : ∀ m, ∃ x ∈ W, η m x ≠ ⊥) :
    RestrictionTendsto omega hW θ φs φ := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  have : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hsub {u : X → EReal} (h : ∃ x ∈ W, u x ≠ ⊥) : ∃ y : W, u y ≠ ⊥ := by
    obtain ⟨x, hx, hux⟩ := h
    exact ⟨⟨x, hx⟩, hux⟩
  exact tendstoSingularityType_comp_of_barriers (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2)
    omega (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 omega.form omega.isKahler)
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega) hφs hφ hle hanti hη hbar
    (hsub hne) fun m => hsub (hηne m)

/-- `cor:rest_gen_very_good` (ii)-(iv) on one submanifold. -/
theorem isVeryGoodRestriction_of_data (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {u : X → EReal}
    {ε : ℕ → ℝ} {U η : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j))
    (hη : ∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m))
    (hbar : ∀ m : ℕ, ∃ j, ThetaPshConvexCombination.convexComb (1 - ((m : ℝ) + 2)⁻¹) (U j)
      (η m) ≤ u)
    (hne : ∃ x ∈ W, u x ≠ ⊥) (hηne : ∀ m, ∃ x ∈ W, η m x ≠ ⊥) :
    IsVeryGoodRestriction omega hW u := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  have : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hsub {v : X → EReal} (h : ∃ x ∈ W, v x ≠ ⊥) : ∃ y : W, v y ≠ ⊥ := by
    obtain ⟨x, hx, hvx⟩ := h
    exact ⟨⟨x, hx⟩, hvx⟩
  have htrace : IsNaturalSourceTraceRepresentative omega hW u (fun y : W => u y) :=
    isSourceTraceRepresentativeAlong_comp_of_iGood_data
      (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) hn omega
      (SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 omega.form omega.isKahler)
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega) happ hU hη hbar (hsub hne)
      fun m => hsub (hηne m)
  obtain ⟨hgood, hgen, hall⟩ :=
    restriction_properties_of_trace (SubmanifoldChartedSpace.contMDiff_val hk hW.2.2) hk htrace
  exact ⟨hgood, hgen, htrace, fun omega' τ hτ => hall omega' _ τ hτ⟩

/-- The final assertion of `cor:rest_gen_very_good` on one submanifold: if `φ|_W` is a trace
operator and `φ|_W ∈ PSH(W, θ|_W)_{>0}`, then `Tr_W(φ)` has a representative in
`PSH(W, θ|_W)_{>0}`. -/
theorem hasPositiveNaturalTrace_of (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hvg : IsVeryGoodRestriction omega hW φ) (hpos : RestrictionHasPositiveMass hW θ φ) :
    HasPositiveNaturalTrace omega hW θ φ := by
  obtain ⟨-, -, htrace, -⟩ := hvg
  obtain ⟨hφV, hposV⟩ := hpos
  exact ⟨_, htrace, hφV, hposV⟩

/-- `cor:tracegeneralwelldef` on one submanifold: if `φ|_W ≢ -∞` and `ψ = P_θ[φ]_𝓘` has a very
good restriction with `ψ|_W ∈ PSH(W, θ|_W)_{>0}`, then `Tr^θ_W(φ)` is defined and has positive
mass and volume. -/
theorem hasPositiveVolumeNaturalTrace_of (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ x ∈ W, φ x ≠ ⊥)
    (hvg : IsVeryGoodRestriction omega hW (iSingularityEnvelope θ.val φ))
    (hpos : RestrictionHasPositiveMass hW θ (iSingularityEnvelope θ.val φ)) :
    HasPositiveVolumeNaturalTrace omega hW θ φ := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  have : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  let omegaW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  obtain ⟨-, -, htrψ, -⟩ := hvg
  obtain ⟨hψV, hψpos⟩ := hpos
  obtain ⟨x, hx, hφx⟩ := hne
  obtain ⟨-, hdef⟩ := hasPositiveSourceTraceAlong_of_iEnvelope_trace hι hk hn omega omegaW hφ
    ⟨⟨x, hx⟩, hφx⟩ htrψ hψV hψpos
  have hmass := (hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos hk omega omegaW hι θ φ).mp hdef
  refine ⟨hdef, hmass, ?_⟩
  have hE := isThetaPshPotential_sourceTraceEnvelope omega omegaW hι θ φ hdef
  have hmassE : sourceTraceMass omega omegaW hι θ φ =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (sourceTraceEnvelope omega omegaW hι θ φ hdef) hE := by
    simp only [sourceTraceMass, dif_pos hdef]
  rw [hmassE] at hmass
  refine hmass.trans_le ?_
  exact diagonalPotentialMass_mono_of_kahler omegaW hE _
    (moreSingularOn_iSingularityEnvelope hE)

end Submanifold

/-! ### Co-pluripolar sets -/

section CoPluripolar

variable {Y : Type*} [TopologicalSpace Y] {A : SGPT.PSH.VariableComplexAtlas Y}

/-- Supersets of co-pluripolar sets are co-pluripolar. -/
theorem coPluripolar_mono {S T : Set Y} (hS : A.CoPluripolar S) (hST : S ⊆ T) :
    A.CoPluripolar T :=
  LocallyPluripolar.mono hS (compl_subset_compl.mpr hST)

/-- Countable intersections of co-pluripolar sets are co-pluripolar (`prop:pluripolarunion`). -/
theorem coPluripolar_iInter {S : ℕ → Set Y} (hS : ∀ j, A.CoPluripolar (S j)) :
    A.CoPluripolar (⋂ j, S j) := by
  have h := LocallyPluripolar.iUnion hS
  unfold CoPluripolar
  rwa [compl_iInter]

/-- Finite intersections of co-pluripolar sets are co-pluripolar. -/
theorem coPluripolar_inter {S T : Set Y} (hS : A.CoPluripolar S) (hT : A.CoPluripolar T) :
    A.CoPluripolar (S ∩ T) := by
  let F : ℕ → Set Y := fun j => if j = 0 then S else T
  have h := coPluripolar_iInter (A := A) (S := F) fun j => by
    by_cases hj : j = 0
    · simp only [F, if_pos hj]
      exact hS
    · simp only [F, if_neg hj]
      exact hT
  refine coPluripolar_mono h fun x hx => ?_
  have h0 := mem_iInter.mp hx 0
  have h1 := mem_iInter.mp hx 1
  simp only [F, if_pos rfl] at h0
  simp only [F, one_ne_zero, if_false] at h1
  exact ⟨h0, h1⟩

end CoPluripolar

/-! ### General members of the linear system -/

section Bertini

open SGPT.Trace.Bertini SGPT.Projective

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] (p : X → ComplexProjectiveSpace N)

variable (n) in
/-- `H_ℓ ∩ X = p⁻¹(H_ℓ)` is a connected smooth hypersurface (the book's "`H` is connected and
smooth"). -/
def IsConnectedSmoothMember (l : HyperplaneSpace N) : Prop :=
  IsSmoothHypersurfaceMember n p l ∧ IsConnected (member p l)

omit [CompactSpace X] in
/-- A connected smooth member is a closed connected submanifold of dimension `n - 1`. -/
theorem isClosedConnectedSubmanifold_member
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {l : HyperplaneSpace N}
    (h : IsConnectedSmoothMember n p l) : IsClosedConnectedSubmanifold n (member p l) (n - 1) :=
  ⟨isClosed_member p hp.continuous l, h.2, fun _ hx => regularAtDim_member p hp h.1 hx⟩

omit [CompactSpace X] in
/-- A `θ`-psh potential is quasi-psh in the sense of `def:qpsh`. -/
theorem isQPSH_of_isThetaPshPotential {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) : (ofFixedModel n X).IsQPSH φ := by
  refine ⟨nativeClosedFormToAtlas θ, (isThetaPSH_iff_nativeThetaPotential _ φ).mpr ?_⟩
  have hinv : atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
    rcases θ with ⟨θ, hθ⟩
    cases θ
    rfl
  rwa [hinv]

variable (n) in
/-- **The conclusion of `cor:qpshgeneralres`** in the form used below: for every quasi-psh `φ`
(`φ ∈ PSH(X, θ)` for some `θ`), for quasi-every `ℓ ∈ Λ` the member `p⁻¹(H_ℓ)` is a smooth
hypersurface and `φ|_{p⁻¹(H_ℓ)} ≢ -∞`. It holds for nondegenerate `p`
(`qpshGeneralRestriction`, from package C). -/
def QPSHGeneralRestriction : Prop :=
  ∀ (θ : ClosedRealOneOneForm n X) (φ : X → EReal), IsThetaPshPotential θ.val φ →
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsSmoothHypersurfaceMember n p l ∧ ∃ x ∈ member p l, φ x ≠ ⊥}

/-- **`cor:qpshgeneralres`** (`SGPT.Trace.Bertini.coPluripolar_restriction_strong`, package C):
for a base-point-free linear system (`p` nondegenerate, `N ≥ 1`), `QPSHGeneralRestriction` holds. -/
theorem qpshGeneralRestriction [ConnectedSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hnd : IsNondegenerate p)
    (hN : 1 ≤ N) : QPSHGeneralRestriction n p := by
  intro θ φ hφ
  refine LocallyPluripolar.mono
    (coPluripolar_restriction_strong p hp hnd hN (isQPSH_of_isThetaPshPotential hφ)) ?_
  refine compl_subset_compl.mpr fun l hl => ⟨hl.1, ?_⟩
  obtain ⟨y, hy, hφy⟩ := hl.2.2 univ isOpen_univ (by simpa using hl.2.1)
  exact ⟨y, hy.2, hφy⟩

variable (n) in
/-- The `ℓ` such that `p⁻¹(H_ℓ)` is a connected smooth member on which `φ ≢ -∞`. -/
def generalPositionSet (φ : X → EReal) : Set (HyperplaneSpace N) :=
  {l | IsConnectedSmoothMember n p l ∧ ∃ x ∈ member p l, φ x ≠ ⊥}

omit [CompactSpace X] in
/-- Under `cor:qpshgeneralres` and the connectedness hypothesis, every quasi-psh `φ` is in
general position with respect to quasi-every member. -/
theorem coPluripolar_generalPositionSet (hres : QPSHGeneralRestriction n p)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar (generalPositionSet n p φ) :=
  coPluripolar_mono (coPluripolar_inter (hres θ φ hφ) hconn) fun _ hl =>
    ⟨⟨hl.1.1, hl.2⟩, hl.1.2⟩

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)

/-- **Source `lma:posmasscurrres`.** Let `T = θ + dd^c φ` be a closed positive `(1,1)`-current
on `X` with `∫_X T^n > 0` (`φ ∈ PSH(X,θ)_{>0}`). Then quasi-every `H ∈ Λ` is connected and
smooth, `T|_H = θ|_H + dd^c φ|_H` is well defined (`φ|_H ≢ -∞`) and `∫_H T|_H^{n-1} > 0`. -/
theorem coPluripolar_restrictionHasPositiveMass (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hpos : HasPositivePotentialMass θ φ hφ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        RestrictionHasPositiveMass (isClosedConnectedSubmanifold_member p hp h) θ φ} := by
  obtain ⟨δ, hδ, s, hs, hsφ⟩ := exists_kahlerCurrent_le (Nat.pos_of_ne_zero hn) omega hφ hpos
  refine coPluripolar_mono (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn hs) fun l hl => ?_
  obtain ⟨h, hx⟩ := hl
  exact ⟨h, restrictionHasPositiveMass_of_le omega _ hδ hφ hs hsφ hx⟩

/-- **Source `prop:varphiP_rest_gen`.** Let `φ, ψ ∈ QPSH(X)` with `φ ⪯_P ψ`. Then quasi-every
`H ∈ Λ` is connected and smooth, and `φ|_H ⪯_P ψ|_H`. -/
theorem coPluripolar_restrictionPOrder (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {φ ψ : X → EReal} (hφψ : SourcePOrder (n := n) φ ψ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        RestrictionPOrder (isClosedConnectedSubmanifold_member p hp h) φ ψ} := by
  obtain ⟨θ, hφ, hψ, -, hψpos, hP⟩ := hφψ
  obtain ⟨e, he, hbar⟩ := exists_envelope_barriers omega θ hψ hψpos
  have hG := coPluripolar_inter (coPluripolar_inter
    (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn hφ)
    (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn hψ))
    (coPluripolar_iInter fun m => coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn (he m))
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨⟨⟨h, hφx⟩, ⟨-, hψx⟩⟩, hem⟩ := hl
  rw [mem_iInter] at hem
  exact ⟨h, restrictionPOrder_of_barriers omega _ hφ hψ hP he hbar hφx hψx
    fun m => (hem m).2⟩

/-- **Source `lma:Igoodrest`.** Let `θ` represent a big class, `(φ_j)` a decreasing sequence in
`PSH(X,θ)` and `φ ∈ PSH(X,θ)` with `φ ≤ φ_j` and `φ_j → φ` in `d_S`. Then quasi-every
`H ∈ Λ` is connected and smooth, `φ_j|_H ≢ -∞`, `φ|_H ≢ -∞` (indeed all lie in
`PSH(H, θ|_H)`) and `φ_j|_H → φ|_H` in `d_S`. -/
theorem coPluripolar_restrictionTendsto (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {φs : ℕ → X → EReal} {φ : X → EReal}
    (hφs : ∀ j, IsThetaPshPotential θ.val (φs j)) (hφ : IsThetaPshPotential θ.val φ)
    (hanti : ∀ x, Antitone fun j => φs j x) (hle : ∀ j, φ ≤ φs j)
    (hlim : Tendsto (fun j => (⟨φs j, hφs j⟩ : ThetaPshL1Topology.ThetaPshL1 θ.val)) atTop
      (@nhds (ThetaPshL1Topology.ThetaPshL1 θ.val)
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega θ
          hbig).toUniformSpace.toTopologicalSpace ⟨φ, hφ⟩)) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        RestrictionTendsto omega (isClosedConnectedSubmanifold_member p hp h) θ φs φ} := by
  obtain ⟨η, hη, hbar⟩ := exists_barriers_of_tendsto omega θ hbig hφs hφ hle hlim
  have hG := coPluripolar_inter (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn hφ)
    (coPluripolar_iInter fun m => coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn (hη m))
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨⟨h, hx⟩, hηm⟩ := hl
  rw [mem_iInter] at hηm
  exact ⟨h, restrictionTendsto_of_barriers omega _ hφs hφ hle hanti hη hbar hx
    fun m => (hηm m).2⟩

/-- **Source `cor:rest_gen_very_good`, items (i)-(iv).** Let `φ ∈ QPSH(X)` be `𝓘`-good. Then
quasi-every `H ∈ Λ` satisfies: (i) `H` is connected and smooth; (ii) `φ|_H` is `𝓘`-good;
(iii) `ν(φ, H) = 0`; (iv) `Tr_H φ ∼_P φ|_H`. -/
theorem coPluripolar_isVeryGoodRestriction (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {φ : X → EReal} (hgood : IGood (n := n) φ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsVeryGoodRestriction omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  obtain ⟨θ, ε, U, η, happ, hU, hη, hbar⟩ := exists_iGood_trace_data omega hgood
  have hG := coPluripolar_inter (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn happ.target)
    (coPluripolar_iInter fun m => coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn (hη m))
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨⟨h, hx⟩, hηm⟩ := hl
  rw [mem_iInter] at hηm
  exact ⟨h, isVeryGoodRestriction_of_data hn omega _ happ hU hη hbar hx fun m => (hηm m).2⟩

/-- **Source `cor:rest_gen_very_good`, with the final assertion.** Let `φ ∈ QPSH(X)` be
`𝓘`-good and `θ` a closed real `(1,1)`-form with `φ ∈ PSH(X,θ)_{>0}`. Then on a co-pluripolar
set of `H ∈ Λ`, (i)-(iv) hold and moreover `Tr_H(φ)` has a representative in
`PSH(H, θ|_H)_{>0}` (namely `φ|_H`). -/
theorem coPluripolar_isVeryGoodRestriction_positive (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {φ : X → EReal} (hgood : IGood (n := n) φ) {θ : ClosedRealOneOneForm n X}
    (hφ : IsThetaPshPotential θ.val φ) (hpos : HasPositivePotentialMass θ φ hφ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsVeryGoodRestriction omega (isClosedConnectedSubmanifold_member p hp h) φ ∧
        RestrictionHasPositiveMass (isClosedConnectedSubmanifold_member p hp h) θ φ ∧
        HasPositiveNaturalTrace omega (isClosedConnectedSubmanifold_member p hp h) θ φ} := by
  have hG := coPluripolar_inter (coPluripolar_isVeryGoodRestriction p hp hn omega hnd hN hconn hgood)
    (coPluripolar_restrictionHasPositiveMass p hp hn omega hnd hN hconn hφ hpos)
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨⟨h, hvg⟩, ⟨_h, hpm⟩⟩ := hl
  exact ⟨h, hvg, hpm, hasPositiveNaturalTrace_of omega _ hvg hpm⟩

/-- **Source `cor:tracegeneralwelldef`.** Let `T = θ + dd^c φ` be a closed positive
`(1,1)`-current with `vol T > 0` (`vol(θ, φ) = ∫_X (θ + dd^c P_θ[φ]_𝓘)^n`, `def:volqpsh`).
Then quasi-every `H ∈ Λ` is connected and smooth, and `Tr^{θ|_H}_H(T) = Tr^θ_H(φ)` is
well defined and has positive volume. -/
theorem coPluripolar_hasPositiveVolumeNaturalTrace (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hvol : 0 < iVolume θ hφ.1.hasSmoothLocalPotentials φ hφ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        HasPositiveVolumeNaturalTrace omega (isClosedConnectedSubmanifold_member p hp h) θ φ} := by
  have hψ : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val φ) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hφ.1.hasSmoothLocalPotentials φ hφ
  have hψpos : HasPositivePotentialMass θ (iSingularityEnvelope θ.val φ) hψ := hvol
  have hgood : IGood (n := n) (iSingularityEnvelope θ.val φ) := by
    refine ⟨θ, hψ, hψpos, ?_⟩
    have h := (originalIEnvelope_positive_iGood omega θ _ hψ hψpos).2
    rwa [iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2
      hφ.1.hasSmoothLocalPotentials φ hφ] at h
  have hG := coPluripolar_inter
    (coPluripolar_isVeryGoodRestriction_positive p hp hn omega hnd hN hconn hgood hψ hψpos)
    (coPluripolar_generalPositionSet p (qpshGeneralRestriction p hp hnd hN) hconn hφ)
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨⟨h, hvg, hpm, -⟩, ⟨-, hx⟩⟩ := hl
  exact ⟨h, hasPositiveVolumeNaturalTrace_of hn omega _ hφ hx hvg hpm⟩

end Bertini

end SGPT.Trace.BertiniGeneral
