import SGPT.Trace.OTExt2LocalGain
import SGPT.Trace.OTExt2NormalPole
import SGPT.Trace.TwistedL2OTExtStatement

/-!
# The remaining statements of FPT's proof of `thm:compact-submanifold-extension`

Blueprint `claude-ot-ext2.tex`, nodes `claude-ot-ext2:gluing-data`, `claude-ot-ext2:gluing`,
`claude-ot-ext2:residue`, `claude-ot-ext2:compact-submanifold-extension`.  Xia, *Foundations of
pluripotential theory*, q07, `lem:critical-gain-initial-gluing`,
`lem:gentle-weighted-normal-residue`, `thm:compact-submanifold-extension`.

These are **statements** (no result below is assumed anywhere as a hypothesis of a result
presented as proved; `GentleWeightedNormalResidueHypothesis` is the named hypothesis of the
resolution-dependent residue lemma).

* `IsCriticalGainGluing`: `G = ∑_i η_i F_i` is glued, by a finite family of compactly supported
  smooth cut-offs `η_i` with `∑ η_i = 1` near `Y`, from holomorphic sections `F_i` on open sets
  `U_i` with `F_i = f` on `Y ∩ U_i` and the critical gain
  `∫_{U_i} |F_i|²_{h₀} e^{-(1+κ)Φ} R_Y^{-q} (log R_Y)^{-2} < ∞`
  (FPT `eq:critical-local-extension-gain`): the data of `lem:critical-gain-initial-gluing`, and
  the class of `G` to which `lem:gentle-weighted-normal-residue` applies.
* `CriticalGainInitialGluingAlong ω Y R`: FPT `lem:critical-gain-initial-gluing` for the normal
  pole `R`: for every line bundle `V` with a smooth metric `h₀`, a psh metric `h₀ e^{-Φ}`
  (`Φ ∈ PSH(X, c₁(V, h₀))`) whose restriction to `Y` is defined and every holomorphic section
  `f` of `V|_Y` in `𝓘(Φ|_Y)`, there are `κ > 0` and a glued smooth `G` with `G|_Y = f`,
  `∂̄G|_Y = 0`, the strengthened initial norm `eq:strengthened-critical-initial-norm` and the
  decay `eq:critical-gluing-error-decay` (`|∂̄G|²_{ω,h₀}` is recorded by a pointwise bound `Dg`
  in every chart and frame, as in `TwistedL2CorrectionStatement`).
* `GentleWeightedNormalResidueHypothesis ω Y`: **the named hypothesis** (FPT
  `lem:gentle-weighted-normal-residue`, which needs an embedded principalization of the ideal of
  `Φ` on `Bl_Y X` adapted to the exceptional divisor, FPT `thm:marked-order-one-input` and
  `lem:smooth-divisor-discrepancy-margin`): there is a normal pole `R` of `Y` (FPT
  `lem:global-normal-pole`) and `C_Y` such that for gentle `Φ` (TN's
  `HasGentleAnalyticSingularitiesOfType`, the class produced by the gentle quasi-equisingular
  approximation; FPT's `def:gentle-analytic-singularities` asks for a smooth remainder on every
  log resolution) and every glued `G` as above,
  `limsup_{ε → 0+} ∫_{ε/2 ≤ R ≤ ε} |G|²_h R^{-q} dV ≤ C_Y ∫_Y |f|²_h dV_Y`.
  It is implied by FPT's two lemmas; the existential form over `R` (instead of FPT's "for `R_Y`
  as in `lem:global-normal-pole`") only weakens it.
* `CompactSubmanifoldExtensionAlong ω Y`: FPT `thm:compact-submanifold-extension`: constants
  `N, C > 0` (depending on `X, ω, Y`) such that every `f ∈ H⁰(Y, V|_Y)` with finite norm for a
  psh metric `h = h₀ e^{-φ}` with `c₁(V, h) ≥ N ω` (`φ ∈ PSH(X, c₁(V, h₀) - N ω)`), whose
  restriction to `Y` is defined, extends to `s ∈ H⁰(X, V)` with
  `∫_X |s|²_h dV ≤ C ∫_Y |f|²_h dV_Y`.  Volumes are the Kähler volumes of `ω` and `ω|_Y`
  (FPT's `ω^n/n!` changes `C` by a fixed factor); "`f` has finite norm" is
  `IsAlongMultiplierSection` (holomorphic coefficients in `𝓘(φ|_Y)`, i.e. locally finite norm,
  equivalent on the compact `Y`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-! ### Glued extensions -/

section Gluing

variable (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

open Classical in
/-- **`G` is glued from local extensions of `f` with critical gain** (the construction of FPT
`lem:critical-gain-initial-gluing`): `G = ∑_i η_i F_i` (each term extended by `0`) for finitely
many open `U_i`, sections `F_i` holomorphic on `U_i` with `F_i = f` on `Y ∩ U_i` and
`∫_{U_i} |F_i|² e^{-(1+κ)Φ} R^{-q} (log R)^{-2} dμ < ∞`, and smooth compactly supported cut-offs
`η_i` with `tsupp η_i ⊆ U_i` and `∑ η_i = 1` on an open neighbourhood of `Y`. -/
def IsCriticalGainGluing (μ : Measure X) (W : Set X) (q : ℕ) (R : X → ℝ) (Φ : X → EReal)
    (κ : ℝ) (f : (y : W) → V y) (G : (x : X) → V x) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (U : ι → Set X) (F : ι → (x : X) → V x) (η : ι → X → ℝ),
    (∀ i, IsOpen (U i)) ∧
    (∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V (F i) (U i)) ∧
    (∀ i, ∀ y : W, y.1 ∈ U i → F i y = f y) ∧
    (∀ i, ∫⁻ x in U i, ENNReal.ofReal (‖F i x‖ ^ 2) * multiplierWeight (1 + κ) (Φ x) *
      ENNReal.ofReal ((R x ^ q * Real.log (R x) ^ 2)⁻¹) ∂μ ≠ ⊤) ∧
    (∀ i, ChartSmooth (n := n) (η i)) ∧ (∀ i, HasCompactSupport (η i)) ∧
    (∀ i, tsupport (η i) ⊆ U i) ∧
    (∃ N : Set X, IsOpen N ∧ W ⊆ N ∧ ∀ x ∈ N, ∑ i, η i x = 1) ∧
    ∀ x, G x = ∑ i, (η i x : ℂ) • (if x ∈ U i then F i x else 0)

end Gluing

/-! ### The statements -/

section Statements

variable [CompactSpace X]

/-- **FPT `lem:critical-gain-initial-gluing`** for the normal pole `R` of `W` (statement).  For a
line bundle `V` with smooth metric `h₀` and own Chern form `θ_V`, a weight `Φ ∈ PSH(X, θ_V)` with
`Φ|_W ≢ -∞` and a holomorphic section `f` of `V|_W` with coefficients in `𝓘(Φ|_W)`, there are
`κ > 0`, a glued `G` (`IsCriticalGainGluing`), smooth on `X`, with `G|_W = f`, and a pointwise
bound `Dg ≥ 0` of `|∂̄G|²_{ω,h₀}` in every chart and frame, vanishing on `W`, with
`∫_X (|G|² + Dg) e^{-(1+κ)Φ} R^{-q} (log R)^{-2} dV < ∞` and
`∫_{R < ε} Dg e^{-Φ} R^{-q} dV → 0` as `ε → 0+`. -/
def CriticalGainInitialGluingAlong (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) (R : X → ℝ) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ Φ : X → EReal, IsThetaPshPotential θV.val Φ → (∃ y ∈ W, Φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => Φ y) f →
  ∃ κ : ℝ, 0 < κ ∧ ∃ (G : (x : X) → V.Fiber x) (Dg : X → ℝ),
    IsCriticalGainGluing (n := n) V.Fiber (IntegrationCurrent.kahlerVolume ωb) W (n - m) R Φ κ f G ∧
    IsSmoothSectionOn V G univ ∧ (∀ y : W, G y = f y) ∧
    (∀ x, 0 ≤ Dg x) ∧ (∀ x ∈ W, Dg x = 0) ∧
    (∀ (c : ComplexChart n X) (e : AtlasFrame V), ∀ z ∈ chartFrameDomain V c e,
      ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff V c e G) z v‖ ^ 2 * frameNormSq V e (c.val.symm z) ≤
          Dg (c.val.symm z) * kahlerQuad ωb c z v) ∧
    ∫⁻ x, ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) * (R x ^ (n - m) * Real.log (R x) ^ 2)⁻¹) *
      multiplierWeight (1 + κ) (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb) ≠ ⊤ ∧
    Tendsto (fun ε : ℝ => ∫⁻ x in {x | R x < ε}, ENNReal.ofReal (Dg x * (R x ^ (n - m))⁻¹) *
      multiplierWeight 1 (Φ x) ∂(IntegrationCurrent.kahlerVolume ωb)) (𝓝[>] 0) (𝓝 0)

/-- **Hypothesis: FPT `lem:gentle-weighted-normal-residue`** (proved in `SGPT.Trace.OTRes.gentleWeightedNormalResidueHypothesis`, without resolution).
For `m < n`: there are a normal pole `R` of `W` (FPT `lem:global-normal-pole`) and `C_Y > 0` such
that for every line bundle `V` with smooth metric `h₀`, every `Φ ∈ PSH(X, c₁(V, h₀))` with gentle
analytic singularities and `Φ|_W ≢ -∞`, every holomorphic section `f` of `V|_W` in `𝓘(Φ|_W)`, every
`κ > 0` and every `G` glued from `f` as in `lem:critical-gain-initial-gluing`,
`limsup_{ε → 0+} ∫_{ε/2 ≤ R ≤ ε} |G|² e^{-Φ} R^{-q} dV ≤ C_Y ∫_W |f|² e^{-Φ} dV_W`. -/
def GentleWeightedNormalResidueHypothesis (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  m < n → ∃ R : X → ℝ, IsGlobalNormalPole ωb W R ∧ ∃ CY : ℝ, 0 < CY ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ Φ : X → EReal, IsThetaPshPotential θV.val Φ →
    (∃ (c : ℚ) (𝔞 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) →
    (∃ y ∈ W, Φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => Φ y) f →
  ∀ κ : ℝ, 0 < κ → ∀ G : (x : X) → V.Fiber x,
    IsCriticalGainGluing (n := n) V.Fiber (IntegrationCurrent.kahlerVolume ωb) W (n - m) R Φ κ f G →
    limsup (fun ε : ℝ => ∫⁻ x in {x | ε / 2 ≤ R x ∧ R x ≤ ε},
        ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ (n - m))⁻¹) * multiplierWeight 1 (Φ x)
          ∂(IntegrationCurrent.kahlerVolume ωb)) (𝓝[>] 0) ≤
      ENNReal.ofReal CY * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb))

/-- **FPT `thm:compact-submanifold-extension`** for the closed connected submanifold `W`
(statement): there are `N, C > 0` such that for every line bundle `V` with smooth metric `h₀`,
own Chern form `θ_V` and every `φ ∈ PSH(X, θ_V - N ω)` (`c₁(V, h₀ e^{-φ}) ≥ N ω`) with
`φ|_W ≢ -∞`, every holomorphic section `f` of `V|_W` with coefficients in `𝓘(φ|_W)` extends to
`s ∈ H⁰(X, V)` with `∫_X |s|²_{h₀} e^{-φ} dV ≤ C ∫_W |f|²_{h₀} e^{-φ} dV_W`. -/
def CompactSubmanifoldExtensionAlong (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ N C : ℝ, 0 < N ∧ 0 < C ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ φ : X → EReal, IsThetaPshPotential (θV - N • ωb.form).val φ → (∃ y ∈ W, φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => φ y) f →
  ∃ s : HolomorphicSections (n := n) V.Fiber, (∀ y : W, s y = f y) ∧
    ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight 1 (φ x)
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤
      ENNReal.ofReal C * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb))

end Statements

end SGPT.Trace.OTExt2
