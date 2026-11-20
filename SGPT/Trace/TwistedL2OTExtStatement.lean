import SGPT.PSH.GlobalL2PointMain
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# The Ohsawa--Takegoshi extension theorem `thm:OT_ext`: statement and the point case

Blueprint `claude-ot-ext.tex`, nodes `claude-ot-ext:along-sections`, `claude-ot-ext:statement`,
`claude-ot-ext:point-case`.  Source `thm:OT_ext` (`chapter_pshfunctions.tex` 1930--1941):

> Assume that `L` is big and `T` is a holomorphic line bundle on `X`. Fix a Hermitian metric `h_T`
> on `T`, a Hermitian metric `h` on `L` and let `θ = c₁(L,h)`. Take a Kähler form `ω` on `X`. Let
> `Y ⊆ X` be a connected closed submanifold of dimension `m`. Suppose that
> `φ ∈ PSH(X, θ - δω)` for some `δ > 0` and `φ|_Y ≢ -∞`. Then there exists `k₀(δ, h_T) > 0` such
> that for all `k ≥ k₀` and `s ∈ H⁰(Y, T ⊗ L|_Y^k ⊗ I(kφ|_Y))`, there exists an extension
> `s̃ ∈ H⁰(X, T ⊗ L^k ⊗ I(kφ))` such that
> `∫_X |s̃|²_{h^k ⊗ h_T} e^{-kφ} ω^n ≤ C ∫_Y |s|²_{(h^k ⊗ h_T)|_Y} e^{-kφ|_Y} ω|_Y^m`,
> where `C > 0` is an absolute constant, independent of the data `(φ, s, k)`.

## Formalization

* `Y` is a closed connected complex submanifold `W ⊆ X` of dimension `m`
  (`IsClosedConnectedSubmanifold n W m`), with the complex structure of TN's
  `SubmanifoldChartedSpace` and the Kähler form `ω|_W` of `SubmanifoldKahlerRestriction`; `ω|_Y^m`
  is the Kähler volume of `ω|_W` (`ω^n` is `kahlerVolume ω`, as in `bergmanSeq`).
* A section of `(L^k ⊗ T)|_Y` is a function `s : (y : W) → (L^k ⊗ T)_y`; its coefficient in a
  frame `e` is `alongCoefficient`.  `s ∈ H⁰(Y, T ⊗ L|_Y^k ⊗ I(kφ|_Y))` is
  `IsAlongMultiplierSection`: at every `y ∈ W` the coefficient in the preferred frame at `y` is a
  holomorphic germ of `W` lying in the multiplier ideal `I(kφ|_W)` of `W` (the book's sheaf
  `𝒪_Y(T ⊗ L^k) ⊗ I(kφ|_Y)`; the convention of `fullHolomorphicIdealSections` on `X`).
* `H⁰(X, T ⊗ L^k ⊗ I(kφ))` is `fullHolomorphicIdealSections (L^k ⊗ T) (sourceDegreeMultiplierIdeal k φ)`
  (the Bergman chapter's literal space), `s̃|_Y = s` is `∀ y : W, s̃ y = s y`.
* Bigness of `L` is not assumed: it follows from the existence of `φ ∈ PSH(X, θ - δω)`, and
  without such `φ` the statement is vacuous.
* `OTExtAlong ω L T θ hW δ`: the conclusion for fixed data; `OTExtStatement n X`: the theorem.

## Results

* `otExtAlong_of_dim_zero`: the theorem for `dim Y = 0` (then `Y` is a point, and the statement is
  the uniform point extension `SGPT.PSH.GlobalL2.globalPointExtension` of lane S62, FPT
  `thm:compact-point-extension`).
* `eq_of_mem_of_dim_zero`: a closed connected submanifold of dimension `0` is a point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)

/-! ### Sections along a submanifold -/

section Along

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- The coefficient, in the frame `e`, of a section `s` of `V|_W` along a subset `W`:
`y ↦ (e (y, s y)).2` (meaningful on `W ∩ e.baseSet`). -/
def alongCoefficient (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) {W : Set X}
    (s : (y : W) → V y) : W → ℂ :=
  fun y => (e ⟨y.val, s y⟩).2

/-- **`s ∈ H⁰(W, V|_W ⊗ I(c u))`** for a complex structure on the submanifold `W` and a function
`u` on `W`: at every `y ∈ W` the coefficient of `s` in the preferred frame of `V` at `y` is a
holomorphic germ of `W` at `y` lying in the multiplier ideal `I(c u)` (book convention
`|f|² e^{-cu}` locally integrable).  For `u = φ|_W`, `c = k` this is the book's
`H⁰(Y, T ⊗ L|_Y^k ⊗ I(kφ|_Y))`. -/
def IsAlongMultiplierSection {m : ℕ} {W : Set X} [ChartedSpace (ComplexModel m) W]
    [IsComplexManifold m W] (c : ℝ) (u : W → EReal) (s : (y : W) → V y) : Prop :=
  ∀ y : W, (multiplierIdeal (n := m) 1 (fun w => (c : EReal) * u w)).mem y
    (alongCoefficient V (trivializationAt ℂ V y.val) s)

end Along

/-! ### The statement -/

section Statement

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **The conclusion of `thm:OT_ext`** for fixed `ω`, `(L, h)`, `(T, h_T)`, `θ`, `Y = W` and `δ`:
there are `k₀` and `C > 0` such that for all `k ≥ k₀`, all `φ ∈ PSH(X, θ - δω)` with
`φ|_W ≢ -∞` and all `s ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ I(kφ|_W))` there is
`s̃ ∈ H⁰(X, L^k ⊗ T ⊗ I(kφ))` with `s̃|_W = s` and
`∫_X |s̃|² e^{-kφ} ω^n ≤ C ∫_W |s|² e^{-kφ} ω|_W^m`. -/
def OTExtAlong (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (θ : ClosedRealOneOneForm n X) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (δ : ℝ) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ (k₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℕ, k₀ ≤ k →
  ∀ φ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val φ → (∃ y ∈ W, φ y ≠ ⊥) →
  ∀ s : (y : W) → (twistedPower L T k).Fiber y,
    IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) (k : ℝ) (fun y : W => φ y) s →
  ∃ s' : twistedSections L T k,
    s' ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ) ∧
    (∀ y : W, s' y = s y) ∧
    ∫⁻ x, ENNReal.ofReal (‖s' x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤
      ENNReal.ofReal C * ∫⁻ y : W, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb))

variable (n X) in
/-- **`thm:OT_ext`** (Hisamoto, Theorem 1.4; Xia, *Foundations of pluripotential theory*,
`thm:compact-submanifold-extension` and `cor:compact-positive-metric-extension`): on a compact
Kähler manifold `X` with Kähler form `ω`, for holomorphic line bundles `L`, `T` with smooth
Hermitian metrics `h`, `h_T`, `θ = c₁(L, h)`, every closed connected submanifold `Y` and every
`δ > 0`, the conclusion `OTExtAlong` holds. -/
def OTExtStatement : Prop :=
  ∀ (ωb : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∀ (W : Set X) (m : ℕ) (hW : IsClosedConnectedSubmanifold n W m) (δ : ℝ), 0 < δ →
    OTExtAlong ωb L T θ hW δ

end Statement

/-! ### Zero-dimensional submanifolds -/

section Point

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A closed connected complex submanifold of dimension `0` is a point. -/
theorem eq_of_mem_of_dim_zero {W : Set X} (hW : IsClosedConnectedSubmanifold n W 0)
    {x y : X} (hx : x ∈ W) (hy : y ∈ W) : x = y := by
  let hk : 0 ≤ n := Nat.zero_le n
  let : ChartedSpace (ComplexModel 0) W := chartedSpace hk hW.2.2
  -- every singleton of `W` is open: the chart at `p` is injective with values in a point
  have hopen : ∀ p : W, IsOpen ({p} : Set W) := by
    intro p
    set e := chartAt (ComplexModel 0) p with he
    have hsrc : e.source = {p} := by
      ext q
      constructor
      · intro hq
        have : e q = e p := Subsingleton.elim _ _
        exact e.injOn hq (mem_chart_source (ComplexModel 0) p) this
      · rintro rfl
        exact mem_chart_source (ComplexModel 0) q
    rw [← hsrc]
    exact e.open_source
  have : DiscreteTopology W := discreteTopology_iff_isOpen_singleton.mpr hopen
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have hcl : IsClopen ({(⟨x, hx⟩ : W)} : Set W) := isClopen_discrete _
  have huniv := hcl.eq_univ (singleton_nonempty _)
  have hmem : (⟨y, hy⟩ : W) ∈ ({(⟨x, hx⟩ : W)} : Set W) := by rw [huniv]; trivial
  exact (congrArg Subtype.val (mem_singleton_iff.mp hmem)).symm

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **`thm:OT_ext` for `dim Y = 0`.**  A zero-dimensional closed connected submanifold is a point
`{x₀}`; `φ(x₀) > -∞`, every vector of `(L^k ⊗ T)_{x₀}` is a section over `Y`, `ω|_Y^0` is a
positive multiple of the unit mass at `x₀`, and the statement is the uniform point extension
(lane S62, `SGPT.PSH.GlobalL2.globalPointExtension`; FPT `thm:compact-point-extension`). -/
theorem otExtAlong_of_dim_zero (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} (hW : IsClosedConnectedSubmanifold n W 0)
    {δ : ℝ} (hδ : 0 < δ) : OTExtAlong ωb L T θ hW δ := by
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  obtain ⟨k₀, C, hC, hext⟩ := SGPT.PSH.GlobalL2.globalPointExtension (n := n) (X := X)
    ‹CompactSpace X› ωb (IntegrationCurrent.kahlerVolume ωb) hμ L T hL hT θ hθ δ hδ
  unfold OTExtAlong
  intro hk
  let : ChartedSpace (ComplexModel 0) W := chartedSpace hk hW.2.2
  have : IsComplexManifold 0 W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
  set y₀ : W := ⟨x₀, hx₀⟩ with hy₀
  have hall : ∀ y : W, y = y₀ := fun y => Subtype.ext (eq_of_mem_of_dim_zero hW y.2 hx₀)
  set μW := IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
    with hμW
  have hc0 : μW univ ≠ 0 := (isOpen_univ.measure_pos μW ⟨y₀, mem_univ _⟩).ne'
  have hctop : μW univ ≠ ⊤ := measure_ne_top μW univ
  have hcpos : 0 < (μW univ).toReal := ENNReal.toReal_pos hc0 hctop
  refine ⟨k₀, C / (μW univ).toReal, div_pos hC hcpos, fun k hk' φ hφ hφW s _hs => ?_⟩
  have hφx₀ : φ x₀ ≠ ⊥ := by
    obtain ⟨y, hyW, hy⟩ := hφW
    rwa [eq_of_mem_of_dim_zero hW hyW hx₀] at hy
  obtain ⟨s', hs'x, hs'int⟩ := hext k hk' φ hφ x₀ hφx₀ (s y₀)
  -- the weight at `x₀` is finite
  have hwtop : multiplierWeight (k : ℝ) (φ x₀) ≠ ⊤ := by
    rw [← EReal.coe_toReal (hφ.1.quasiPlurisubharmonic.ne_top x₀) hφx₀, multiplierWeight_coe]
    exact ENNReal.ofReal_ne_top
  have hfin : ∫⁻ x, ENNReal.ofReal (‖s' x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)
      ∂(IntegrationCurrent.kahlerVolume ωb) < ⊤ :=
    lt_of_le_of_lt hs'int (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwtop.lt_top))
  refine ⟨s', (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ.quasiPshPotential s' hμ).mpr hfin, fun y => ?_, ?_⟩
  · rw [hall y]
    exact hs'x
  · -- the integral over the point `W`
    have hW_int : ∫⁻ y : W, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μW =
        ENNReal.ofReal (‖s y₀‖ ^ 2) * multiplierWeight (k : ℝ) (φ x₀) * μW univ := by
      rw [← lintegral_const]
      refine lintegral_congr fun y => ?_
      rw [hall y]
    rw [hW_int]
    refine hs'int.trans (le_of_eq ?_)
    have key : ∀ A : ℝ≥0∞, ENNReal.ofReal C / μW univ * (A * μW univ) = ENNReal.ofReal C * A := by
      intro A
      rw [mul_comm A, ← mul_assoc, ENNReal.div_mul_cancel hc0 hctop]
    rw [ENNReal.ofReal_div_of_pos hcpos, ENNReal.ofReal_toReal hctop, key]

end Point

end SGPT.Trace.TwistedL2
