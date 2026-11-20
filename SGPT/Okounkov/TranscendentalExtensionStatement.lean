import SGPT.PSH.SourceGentleApproximation
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

/-!
# Extension of Kähler currents from a submanifold: statements

Source: the book's `thm:CT-thm-refined'` (chapter *Quasi-plurisubharmonic functions*,
`chapter_pshfunctions.tex` l. 1550--1560), which is Darvas--Reboulet--Witt Nyström--Xia--Zhang,
*Transcendental Okounkov bodies* (DRWNXZ), Theorem 6.1; complete proof in Xia, *Foundations of
pluripotential theory* (FPT), `thm:holder-positive-potential-extension`. Blueprint nodes
`tok:ct-extension`, `tok:ct-gentle`, `tok:ext-pole` (chapter `claude-okounkov-transcendental`).

> Let `X` be a connected compact Kähler manifold and `Y ⊆ X` a connected closed submanifold.
> Take a Kähler form `ω` on `X` and `φ ∈ PSH(Y, ω|_Y)` such that `ω|_Y + dd^c φ` is a Kähler
> current and `e^φ` is a Hölder continuous function on `Y`. Then there exists
> `φ̃ ∈ PSH(X, ω)` with `φ̃|_Y = φ` and `ω_φ̃` a Kähler current. In addition, if `φ` has
> analytic singularities, then so does `φ̃`.

This file contains **definitions and statements only** (package EXT of the formalization plan
of `thm:Okounkovtranmain`); the proofs are in `TranscendentalExtension*.lean`.

## Formal conventions

* `X` is a complex manifold over `ComplexModel n` (TN's `IsComplexManifold`), `ω` a
  `KahlerBackground` (a Kähler form), `Y` an `IsClosedConnectedSubmanifold n Y k` with the
  submanifold charts of `SubmanifoldChartedSpace` (`submanifoldCharts`) and the restricted
  Kähler form `ω|_Y` (`restrictedKahler`, the pullback along the holomorphic inclusion).
* `φ ∈ PSH(Y, θ)` is `IsThetaPshPotential θ.val φ`; "`θ + dd^c φ` is a Kähler current" is
  `IsKahlerCurrentPotential θ φ` (`θ + dd^c φ ≥ ω'` for a Kähler form `ω'`, book
  `def:psefclass`).
* `e^φ` (with `e^{-∞} = 0`) is `expPotential φ`; Hölder continuity on a manifold is
  `IsChartHolder` (FPT, `sec:strict-positive-potential-extension`): there is an exponent
  `α ∈ (0, 1]` such that near every point of every chart `|f a - f b| ≤ C |e a - e b|^α`.
  Hölder continuity is chart-independent (FPT `lem:manifold-holder-operations` (1)), so it is
  tested in every chart of the atlas; on a compact manifold one exponent serves everywhere
  (FPT `lem:manifold-holder-operations` (2)), so the exponent is fixed globally, as in DRWNXZ
  ("`e^φ` is `α`-Hölder continuous for some `α > 0`").
* "Analytic singularities" is TN's `HasManifoldAnalyticSingularityType` (in every holomorphic
  chart, near every point, `φ = c log ∑ |f_i|² + O(1)` with `c ∈ ℚ_{>0}`), the convention of
  `SGPT.Okounkov.TranscendentalCore.analyticCurrents` (`tok:def-classes`).
* `φ̃|_Y = φ` is `∀ y : Y, φ̃ y = φ y`.

## Main definitions

* `IsChartHolderWith`, `IsChartHolder`, `expPotential`;
* `HasKahlerCurrentExtension ω hY`: the conclusion of `thm:CT-thm-refined'` for fixed data;
  `KahlerCurrentExtensionStatement`: the book's theorem (all dimensions of `Y`);
* `HasContinuousKahlerCurrentExtension`: the version of DRWNXZ Theorem 6.1 used downstream
  (moreover `φ̃` is finite and continuous on `X \ Y`, blueprint `tok:ct-extension`);
* `HasGentleKahlerCurrentExtension`, `GentleExtensionStatement`: DRWNXZ Theorem 6.4
  (blueprint `tok:ct-gentle`);
* `IsNormalPole`, `NormalPoleStatement`: the input of DRWNXZ's proof from DP04 Lemma 2.1 /
  FPT `lem:global-normal-pole` (blueprint `tok:ext-pole`, package POLE): a quasi-psh function
  equal to `-∞` exactly on `Y`, continuous off `Y`, with analytic singularities and with the
  normal lower bound `|w|² ≤ C e^F` in every system of normal coordinates.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalExtension

open Set Filter
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

section Holder

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]

/-- `f` is Hölder continuous with exponent `α` in the charts of `M`: near every point of the
source of every chart `e` of the atlas, `|f a - f b| ≤ C ‖e a - e b‖^α` (FPT,
`sec:strict-positive-potential-extension`). -/
def IsChartHolderWith (α : ℝ) (f : M → ℝ) : Prop :=
  ∀ e ∈ atlas (ComplexModel k) M, ∀ x ∈ e.source, ∃ V ∈ 𝓝 x, V ⊆ e.source ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ V, ∀ b ∈ V, |f a - f b| ≤ C * ‖e a - e b‖ ^ α

/-- `f` is Hölder continuous on `M`: Hölder continuous with some exponent `α ∈ (0, 1]` in the
charts of `M`. -/
def IsChartHolder (f : M → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ IsChartHolderWith (k := k) α f

end Holder

/-- `e^u` as a real function, with `e^{-∞} = 0` (the value at `+∞`, never taken by a quasi-psh
function, is the junk value `0`). -/
def expPotential {M : Type*} (u : M → EReal) (x : M) : ℝ :=
  (EReal.exp (u x)).toReal

section Submanifold

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The submanifold charts of a closed connected submanifold `Y` of dimension `k`
(`SubmanifoldChartedSpace.chartedSpace`; the subspace topology). -/
abbrev submanifoldCharts {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) :
    ChartedSpace (ComplexModel k) Y :=
  SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hY) hY.2.2

theorem submanifold_isComplexManifold {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) :
    letI := submanifoldCharts hY
    IsComplexManifold k Y :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hY) hY.2.2

/-- The restriction `ω|_Y` of a Kähler form to the submanifold `Y` (the pullback along the
holomorphic inclusion), a Kähler form of `Y`. -/
abbrev restrictedKahler (ω : KahlerBackground n X) {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) :
    letI := submanifoldCharts hY
    haveI := submanifold_isComplexManifold hY
    KahlerBackground k Y :=
  SubmanifoldKahlerRestriction.kahlerBackground
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hY) hY.2.2 ω

/-- **The conclusion of `thm:CT-thm-refined'`** for fixed `X`, `ω`, `Y`: every
`φ ∈ PSH(Y, ω|_Y)` such that `ω|_Y + dd^c φ` is a Kähler current and `e^φ` is Hölder
continuous extends to `φ̃ ∈ PSH(X, ω)` with `φ̃|_Y = φ` and `ω + dd^c φ̃` a Kähler current;
if `φ` has analytic singularities, so does `φ̃`. -/
def HasKahlerCurrentExtension (ω : KahlerBackground n X) {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) : Prop :=
  letI := submanifoldCharts hY
  haveI := submanifold_isComplexManifold hY
  ∀ φ : Y → EReal, IsThetaPshPotential (restrictedKahler ω hY).form.val φ →
    IsKahlerCurrentPotential (restrictedKahler ω hY).form φ →
    IsChartHolder (k := k) (expPotential φ) →
    ∃ φ' : X → EReal, IsThetaPshPotential ω.form.val φ' ∧ (∀ y : Y, φ' y = φ y) ∧
      IsKahlerCurrentPotential ω.form φ' ∧
      (HasManifoldAnalyticSingularityType (n := k) φ →
        HasManifoldAnalyticSingularityType (n := n) φ')

/-- **The extension of DRWNXZ Theorem 6.1 used downstream** (blueprint `tok:ct-extension`): the
conclusion of `HasKahlerCurrentExtension`, and moreover `φ̃` is finite and continuous on
`X \ Y`. -/
def HasContinuousKahlerCurrentExtension (ω : KahlerBackground n X) {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) : Prop :=
  letI := submanifoldCharts hY
  haveI := submanifold_isComplexManifold hY
  ∀ φ : Y → EReal, IsThetaPshPotential (restrictedKahler ω hY).form.val φ →
    IsKahlerCurrentPotential (restrictedKahler ω hY).form φ →
    IsChartHolder (k := k) (expPotential φ) →
    ∃ φ' : X → EReal, IsThetaPshPotential ω.form.val φ' ∧ (∀ y : Y, φ' y = φ y) ∧
      IsKahlerCurrentPotential ω.form φ' ∧
      (HasManifoldAnalyticSingularityType (n := k) φ →
        HasManifoldAnalyticSingularityType (n := n) φ') ∧
      ContinuousOn φ' Yᶜ ∧ ∀ x ∉ Y, φ' x ≠ ⊥

/-- **DRWNXZ Theorem 6.4** (blueprint `tok:ct-gentle`) for fixed data: for a Kähler form `κ`
on `X`, every Kähler current `κ|_Y + dd^c φ` on `Y` with gentle analytic singularities extends
to a Kähler current `κ + dd^c φ̃` on `X` with analytic singularities, `φ̃|_Y = φ`, and `φ̃`
finite and continuous on `X \ Y`. -/
def HasGentleKahlerCurrentExtension (κ : KahlerBackground n X) {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) : Prop :=
  letI := submanifoldCharts hY
  haveI := submanifold_isComplexManifold hY
  ∀ φ : Y → EReal, IsKahlerCurrentPotential (restrictedKahler κ hY).form φ →
    (∃ (c : ℚ) (𝔞 : GermIdeal k Y), SGPT.PSH.SourceGentleAnalyticSingularities φ c 𝔞) →
    ∃ φ' : X → EReal, IsKahlerCurrentPotential κ.form φ' ∧
      HasManifoldAnalyticSingularityType (n := n) φ' ∧ (∀ y : Y, φ' y = φ y) ∧
      ContinuousOn φ' Yᶜ ∧ ∀ x ∉ Y, φ' x ≠ ⊥

/-- The normal part `w` of a point `z = (z', w)` of `ℂⁿ = ℂᵏ × ℂ^{n-k}`, as a vector of `ℂⁿ`
(`z - ι(pr z)`). -/
def normalPart (n k : ℕ) (z : ComplexModel n) : ComplexModel n :=
  z - coordinateInclusion n k (coordinateProjection n k z)

/-- **A normal pole along `Y`** (blueprint `tok:ext-pole`; DP04 Lemma 2.1, FPT
`lem:global-normal-pole` with `F = log R_Y`): `F` is quasi-psh (`B ω + dd^c F ≥ 0`), equal to
`-∞` exactly on `Y`, finite-valued and continuous off `Y`, with analytic singularities, and
`F ≥ log |w|² - O(1)` near every point of `Y` in every system of normal coordinates `(z', w)`
(flattening data of `Y`). -/
structure IsNormalPole (ω : KahlerBackground n X) (Y : Set X) (k : ℕ) (F : X → EReal) : Prop where
  thetaPsh : ∃ B : ℝ, 0 ≤ B ∧ IsThetaPshPotential (B • ω.form).val F
  eq_bot_iff : ∀ x, F x = ⊥ ↔ x ∈ Y
  continuousOn : ContinuousOn F Yᶜ
  analytic : HasManifoldAnalyticSingularityType (n := n) F
  lower : ∀ (G : SubmanifoldChartedSpace.FlatData n k X Y) (q : X), q ∈ Y → q ∈ G.ambSource →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in 𝓝 q,
      ‖normalPart n k (G.flat (G.amb.val x))‖ ^ 2 ≤ C * expPotential F x

end Submanifold

/-- **Source `thm:CT-thm-refined'`** (book, chapter *Quasi-plurisubharmonic functions*): for
every connected compact Kähler manifold `(X, ω)` and every connected closed submanifold `Y ⊆ X`
(of any dimension `k`), `HasKahlerCurrentExtension ω hY`. -/
def KahlerCurrentExtensionStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] (ω : KahlerBackground n X)
    (Y : Set X) (k : ℕ) (hY : IsClosedConnectedSubmanifold n Y k),
    HasKahlerCurrentExtension ω hY

/-- **DRWNXZ Theorem 6.1** in the form of blueprint `tok:ct-extension` (connected closed
submanifold of positive dimension; `φ̃` moreover finite and continuous off `Y`). -/
def ContinuousKahlerCurrentExtensionStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] (ω : KahlerBackground n X)
    (Y : Set X) (k : ℕ) (hY : IsClosedConnectedSubmanifold n Y k), 0 < k →
    HasContinuousKahlerCurrentExtension ω hY

/-- **DRWNXZ Theorem 6.4** (blueprint `tok:ct-gentle`): `Y ⊊ X` a connected closed submanifold
of positive dimension (`0 < k < n`; for connected `X`, `k < n` is `Y ≠ X`). -/
def GentleExtensionStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] (κ : KahlerBackground n X)
    (Y : Set X) (k : ℕ) (hY : IsClosedConnectedSubmanifold n Y k), 0 < k → k < n →
    HasGentleKahlerCurrentExtension κ hY

/-- **The pole input** (blueprint `tok:ext-pole`, DP04 Lemma 2.1, FPT `lem:global-normal-pole`):
every proper connected closed submanifold of a compact Kähler manifold carries a normal pole.
This is the interface of the extension package to package POLE; it is a statement, not proved
here. -/
def NormalPoleStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] (ω : KahlerBackground n X)
    (Y : Set X) (k : ℕ), IsClosedConnectedSubmanifold n Y k → k < n →
    ∃ F : X → EReal, IsNormalPole ω Y k F

end SGPT.Okounkov.TranscendentalExtension
