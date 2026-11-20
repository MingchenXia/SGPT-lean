import SGPT.Foundations.Analysis.Pending.IntegrationCurrent
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope
import SGPT.Okounkov.TranscendentalWNRegBeta

/-!
# Package WN-REG: the statements consumed by WN-KEY (and the book's DNT environments)

Package WN-REG of the Witt Nyström chapter (`claude-tok-wn`, nodes `tok-wn:berman`,
`tok-wn:dnt`; refined in `claude-tok-wn-reg`).  This file contains **statements only**
(`def … : Prop`) and the definitions they need; nothing is asserted.

## Conventions

* Manifolds are TN's: `ChartedSpace (ComplexModel N) Y`, `IsComplexManifold N Y`; Kähler forms
  are `KahlerBackground`s, closed real `(1,1)`-forms are `ClosedRealOneOneForm`s,
  `θ`-psh functions are TN's `IsThetaPshPotential θ.val` (extended-real valued, with poles), the
  non-pluripolar measure `⟨(θ + ddᶜu)^N⟩` is `DiagonalMass.diagonalPotentialMeasure θ u hu`, and
  the envelope `P_θ(f) = (sup{v ∈ PSH(Y, θ) : v ≤ f q.e.})^*` is `rooftopEnvelope θ.val f`
  (`FirstPass.RooftopEnvelope`; for a continuous obstacle "q.e." and "everywhere" competitors give
  the same envelope).
* `positiveTopMeasure ω α` is the positive part `(α^N)^+` of the smooth top power of a closed
  real `(1,1)`-form `α`, as the measure with density `max(α^N/ω^N, 0)` against `ω^N`; on a set
  where `α ≥ 0` (e.g. a contact set, `tok-wn:contact-positivity`) it is `α^N`, so
  `1_E α^N = (positiveTopMeasure ω α).restrict E` there.
* `IsCOneOneBar f` (`C^{1,1̄}(Y)`, Darvas–Rubinstein; the book uses it without a definition): `f`
  is continuous and in every chart the distributional complex Hessian `ddᶜf` has locally bounded
  coefficients, i.e. `|∫ f ∂_v∂̄_v φ| ≤ C |v|² ‖φ‖_{L¹}` for test functions `φ` supported in a
  fixed compact set of the chart (`∂_v∂̄_v φ = leviForm φ · v`).
* `HasSmoothLineBoundApproximation A u b`: `u` is a uniform limit of chart-smooth `u_j` with
  `A + ddᶜu_j` Kähler and, for every `ε > 0` and large `j`, `A + ddᶜu_j ≤ (b(x) + ε) A` on every
  complex line at every point `x`.  This is the form in which the Laplacian bound of
  `tok-wn:berman` is produced (by Berman's β-family) and consumed (WN21 §7: the Lipschitz bound of
  `tok-wn:lipschitz` is applied to the smooth `u_j` and passes to the uniform limit); it implies
  `0 ≤ A + ddᶜu ≤ b A` in the sense of currents.

## Statements

* `BermanSmoothEnvelopeStatement` (`tok-wn:berman`, smooth obstacle; WN21 Theorem 2.5 with
  `ψ` smooth; Berman 2019, Prop. 2.4 + Prop. 2.7): constants `a, Λ` depending only on `(Y, A)`
  such that `P_A(F)` is real-valued and has the line bound `b(x) = (1 + S)Λ e^{a(F(x) - m)}`
  whenever `ddᶜF ≤ S A` and `m ≤ F`.
* `DNTConstantObstacleStatement` (`tok-wn:dnt` in the form WN-KEY uses it, WN21 §6 (v) and §7:
  constant obstacles on the fibres `X_τ`): `u ≤ c` gives `1_{u=c} θ^N ≤ ⟨θ_u^N⟩`.
* `DNTSmoothContactStatement` (`thm:DNTcontact` for `θ₁ = … = θ_N`, `φ₁ = … = φ_N`,
  `f₁ = … = f_N` smooth): `1_{u=f} ⟨θ_u^N⟩ = 1_{u=f} (θ + ddᶜf)^N`.
* The full `thm:DNTcontact` (mixed products, `fᵢ ∈ C^{1,1̄}`) needs the measure
  `θ_{1,f₁} ∧ ⋯ ∧ θ_{N,f_N}` of `C^{1,1̄}` functions (`L^∞` coefficients), which has no Lean
  definition yet; it is not stated here (see `tok/WN-REG/PLAN.md`).
* `DR16COneOneBarStatement` (`prop:DR16_C11bar`): `P_ω(min{f₁, f₂}) ∈ C^{1,1̄}` for
  `f₁, f₂ ∈ C^{1,1̄}` and `ω` Kähler.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

section Defs

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The positive part `(α^N)^+` of the smooth top power of a closed real `(1,1)`-form `α`, as the
measure with density `max(α^N/ω^N, 0)` against `ω^N`.  On a set where `α ≥ 0` it is `α^N`. -/
def positiveTopMeasure [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (w : KahlerBackground N Y) (α : ClosedRealOneOneForm N Y) : Measure Y :=
  (IntegrationCurrent.kahlerVolume w).withDensity fun x =>
    ENNReal.ofReal (IntegrationCurrent.topRatio w.form.val (ProductTestForms.formPow α.val N) x)

/-- The envelope `P_θ(F)` of a real obstacle, read as a real function (`(·).toReal`). -/
def envelopeReal (θ : ClosedRealOneOneForm N Y) (F : Y → ℝ) (x : Y) : ℝ :=
  (rooftopEnvelope θ.val (fun y => (F y : EReal)) x).toReal

/-- **Line-bounded smooth approximation**: `u` is a uniform limit of chart-smooth `u_j` with
`A + ddᶜu_j` Kähler and, for every `ε > 0`, eventually `A + ddᶜu_j ≤ (b(x) + ε)·A` on every
complex line at every point `x`. -/
def HasSmoothLineBoundApproximation (A : KahlerBackground N Y) (u b : Y → ℝ) : Prop :=
  ∃ (uj : ℕ → Y → ℝ) (huj : ∀ j, ChartSmooth (n := N) (uj j)),
    TendstoUniformly uj u atTop ∧
    (∀ j, (A.form + ddcClosedForm (uj j) (huj j)).val.IsKahler) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ (e : ComplexChart N Y) (z : ComplexModel N),
      z ∈ e.val.target → ∀ v : ComplexModel N,
        (A.form + ddcClosedForm (uj j) (huj j)).val.coeff e z ![v, Complex.I • v] ≤
          (b (e.val.symm z) + ε) * A.form.val.coeff e z ![v, Complex.I • v]

/-- Locally bounded distributional complex Hessian of a function on an open subset `U` of a
chart: for every compact `K ⊆ U` there is `C` with `|∫ g ∂_v∂̄_v φ| ≤ C |v|² ‖φ‖_{L¹}` for every
smooth `φ` supported in `K` (`∂_v∂̄_v φ = leviForm φ · v`). -/
def HasLocallyBoundedComplexHessianOn (g : ComplexModel N → ℝ) (U : Set (ComplexModel N)) :
    Prop :=
  ∀ K : Set (ComplexModel N), IsCompact K → K ⊆ U → ∃ C : ℝ,
    ∀ φ : ComplexModel N → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ K → ∀ v : ComplexModel N,
      |∫ z, g z * leviForm φ z v| ≤ C * ‖v‖ ^ 2 * ∫ z, |φ z|

/-- **`C^{1,1̄}(Y)`**: continuous, with locally bounded distributional complex Hessian in every
holomorphic chart (`ddᶜf ∈ L^∞`). -/
def IsCOneOneBar (f : Y → ℝ) : Prop :=
  Continuous f ∧ ∀ e : ComplexChart N Y,
    HasLocallyBoundedComplexHessianOn (fun z => f (e.val.symm z)) e.val.target

end Defs

/-! ### Berman's Laplacian estimate (`tok-wn:berman`) -/

/-- **`tok-wn:berman`, smooth obstacle** (WN21 Theorem 2.5 for smooth `ψ`; Berman 2019,
arXiv:1307.3008v3, Propositions 2.4 and 2.7): on a compact connected complex manifold `Y` of
dimension `N` with a Kähler form `A` there are `a ≥ 0` and `Λ > 0` such that for every
chart-smooth `F` with `ddᶜF ≤ S·A` on complex lines (`S ≥ 0`) and every lower bound `m ≤ F`, the
envelope `P_A(F)` is real-valued and is a line-bounded smooth limit with bound
`(1 + S) Λ e^{a(F(x) - m)}`; in particular `0 ≤ A + ddᶜP_A(F) ≤ (1 + S)Λ e^{a(F - m)} A`. -/
def BermanSmoothEnvelopeStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y),
    ∃ a Λ : ℝ, 0 ≤ a ∧ 0 < Λ ∧
      ∀ (F : Y → ℝ) (hF : ChartSmooth (n := N) F) (S : ℝ), 0 ≤ S →
        (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
          ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
            S * A.form.val.coeff e z ![v, Complex.I • v]) →
        ∀ m : ℝ, (∀ y, m ≤ F y) →
          (∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
            ((envelopeReal A.form F x : ℝ) : EReal)) ∧
          HasSmoothLineBoundApproximation A (envelopeReal A.form F)
            (fun x => (1 + S) * Λ * Real.exp (a * (F x - m)))

/-! ### The Di Nezza–Trapani contact formula (`tok-wn:dnt`, book `thm:DNTcontact`) -/

/-- **`tok-wn:dnt` for constant obstacles** (the form used in WN21 §6, step (v), and §7 on the
fibres `X_τ`): on a compact connected Kähler manifold, for a closed real `(1,1)`-form `θ`, a
`θ`-psh `u` and a constant `c` with `u ≤ c`, `1_{u = c} θ^N ≤ ⟨(θ + ddᶜu)^N⟩`.  (The reverse
inequality on `{u = c}` is `tok-wn:contact-upper`, package WN-ENV.) -/
def DNTConstantObstacleStatement : Prop :=
  ∀ (N : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
    [BorelSpace M] (w : KahlerBackground N M) (θ : ClosedRealOneOneForm N M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (c : ℝ), (∀ x, u x ≤ (c : EReal)) →
      (positiveTopMeasure w θ).restrict {x | u x = (c : EReal)} ≤
        DiagonalMass.diagonalPotentialMeasure θ u hu

/-- **`thm:DNTcontact` for a smooth obstacle, diagonal case** (`θᵢ = θ`, `φᵢ = u`, `fᵢ = f`
chart-smooth): `1_{u = f} ⟨(θ + ddᶜu)^N⟩ = 1_{u = f} (θ + ddᶜf)^N`. -/
def DNTSmoothContactStatement : Prop :=
  ∀ (N : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
    [BorelSpace M] (w : KahlerBackground N M) (θ : ClosedRealOneOneForm N M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (f : M → ℝ) (hf : ChartSmooth (n := N) f),
    (∀ x, u x ≤ (f x : EReal)) →
      (DiagonalMass.diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
        (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict {x | u x = (f x : EReal)}

/-- **`prop:DR16_C11bar`** (Darvas–Rubinstein, Theorem 2.5): for a Kähler form `ω` and
`f₁, f₂ ∈ C^{1,1̄}(Y)`, the envelope `P_ω(min{f₁, f₂})` is real-valued and lies in
`C^{1,1̄}(Y)`. -/
def DR16COneOneBarStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y] (w : KahlerBackground N Y)
    (f₁ f₂ : Y → ℝ), IsCOneOneBar (N := N) f₁ → IsCOneOneBar (N := N) f₂ →
      (∀ x, rooftopEnvelope w.form.val (fun y => (min (f₁ y) (f₂ y) : EReal)) x =
        ((envelopeReal w.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
      IsCOneOneBar (N := N) (envelopeReal w.form (fun y => min (f₁ y) (f₂ y)))

/-- The package statement consumed by WN-KEY: Berman's estimate and the DNT lower bound for
constant obstacles. -/
def WNRegStatement : Prop :=
  BermanSmoothEnvelopeStatement.{u} ∧ DNTConstantObstacleStatement.{u}

end SGPT.Okounkov.TranscendentalWNReg
