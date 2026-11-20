import SGPT.PSH.SourceGentleApproximation
import SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor
import SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates

/-!
# A quasi-psh pole along a closed submanifold: the statement

Source: DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*),
proofs of Proposition 3.4 and Theorem 6.1, which quote Demailly--Păun, *Numerical
characterization of the Kähler cone*, Lemma 2.1; complete proof in Xia, *Foundations of
pluripotential theory*, `lem:global-normal-pole`. Blueprint node `tok:ext-pole`.

Let `X` be a compact complex manifold with a Kähler form `ω` and `V ⊆ X` a closed complex
submanifold with empty interior (codimension `≥ 1` at each of its points; components may have
different dimensions, and `V = ∅` is allowed). A **pole along `V`** is a function
`F : X → [-∞, ∞)` such that (`IsSubmanifoldPole`)

* `F ∈ PSH(X, C ω)` for a constant `C ≥ 0`, i.e. `ddᶜ F ≥ -C ω`;
* `F = -∞` exactly on `V`, `F` is smooth on `X \ V` and continuous as an extended-real function,
  and `e^F` is smooth on `X`;
* near every point of `V`, in **every** flattening chart `ζ` of `V` (`V = {ζ_i = 0, i ≥ k}`),
  `F = log ∑_{i ≥ k} |ζ_i|² + O(1)`;
* `F` has analytic singularities of type `(1, 𝓘_V)`;
* on **every** blowup `π : Z → X` along `V`, locally `F ∘ π = log |h|² + R` with `h` a local
  generator of the ideal `π^* 𝓘_V = 𝒪_Z(-E)` of the exceptional divisor `E` and `R` smooth;
* for every `c ∈ ℚ_{>0}`, `c F` has gentle analytic singularities of type `(c, 𝓘_V)` in the sense
  of the book (`def:analy-sing`, `SGPT.PSH.SourceGentleAnalyticSingularities`).

`SubmanifoldPoleStatement` asserts that every such `V` has a pole. It is the interface consumed by
the packages BODY (`tok:body-interior`) and EXT (`tok:ct-key`, `tok:ct-extension`); its proof is
`SGPT.Okounkov.TranscendentalPole.exists_submanifold_pole` (file `TranscendentalPole.lean`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The normal weight `∑_{i ≥ k} |ζ_i|²` of a flattening chart `ζ = Φ ∘ chartAt x₀` in which the
submanifold is `{ζ_i = 0, i ≥ k}`. -/
def flatNormalWeight {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (k : ℕ) (y : X) : ℝ :=
  ∑ i : Fin n, if k ≤ i.1 then Complex.normSq (flatCoord Φ i y) else 0

/-- `Φ` (at the chart of `x₀`) flattens `V` onto the coordinate plane `{ζ_i = 0, i ≥ k}`: the
flattening condition of `RegularAtDim`. -/
def IsFlatteningOf (V : Set X) {x₀ : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)) (k : ℕ) : Prop :=
  Φ.source ⊆ (chartAt (ComplexModel n) x₀).target ∧
    ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x₀).source →
      chartAt (ComplexModel n) x₀ y ∈ Φ.source →
        (y ∈ V ↔ Φ.toFun (chartAt (ComplexModel n) x₀ y) ∈ complexCoordinatePlane n k)

/-- **A pole along the closed submanifold `V`** (DP04 Lemma 2.1, FPT `lem:global-normal-pole`),
relative to the Kähler form `ω`. -/
structure IsSubmanifoldPole (omega : KahlerBackground n X) (V : Set X) (F : X → EReal) : Prop where
  /-- `ddᶜ F ≥ -C ω`: `F` is a `C ω`-psh potential. -/
  exists_thetaPsh : ∃ C : ℝ, 0 ≤ C ∧ IsThetaPshPotential (C • omega.form).val F
  /-- The pole set of `F` is exactly `V`. -/
  eq_bot_iff : ∀ x, F x = ⊥ ↔ x ∈ V
  /-- `F` never takes the value `+∞`. -/
  ne_top : ∀ x, F x ≠ ⊤
  /-- `F` is continuous as an extended-real function (so `F → -∞` at `V`). -/
  continuous : Continuous F
  /-- `F` is smooth on `X \ V`. -/
  smoothOn_compl : ∀ e : ComplexChart n X,
    ContDiffOn ℝ ∞ (fun z => (F (e.val.symm z)).toReal) (e.val.target ∩ e.val.symm ⁻¹' Vᶜ)
  /-- `e^F` is smooth on `X`. -/
  chartSmooth_exp : ChartSmooth (n := n) (fun x => (EReal.exp (F x)).toReal)
  /-- In every flattening chart `ζ` of `V` at a point `x ∈ V`,
  `F = log ∑_{i ≥ k} |ζ_i|² + O(1)` near `x`. -/
  localForm : ∀ x ∈ V, ∀ (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
    IsFlatteningOf V Φ k → ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, y ∉ V →
      |(F y).toReal - Real.log (flatNormalWeight Φ k y)| ≤ C
  /-- `F` has analytic singularities of type `(1, 𝓘_V)`. -/
  analyticType : HasAnalyticSingularitiesOfType (n := n) F 1 (vanishingIdeal (n := n) V)
  /-- On every blowup `π : Z → X` along `V`: locally `F ∘ π = log |h|² + R`, `h` a local
  generator of the exceptional divisor ideal `π^* 𝓘_V` and `R` smooth. -/
  blowup : ∀ {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (π : Z → X) (hπ : IsBlowupAlong n V π) (z : Z),
    ∃ (S : Set Z) (h : Z → ℂ) (R : Z → ℝ), IsOpen S ∧ z ∈ S ∧
      (∀ y ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h y) ∧
      (∀ y ∈ S, ∀ a : Z → ℂ,
        (exceptionalDivisor hπ).ideal.mem y a ↔ IsInSpanAt (n := n) (· = h) y a) ∧
      (∀ e : ComplexChart n Z,
        ContDiffOn ℝ ∞ (fun w => R (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      ∀ y ∈ S, F (π y) = ENNReal.log (ENNReal.ofReal (‖h y‖ ^ 2)) + (R y : EReal)
  /-- For every `c ∈ ℚ_{>0}`, `c F` has gentle analytic singularities of type `(c, 𝓘_V)`. -/
  gentle : ∀ c : ℚ, 0 < c →
    SGPT.PSH.SourceGentleAnalyticSingularities (n := n) (fun x => ((c : ℝ) : EReal) * F x) c
      (vanishingIdeal (n := n) V)

/-- **`tok:ext-pole`** (DP04 Lemma 2.1, FPT `lem:global-normal-pole`): every closed complex
submanifold with empty interior of a compact Kähler manifold carries a pole. -/
def SubmanifoldPoleStatement : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] (omega : KahlerBackground n X) (V : Set X),
    IsClosedSubmanifold n V → interior V = ∅ → ∃ F : X → EReal, IsSubmanifoldPole omega V F

end SGPT.Okounkov.TranscendentalPole
