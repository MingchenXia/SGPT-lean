import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.Pending.NonPluripolarLimit
import SGPT.Foundations.Analysis.FirstPass.PluripolarSets

/-!
# The partial Legendre transform: objects and the Monge–Ampère statement (package WN-LEG)

Blueprint chapter `claude-tok-wn` (nodes `tok-wn:legendre`, `tok-wn:legendre-usc`,
`tok-wn:legendre-ma`) and its supplement `claude-tok-wn-leg`; source D. Witt Nyström,
*Deformations of Kähler manifolds to normal bundles and restricted volumes of big classes*,
arXiv:2103.03660 (WN21), §3, Definition 3.1, Lemma 3.2, Theorems 3.3 and 3.5
(`references/wn21-restricted-volume`), after Kiselman (1978).

Let `u` be a circle-invariant plurisubharmonic (or `π_X^* θ`-plurisubharmonic) function of
`(z, τ) ∈ U × ℂ*`.  Its **partial Legendre transform** is

  `û_λ(z) = inf_{τ ∈ ℂ*} (u(z, τ) - λ log |τ|²)`,   `λ ∈ ℝ`.

This file fixes the objects and records, as a `def … : Prop`, the Monge–Ampère identity of
WN21 Theorem 3.3 that the volume formulas of package WN-VF consume.  **Nothing is asserted
here.**  The basic properties of `û_λ` (concavity in `λ`, Kiselman: `û_λ` is (`θ`-)psh, and
Legendre duality) and WN21 Lemma 3.2 are proved in `TranscendentalWNLegendre.lean` and
`TranscendentalWNLegendreUSC.lean`.

## Objects

* `logNormSq τ = log |τ|²` and `puncturedPlane = ℂ* = {τ ≠ 0}`.
* `partialLegendre u λ` — `û_λ` for any `u : X → ℂ → EReal` (`X` arbitrary; `EReal`
  subtraction keeps poles: `⊥ - c = ⊥`).
* `IsCircleInvariant u` — `u(x, τ) = u(x, σ)` whenever `|τ| = |σ|`.
* `IsPullbackThetaPshPunctured θ u` — `u ∈ PSH(M × ℂ*, π_M^* θ)` for a complex manifold `M`
  with a smooth real `2`-form `θ`: in every holomorphic chart `e` of `M`, around every point of
  the chart target there is a smooth local potential `ρ` of `θ` on an open `W` such that
  `(z, τ) ↦ u(e⁻¹ z, τ) + ρ(z)` is plurisubharmonic on `W × ℂ*`.  This is the project's
  `ThetaPlurisubharmonic` for the form `π_M^* θ` on the product charts `e × id`, with the
  local potential `ρ ∘ π_M` (any two local potentials differ by a pluriharmonic function, so
  the choice is immaterial); it is the shape of TN's subgeodesic condition
  `FirstPass.IsSubgeodesicInterior`, with the strip replaced by `ℂ*`.
* `puncturedProductOpens Ω` and `productModelFunction u` — for `Ω ⊆ ℂᴺ` open, the open set
  `Ω × ℂ*` and the function `u` read on the model `ℂᴺ⁺¹` through TN's identification
  `stripModelEquiv N : ℂᴺ⁺¹ ≃ ℂᴺ × ℂ` (the last coordinate is `τ`).

## The statement

`PartialLegendreMALocalStatement N` (`tok-wn:legendre-ma`, WN21 Theorem 3.3 in the form of
Theorem 3.5 with a pluripolar exceptional set): for `Ω ⊆ ℂᴺ` open and `u` circle-invariant psh
on `Ω × ℂ*` such that `û_λ ≡ -∞` on `Ω` for `λ ∉ [a, b]` and, for `λ ∈ [a, b]`, `û_λ` is locally
bounded on `Ω \ A` for a locally pluripolar set `A`, every Borel set `E` satisfies

  `⟨(dd^c u)^{N+1}⟩ (E × ℂ*) = (N + 1) ∫_a^b ⟨(dd^c û_λ)^N⟩ (E) dλ`,

i.e. `(π_Ω)_* ⟨(dd^c u)^{N+1}⟩ = (N + 1) ∫_a^b ⟨(dd^c û_λ)^N⟩ dλ`.  Non-pluripolar products are
TN's local ones (`Pending.MongeAmpere.truncationLimitMeasure`, normalization
`dd^c = i ∂∂̄ / 2π`), which put no mass on (locally) pluripolar sets; a proper analytic subset
of a connected open set is locally pluripolar, so WN21's hypothesis is a special case.  The
`θ`-twisted and global forms of WN21 Theorem 3.5 follow by adding a local potential `ρ` of `θ`
(`û_λ + ρ` is the partial Legendre transform of `u + ρ ∘ π`) and gluing over charts.
The plurisubharmonicity proofs `hu`, `hû` are universally quantified: the measures do not
depend on them (`truncationLimitMeasure_proof_independent`), and both are provided by
`TranscendentalWNLegendre` (`hû` is Kiselman's minimum principle).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

/-! ### The partial Legendre transform -/

section General

variable {X : Type*}

/-- `log |τ|²`. -/
def logNormSq (τ : ℂ) : ℝ := Real.log (‖τ‖ ^ 2)

/-- The punctured plane `ℂ* = {τ ≠ 0}`. -/
def puncturedPlane : Set ℂ := {τ | τ ≠ 0}

theorem isOpen_puncturedPlane : IsOpen puncturedPlane := isOpen_ne

/-- **`tok-wn:legendre`** (WN21 Definition 3.1): the partial Legendre transform
`û_λ(x) = inf_{τ ∈ ℂ*} (u(x, τ) - λ log |τ|²)`. -/
def partialLegendre (u : X → ℂ → EReal) (lam : ℝ) (x : X) : EReal :=
  ⨅ τ : puncturedPlane, u x τ - ((lam * logNormSq τ : ℝ) : EReal)

/-- Circle invariance in the `ℂ` variable: `u(x, τ) = u(x, σ)` when `|τ| = |σ|`. -/
def IsCircleInvariant (u : X → ℂ → EReal) : Prop :=
  ∀ (x : X) (τ σ : ℂ), ‖τ‖ = ‖σ‖ → u x τ = u x σ

end General

/-! ### `π_M^* θ`-plurisubharmonic functions on `M × ℂ*` -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`u ∈ PSH(M × ℂ*, π_M^* θ)`**: in every holomorphic chart `e` of `M`, around every point of
the chart target, a smooth local potential `ρ` of `θ` on an open `W` makes the corrected
complexification `(z, τ) ↦ u(e⁻¹ z, τ) + ρ(z)` plurisubharmonic on `W × ℂ*`. -/
def IsPullbackThetaPshPunctured (θ : SmoothRealForm n M 2) (u : M → ℂ → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ), z ∈ W ∧
      IsSmoothLocalPotential θ e W ρ ∧
        PlurisubharmonicOn (stripChartFunction u e ρ) (W ×ˢ puncturedPlane)

end Manifold

/-! ### The local Monge–Ampère statement -/

section Local

variable {N : ℕ}

/-- `Ω × ℂ*` as an open subset of the model `ℂᴺ⁺¹` (coordinates `stripModelEquiv N`). -/
def puncturedProductOpens (Ω : Opens (ComplexModel N)) : Opens (ComplexModel (N + 1)) :=
  ⟨stripModelEquiv N ⁻¹' ((Ω : Set (ComplexModel N)) ×ˢ puncturedPlane),
    (Ω.isOpen.prod isOpen_puncturedPlane).preimage (stripModelEquiv N).continuous⟩

/-- `u(z, τ)` read on the model `ℂᴺ⁺¹`, `(z, τ) = stripModelEquiv N w`. -/
def productModelFunction (u : ComplexModel N → ℂ → EReal) : ComplexModel (N + 1) → EReal :=
  fun w => u (stripModelEquiv N w).1 (stripModelEquiv N w).2

/-- The hypotheses of `tok-wn:legendre-ma` (WN21 Theorems 3.3 and 3.5) on an open `Ω ⊆ ℂᴺ`:
`u` is circle-invariant psh on `Ω × ℂ*`, `û_λ ≡ -∞` on `Ω` for `λ ∉ [a, b]`, and for
`λ ∈ [a, b]` the function `û_λ` is locally bounded near every point of `Ω \ A`, where `A` is
locally pluripolar in `Ω`. -/
structure IsLegendreMAData (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal)
    (a b : ℝ) (A : Set (ComplexModel N)) : Prop where
  psh : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => u p.1 p.2)
    ((Ω : Set (ComplexModel N)) ×ˢ puncturedPlane)
  circleInvariant : IsCircleInvariant u
  le : a ≤ b
  eq_bot_of_notMem : ∀ lam : ℝ, lam ∉ Icc a b → ∀ z ∈ Ω, partialLegendre u lam z = ⊥
  pluripolar : LocallyPluripolarOn A Ω
  locallyBounded : ∀ lam ∈ Icc a b, ∀ z ∈ (Ω : Set (ComplexModel N)) \ A, ∃ C : ℝ,
    ∀ᶠ w in 𝓝 z, ((-C : ℝ) : EReal) ≤ partialLegendre u lam w ∧
      partialLegendre u lam w ≤ (C : EReal)

/-- **`tok-wn:legendre-ma`** (WN21 Theorem 3.3, with Theorem 3.5's exceptional set), local form:
`(π_Ω)_* ⟨(dd^c u)^{N+1}⟩ = (N + 1) ∫_a^b ⟨(dd^c û_λ)^N⟩ dλ`, tested on every Borel `E ⊆ ℂᴺ`. -/
def PartialLegendreMALocalStatement (N : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ)
    (A : Set (ComplexModel N)), IsLegendreMAData Ω u a b A →
    ∀ (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω))
      (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω)
      (E : Set (ComplexModel N)), MeasurableSet E →
      MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u) hu
          (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ℝ≥0∞) *
          ∫⁻ lam in Icc a b, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E

end Local

end SGPT.Okounkov.TranscendentalWN
