import SGPT.Okounkov.TranscendentalWNLegendre
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

/-!
# The global Monge–Ampère identity of the partial Legendre transform: statement (WN-VF2)

Blueprint node `tok-wn-vf:global-legendre-ma` (chapter `claude-tok-wn-vf`); source D. Witt
Nyström, *Deformations of Kähler manifolds to normal bundles and restricted volumes of big
classes*, arXiv:2103.03660 (WN21), Theorem 3.5 (`references/wn21-restricted-volume`).

Let `Y` be a compact complex manifold of dimension `N`, `θ` a closed real `(1,1)`-form on `Y` and
`u` a circle-invariant `π_Y^*θ`-psh function on `Y × ℂ*` (`IsPullbackThetaPshPunctured`,
`IsCircleInvariant`) with partial Legendre transform `û_λ` (`partialLegendre`).  Assume
`û_λ ≡ -∞` for `λ ∉ [a, b]` and that for `λ ∈ [a, b]` the `û_λ` are locally bounded off a locally
pluripolar set `A ⊆ Y` (WN21: a proper analytic subset) — `IsGlobalLegendreMAData`.  WN21
Theorem 3.5 asserts

  `(π_Y)_* ⟨(π_Y^*θ + dd^c u)^{N+1}⟩ = (N + 1) ∫_a^b ⟨(θ + dd^c û_λ)^N⟩ dλ`,

in particular `∫_{Y × ℂ*} ⟨(π_Y^*θ + dd^c u)^{N+1}⟩ = (N + 1) ∫_a^b ∫_Y ⟨(θ + dd^c û_λ)^N⟩ dλ`.

## Formal conventions

* `Y × ℂ*` is not given a manifold structure.  The non-pluripolar measure of `u` on `Y × ℂ*` is
  **characterized** chart by chart (`IsPuncturedProductMAMeasure`): `ν` is a measure on `Y × ℂ`
  (product Borel structure) such that on every product-chart patch `e⁻¹(W) × ℂ*`
  (`puncturedChartSource`), for every smooth local potential `ρ` of `θ` on `W` for which
  `(z, τ) ↦ u(e⁻¹ z, τ) + ρ(z)` is plurisubharmonic on `W × ℂ*`, `ν` is the local non-pluripolar
  measure (TN's `MongeAmpere.truncationLimitMeasure` on `W × ℂ* ⊆ ℂᴺ⁺¹`, coordinates
  `stripModelEquiv N`) of that function, transported by the chart (`productChartInverse`).
  This is exactly how the global non-pluripolar measure of TN (`globalMixedMeasure`) is built
  from patches, so on a compact manifold `M` with an open embedding `Y × ℂ* ↪ M` (the deformation
  `𝒳`, or `ℰ` minus two sections when the normal bundle is trivial) the restriction of the global
  measure, read on `Y × ℂ`, has this property.
* The measures of `û_λ` are TN's global non-pluripolar measures
  `globalMixedMeasure (fun _ => θ) (fun _ => û_λ)` (Kiselman: `û_λ` is `θ`-psh for every `λ`,
  `thetaPlurisubharmonic_partialLegendre`; for `û_λ ≡ -∞` the measure is `0`).
* The conclusion is the pushforward identity, tested on every Borel `B ⊆ Y`:
  `ν (B × ℂ*) = (N + 1) ∫⁻_{[a, b]} ⟨(θ + dd^c û_λ)^N⟩(B) dλ`.

`GlobalLegendreMAStatement N` is the statement (a `def … : Prop`); its proof from the local form
`PartialLegendreMALocalStatement N` (`tok-wn:legendre-ma`) is in
`TranscendentalWNVolumeGlobalLegendre.lean`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

section Global

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]

/-- The inverse product chart `w ↦ (e⁻¹ z, τ)`, `(z, τ) = stripModelEquiv N w`, from the model
`ℂᴺ⁺¹` to `Y × ℂ`. -/
def productChartInverse (e : ComplexChart N Y) (w : ComplexModel (N + 1)) : Y × ℂ :=
  (e.val.symm (stripModelEquiv N w).1, (stripModelEquiv N w).2)

/-- The product-chart patch `e⁻¹(W) × ℂ* ⊆ Y × ℂ`. -/
def puncturedChartSource (e : ComplexChart N Y) (W : Set (ComplexModel N)) : Set (Y × ℂ) :=
  {p | p.1 ∈ e.val.source ∧ e.val p.1 ∈ W ∧ p.2 ≠ 0}

variable [IsComplexManifold N Y]

/-- **`ν` is the non-pluripolar Monge–Ampère measure `⟨(π_Y^*θ + dd^c u)^{N+1}⟩` on `Y × ℂ*`**,
characterized on product-chart patches: for every chart `e`, open `W ⊆ e.target` with a smooth
local potential `ρ` of `θ` such that `(z, τ) ↦ u(e⁻¹ z, τ) + ρ(z)` is psh on `W × ℂ*`, and every
Borel `T ⊆ e⁻¹(W) × ℂ*`, `ν T` is the local non-pluripolar measure of that function of the
coordinate image of `T`. -/
def IsPuncturedProductMAMeasure [MeasurableSpace Y] (θ : SmoothRealForm N Y 2)
    (u : Y → ℂ → EReal) (ν : Measure (Y × ℂ)) : Prop :=
  ∀ (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ),
    IsSmoothLocalPotential θ e (W : Set (ComplexModel N)) ρ →
    ∀ (hpsh : PlurisubharmonicOn
        (productModelFunction fun z τ => stripChartFunction u e ρ (z, τ))
        (puncturedProductOpens W))
      (T : Set (Y × ℂ)), MeasurableSet T → T ⊆ puncturedChartSource e W →
      ν T = MongeAmpere.truncationLimitMeasure (puncturedProductOpens W)
        (productModelFunction fun z τ => stripChartFunction u e ρ (z, τ)) hpsh
        ((puncturedProductOpens W : Set (ComplexModel (N + 1))) ∩ productChartInverse e ⁻¹' T)

/-- The hypotheses of WN21 Theorem 3.5 on `Y`: `u ∈ PSH(Y × ℂ*, π_Y^*θ)` is circle-invariant,
`û_λ ≡ -∞` for `λ ∉ [a, b]`, and for `λ ∈ [a, b]` the function `û_λ` is locally bounded near every
point off the locally pluripolar set `A`. -/
structure IsGlobalLegendreMAData (θ : SmoothRealForm N Y 2) (u : Y → ℂ → EReal) (a b : ℝ)
    (A : Set Y) : Prop where
  psh : IsPullbackThetaPshPunctured θ u
  circleInvariant : IsCircleInvariant u
  le : a ≤ b
  eq_bot_of_notMem : ∀ lam : ℝ, lam ∉ Icc a b → ∀ y, partialLegendre u lam y = ⊥
  pluripolar : ManifoldLocallyPluripolar (n := N) A
  locallyBounded : ∀ lam ∈ Icc a b, ∀ y ∉ A, ∃ C : ℝ,
    ∀ᶠ y' in 𝓝 y, ((-C : ℝ) : EReal) ≤ partialLegendre u lam y' ∧
      partialLegendre u lam y' ≤ (C : EReal)

end Global

/-- **`tok-wn-vf:global-legendre-ma`** (WN21 Theorem 3.5): on a compact complex manifold `Y` of
dimension `N`, for `u` as in `IsGlobalLegendreMAData` and `ν` its non-pluripolar Monge–Ampère
measure on `Y × ℂ*` (`IsPuncturedProductMAMeasure`),
`(π_Y)_* ν = (N + 1) ∫_a^b ⟨(θ + dd^c û_λ)^N⟩ dλ`, tested on every Borel `B ⊆ Y`. -/
def GlobalLegendreMAStatement (N : ℕ) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (θ : ClosedRealOneOneForm N Y) (u : Y → ℂ → EReal) (a b : ℝ) (A : Set Y)
    (h : IsGlobalLegendreMAData θ.val u a b A) (ν : Measure (Y × ℂ)),
    IsPuncturedProductMAMeasure θ.val u ν →
    ∀ B : Set Y, MeasurableSet B →
      ν (B ×ˢ puncturedPlane) = ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Icc a b,
        globalMixedMeasure (fun _ : Fin N => θ) (fun _ => partialLegendre u lam)
          (fun _ => thetaPlurisubharmonic_partialLegendre h.psh h.circleInvariant lam) B

end SGPT.Okounkov.TranscendentalWN
