import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Okounkov.TranscendentalCoreDivisorGenerators
import SGPT.Foundations.Analysis.Pending.DivisorMetric

/-!
# Relative global generation and pushforwards with analytic singularities: statements

Source: blueprint nodes `tok:relgen`, `tok:boucksom-pushforward` and `relgen:l2-generation`
(chapters `claude-okounkov-transcendental` and `claude-tok-relgen`), i.e. the claim in the proof
of Lemma 2.8 of Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*
(DRWNXZ), Lemma 2.8 itself, and the `L²` input they use (Demailly, *On the cohomology of
pseudoeffective line bundles*, 2015, Corollary 5.3, in the form of Demailly's Theorem 6.27 /
Nadel's argument).

This file contains **statements only** (`def … : Prop`); they are the interface of the RELGEN
package for the other packages (LIFT consumes `PushforwardAnalyticStatement`).

Throughout, `π : Z → X` is an analytic modification (`IsAnalyticModification`: proper
holomorphic with a holomorphic inverse off nowhere dense analytic sets) from a compact complex
manifold `Z`, `θ` is a closed real `(1,1)`-form on `X` (a representative of `ξ = {θ}`), `D` an
effective divisor on `Z` (its invertible ideal sheaf `𝒪(-D) ⊆ 𝒪_Z`), `E` a smooth metric of
`𝒪(D)` (`DivisorMetric.IsDivisorMetric D E`: `ψ_E = log |s_D|²_h` is `log |g|²` plus a smooth
function for every local equation `g` of `D`, and `Θ_E` is its curvature form, so
`[D] = Θ_E + dd^c ψ_E` represents `{D} = {Θ_E}`), and `β` a Kähler form on `Z` with
`{β} = π^*ξ - c {D}` for a constant `c > 0`.

* `RelativeGlobalGenerationStatement` (`tok:relgen`): for some `N` (here `(N + 1) D`,
  `TranscendentalCore.divisorSuccNsmul D N`), every `z ∈ Z` has a neighbourhood `U` of `π z` such
  that the sections of `𝒪(-(N + 1) D)` over `π⁻¹ U` generate the stalk `𝒪(-(N+1)D)_z`.
  Sections of `𝒪(-D)` are holomorphic functions whose germs lie in `𝒪(-D)` at every point
  (`IsIdealSectionOn`).
* `PushforwardAnalyticStatement` (`tok:boucksom-pushforward`): for `c ∈ ℚ_{>0}`, every
  `θ`-psh potential `φ` on `X` with `φ ∘ π = c ψ_E + O(1)` has analytic singularities, i.e.
  lies in `𝒜(X, ξ)` (`TranscendentalCore.analyticCurrents θ`). The potential of
  `π_*(β + c[D])` (DRWNXZ Lemma 2.1, `tok:zariski-bijection`) is such a `φ`, with a smooth
  remainder.
* `WeaklyPseudoconvexL2GenerationStatement` (`relgen:l2-generation`): Nadel's generation
  theorem on weakly pseudoconvex open subsets `V` of a compact Kähler manifold `(Z, ω)`: there
  is `C > 0` (it absorbs the Ricci curvature of `ω` and the curvature of a cut-off pole weight)
  such that for every `q ∈ ℕ` and every weight `φ` with `dd^c φ ≥ C (q + 1) ω` on `V`, every
  germ `f ∈ 𝓘(φ)_z` (`|f|² e^{-φ}` integrable near `z`) is approximated at `z` to pole order
  `q` by a holomorphic `F` on `V` with `F ∈ 𝓘(φ)_y` for every `y ∈ V`:
  `∫_{near z} |F - f|² e^{-φ} |w - z|^{-2q} < ∞` in the coordinates of the preferred chart at
  `z`.

## Formal conventions

* `c {D}` with a real `c > 0` in `RelativeGlobalGenerationStatement` (the blueprint's
  `c = 1` after rescaling `ξ`, `β` and `D`; an effective `ℚ`-divisor is `c D` with `D`
  integral and `c ∈ ℚ_{>0}`).
* Weak pseudoconvexity (`IsWeaklyPseudoconvexOpen`): a chart-smooth function on `V`,
  plurisubharmonic in every chart, all of whose sublevel sets in `V` are compact.
* `dd^c φ ≥ K ω` on `V` is `IsThetaPshPotentialOn (-K • ω) φ V` (the project's convention
  for `PSH(V, θ)` with `θ = -K ω`).
* Integrability near a point is read in the preferred chart against Lebesgue measure
  (`multiplierIdeal 1 φ`, chart independent for a smooth change of coordinates).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

section Definitions

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- `s` is a section of the ideal sheaf `𝔞` over `V`: holomorphic on `V` with germ in `𝔞_y` at
every `y ∈ V`. For `𝔞 = 𝒪(-D)` these are the holomorphic sections of the line bundle `𝒪(-D)`
over `V`, viewed as holomorphic functions vanishing along `D`. -/
def IsIdealSectionOn (𝔞 : GermIdeal n M) (V : Set M) (s : M → ℂ) : Prop :=
  MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) s V ∧ ∀ y ∈ V, 𝔞.mem y s

/-- The sections `H⁰(V, 𝔞)` generate the stalk `𝔞_z`: every germ of `𝔞_z` is a finite
combination, with holomorphic coefficients, of sections of `𝔞` over `V`. -/
def SectionsGenerateAt (𝔞 : GermIdeal n M) (V : Set M) (z : M) : Prop :=
  ∀ g : M → ℂ, 𝔞.mem z g → IsInSpanAt (n := n) (IsIdealSectionOn 𝔞 V) z g

/-- `V` is a weakly pseudoconvex open set: it carries a smooth plurisubharmonic exhaustion
function `ψ` (chart-smooth and plurisubharmonic in every chart over `V`, with compact sublevel
sets `{y ∈ V : ψ y ≤ t}`). -/
def IsWeaklyPseudoconvexOpen (V : Set M) : Prop :=
  IsOpen V ∧ ∃ ψ : M → ℝ,
    (∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun w => ψ (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
    (∀ e : ComplexChart n M,
      PlurisubharmonicOn (fun w => (ψ (e.val.symm w) : EReal)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
    ∀ t : ℝ, IsCompact {y | y ∈ V ∧ ψ y ≤ t}

end Definitions

/-- **Relative global generation** (blueprint `tok:relgen`; the claim in the proof of DRWNXZ
Lemma 2.8). Let `π : Z → X` be an analytic modification from a compact complex manifold, `D`
an effective divisor on `Z` with a smooth metric `E`, and `β` a Kähler form on `Z` with
`{β} = π^*{θ} - c {D}`, `c > 0`. Then for some `N`, every `z ∈ Z` has an open neighbourhood `U`
of `π z` such that `H⁰(π⁻¹ U, 𝒪(-(N + 1) D))` generates `𝒪(-(N + 1) D)_z`. -/
def RelativeGlobalGenerationStatement : Prop :=
  ∀ (n : ℕ) (X Z : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [CompactSpace Z] (π : Z → X)
    (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z)
    (D : EffectiveDivisor n Z) (E : MeteredEffectiveQDivisor n Z) (c : ℝ),
    0 < c → β.val.IsKahler → DivisorMetric.IsDivisorMetric D E →
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1 θ) =
      RealBottChern.ofRepresentative β + c • RealBottChern.ofRepresentative E.curvature →
    ∃ N : ℕ, ∀ z : Z, ∃ U : Set X, IsOpen U ∧ π z ∈ U ∧
      SectionsGenerateAt (TranscendentalCore.divisorSuccNsmul D N).ideal (π ⁻¹' U) z

/-- **Pushforwards with analytic singularities** (blueprint `tok:boucksom-pushforward`; DRWNXZ
Lemma 2.8). In the setting of `RelativeGlobalGenerationStatement` with `c ∈ ℚ_{>0}` (the
current `β + c[D]`, `c D` an effective `ℚ`-divisor), every `θ`-psh potential `φ` on `X` with
`φ ∘ π = c ψ_E + O(1)` lies in `𝒜(X, {θ})`: it has analytic singularities. In particular
`π_*(β + c[D]) ∈ 𝒜(X, π_*{β + c[D]})`, the potential of the pushforward being such a `φ`. -/
def PushforwardAnalyticStatement : Prop :=
  ∀ (n : ℕ) (X Z : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [CompactSpace Z] (π : Z → X)
    (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z)
    (D : EffectiveDivisor n Z) (E : MeteredEffectiveQDivisor n Z) (c : ℚ),
    0 < c → β.val.IsKahler → DivisorMetric.IsDivisorMetric D E →
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1 θ) =
      RealBottChern.ofRepresentative β + (c : ℝ) • RealBottChern.ofRepresentative E.curvature →
    ∀ φ : X → EReal, IsThetaPshPotential θ.val φ →
      (∃ (b : Z → ℝ) (C : ℝ), (∀ z, |b z| ≤ C) ∧
        ∀ z, φ (π z) = ((c : ℝ) : EReal) * E.weight z + (b z : EReal)) →
      φ ∈ TranscendentalCore.analyticCurrents θ

/-- **`L²` generation on weakly pseudoconvex open sets** (blueprint `relgen:l2-generation`;
Demailly 2015, Corollary 5.3, applied as in Demailly, *Analytic methods*, Proposition 5.7 /
Theorem 6.27). Let `(Z, ω)` be a compact Kähler manifold. There is `C > 0` such that for every
`q ∈ ℕ`, every weakly pseudoconvex open `V ⊆ Z`, every `φ` with `dd^c φ ≥ C (q + 1) ω` on `V`,
every `z ∈ V` and every germ `f ∈ 𝓘(φ)_z`, there is a holomorphic `F` on `V` with
`F ∈ 𝓘(φ)_y` for all `y ∈ V` and `∫_{B(p, r)} |F - f|² e^{-φ} |w - p|^{-2q} < ∞` near
`p = e z` in the preferred chart `e` at `z`. -/
def WeaklyPseudoconvexL2GenerationStatement : Prop :=
  ∀ (n : ℕ) (Z : Type u) [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [CompactSpace Z] (omega : KahlerBackground n Z),
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (V : Set Z), IsWeaklyPseudoconvexOpen (n := n) V →
      ∀ φ : Z → EReal, IsThetaPshPotentialOn (-((C * ((q : ℝ) + 1)) • omega.form)).val φ V →
      ∀ z ∈ V, ∀ f : Z → ℂ, (multiplierIdeal (n := n) 1 φ).mem z f →
      ∃ F : Z → ℂ, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F V ∧
        (∀ y ∈ V, (multiplierIdeal (n := n) 1 φ).mem y F) ∧
        ∃ r : ℝ, 0 < r ∧
          ball ((complexChartAt (n := n) z).val z) r ⊆ (complexChartAt (n := n) z).val.target ∧
          (∫⁻ w in ball ((complexChartAt (n := n) z).val z) r,
            multiplierDensity (chartFunction φ (complexChartAt (n := n) z)) 1
                (fun w => F ((complexChartAt (n := n) z).val.symm w) -
                  f ((complexChartAt (n := n) z).val.symm w)) w /
              ENNReal.ofReal (‖w - (complexChartAt (n := n) z).val z‖ ^ (2 * q))) < ⊤

end SGPT.Okounkov.TranscendentalRelGen
