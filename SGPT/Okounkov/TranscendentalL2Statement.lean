import SGPT.Okounkov.TranscendentalRelGenWeight

/-!
# `L²` generation over a coordinate ball of the base of a modification: statement

Plan `tok/RELGEN2/PLAN.md` §0 (blueprint `l2:modification-generation`, chapter
`claude-tok-l2`).

RELGEN reduced relative global generation (`tok:relgen`) to
`WeaklyPseudoconvexL2GenerationStatement` (`relgen:l2-generation`): Nadel's `L²` generation with a
point pole on **every** weakly pseudoconvex open subset `V` of a compact Kähler manifold, for
**every** weight with `dd^c φ ≥ C (q + 1) ω`. The proof of `tok:relgen`
(`TranscendentalRelGenGeneration.relativeGlobalGeneration_of_l2Generation`) uses it only for

* the preimage `V = π⁻¹(d⁻¹ B(p, r))` of a coordinate ball of the base of the modification
  `π : Z → X`, with `ω = β`;
* the weight `φ_N = (N + 1) ψ_E + ((N + 1)/c) (ρ ∘ d ∘ π + h)` (`relgenWeight`), with
  `dd^c φ_N ≥ ((N + 1)/c) β`;

and it needs the holomorphic function `F` only on `π⁻¹ U` for SOME neighbourhood `U` of `π z`.

`ModificationL2GenerationStatement` is this special case. It is implied by RELGEN's statement
(`TranscendentalL2Bridge.modificationL2Generation_of_weaklyPseudoconvex`) and implies relative
global generation (`TranscendentalL2Bridge.relativeGlobalGeneration_of_modificationL2Generation`),
hence `PushforwardAnalyticStatement` and LIFT's item 3. It is the statement proved by the route of
the plan (flat Hörmander on the complement of a hypersurface in the ball `B(p, r)`, files
`TranscendentalL2Hormander`, `TranscendentalL2Complement`, `TranscendentalL2Extension`).

Formal conventions are those of `TranscendentalRelGenStatement`: the class condition
`{β} = π^*{θ} - c{D}` is given by a chart-smooth `h` with `β + c Θ_E = π^*θ + dd^c h`
(`hheq`, as in `TranscendentalRelGenWeight.isThetaPshPotentialOn_weight`); `ρ` is a smooth
potential of `θ` on the ball `B(p, r)` of the chart `d`, `closedBall p r ⊆ d.target`; multiplier
ideals and the pole integral are read in the preferred charts.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalRelGen

/-- **`L²` generation over a coordinate ball of the base of a modification** (blueprint
`l2:modification-generation`; the case of `relgen:l2-generation` used by `tok:relgen`). Let
`π : Z → X` be an analytic modification from a compact complex manifold, `β` a Kähler form on
`Z`, `E` a smooth metric of an effective divisor `D`, `c > 0` and `h` chart-smooth with
`β + c Θ_E = π^*θ + dd^c h`. There is `C > 0` such that for all `q, N` with
`C (q + 1) ≤ (N + 1)/c`, every chart `d` of `X`, every ball `B(p, r)` with closure in its target
carrying a smooth potential `ρ` of `θ`, every `z ∈ V = π⁻¹(d⁻¹ B(p, r))` and every germ
`f ∈ 𝓘(φ_N)_z` (`φ_N = relgenWeight π E d ρ h N ((N+1)/c)`), there are an open `U ∋ π z` inside
`d⁻¹ B(p, r)` and a holomorphic `F` on `π⁻¹ U` with `F ∈ 𝓘(φ_N)_y` for every `y ∈ π⁻¹ U` and
`∫_{B(e z, r')} |F - f|² e^{-φ_N} |w - e z|^{-2q} < ∞` in the preferred chart `e` at `z`. -/
def ModificationL2GenerationStatement : Prop :=
  ∀ (n : ℕ) (X Z : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [CompactSpace Z] (π : Z → X)
    (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z)
    (D : EffectiveDivisor n Z) (E : MeteredEffectiveQDivisor n Z) (c : ℝ) (h : Z → ℝ),
    0 < c → β.val.IsKahler → DivisorMetric.IsDivisorMetric D E → ChartSmooth (n := n) h →
    (∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ.1 θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z) →
    ∃ C : ℝ, 0 < C ∧ ∀ q N : ℕ, C * ((q : ℝ) + 1) ≤ ((N : ℝ) + 1) / c →
      ∀ (d : ComplexChart n X) (p : ComplexModel n) (r : ℝ) (ρ : ComplexModel n → ℝ),
        closedBall p r ⊆ d.val.target → IsSmoothLocalPotential θ.val d (ball p r) ρ →
      ∀ z ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r), ∀ f : Z → ℂ,
        (multiplierIdeal (n := n) 1 (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c))).mem z f →
      ∃ U : Set X, IsOpen U ∧ π z ∈ U ∧ U ⊆ d.val.source ∩ d.val ⁻¹' ball p r ∧
      ∃ F : Z → ℂ, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F (π ⁻¹' U) ∧
        (∀ y ∈ π ⁻¹' U,
          (multiplierIdeal (n := n) 1 (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c))).mem y F) ∧
        ∃ r' : ℝ, 0 < r' ∧
          ball ((complexChartAt (n := n) z).val z) r' ⊆ (complexChartAt (n := n) z).val.target ∧
          (∫⁻ w in ball ((complexChartAt (n := n) z).val z) r',
            multiplierDensity (chartFunction (relgenWeight π E d ρ h N (((N : ℝ) + 1) / c))
                (complexChartAt (n := n) z)) 1
                (fun w => F ((complexChartAt (n := n) z).val.symm w) -
                  f ((complexChartAt (n := n) z).val.symm w)) w /
              ENNReal.ofReal (‖w - (complexChartAt (n := n) z).val z‖ ^ (2 * q))) < ⊤

end SGPT.Okounkov.TranscendentalL2
