import SGPT.Okounkov.TranscendentalRelGenDivisibility
import SGPT.Okounkov.TranscendentalRelGenPushforward

/-!
# Relative global generation and pushforwards with analytic singularities

Package RELGEN of the transcendental Okounkov route (blueprint nodes `tok:ext-l2`, `tok:relgen`,
`tok:boucksom-pushforward`; chapter `claude-tok-relgen`). The statements are in
`SGPT.Okounkov.TranscendentalRelGenStatement`.

Proved here, from the single analytic input `WeaklyPseudoconvexL2GenerationStatement`
(`relgen:l2-generation`, Nadel's `L²` generation on weakly pseudoconvex open subsets of a
compact Kähler manifold, a consequence of Hörmander's estimate `tok:ext-l2`):

* `relativeGlobalGeneration_of_l2Generation'`: relative global generation (`tok:relgen`);
* `pushforwardAnalyticStatement_of_l2Generation`: pushforwards with analytic singularities
  (`tok:boucksom-pushforward`, DRWNXZ Lemma 2.8).

Unconditional ingredients: holomorphic descent along modifications
(`exists_holomorphic_descent`), generators near a fibre (`exists_fibre_generators`), the weight
on the preimage of a coordinate ball (`isThetaPshPotentialOn_weight`,
`isWeaklyPseudoconvexOpen_preimage_ball`), `L²` divisibility (`l2DivisibilityStatement`) and
the point pole (`eq_zero_of_lintegral_div_norm_pow_ne_top`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- **Pushforwards with analytic singularities** (blueprint `tok:boucksom-pushforward`, DRWNXZ
Lemma 2.8), from the `L²` generation theorem on weakly pseudoconvex manifolds
(`relgen:l2-generation`). -/
theorem pushforwardAnalyticStatement_of_l2Generation
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) : PushforwardAnalyticStatement.{u} :=
  pushforwardAnalyticStatement_of_relativeGlobalGeneration
    (relativeGlobalGeneration_of_l2Generation' hL2)

/-- **The pushforward `π_*(β + c[D])` has analytic singularities** (DRWNXZ Lemma 2.8, blueprint
`tok:boucksom-pushforward`), in the form in which the pushforward potential arises: `φ ∘ π =
c ψ_E + h` with `h` chart-smooth on the compact manifold `Z`. Conditional on the `L²` generation
theorem (`relgen:l2-generation`). -/
theorem pushforward_mem_analyticCurrents (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u})
    {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [CompactSpace Z] {π : Z → X}
    (hπ : IsAnalyticModification (n := n) π) {θ : ClosedRealOneOneForm n X}
    {β : ClosedRealOneOneForm n Z} {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    {c : ℚ} (hc : 0 < c) (hβ : β.val.IsKahler) (hE : DivisorMetric.IsDivisorMetric D E)
    (hclass : RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1 θ) =
      RealBottChern.ofRepresentative β + (c : ℝ) • RealBottChern.ofRepresentative E.curvature)
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hφπ : ∀ z, φ (π z) = ((c : ℝ) : EReal) * E.weight z + (h z : EReal)) :
    φ ∈ TranscendentalCore.analyticCurrents θ := by
  have hcont : Continuous h := by
    rw [← continuousOn_univ]
    exact continuousOn_of_chartSmooth isOpen_univ fun e => (hh e).mono Set.inter_subset_left
  obtain ⟨C, hC⟩ := (isCompact_univ.image hcont).isBounded.exists_norm_le
  exact pushforwardAnalyticStatement_of_l2Generation hL2 n X Z π hπ θ β D E c hc hβ hE hclass
    φ hφ ⟨h, C, fun z => by simpa [Real.norm_eq_abs] using hC _ ⟨z, Set.mem_univ _, rfl⟩, hφπ⟩

end SGPT.Okounkov.TranscendentalRelGen
