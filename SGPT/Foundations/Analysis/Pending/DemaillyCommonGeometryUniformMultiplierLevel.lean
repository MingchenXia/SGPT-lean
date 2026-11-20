import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFullQea

set_option autoImplicit false

/-! # Strict multiplier level chosen before every fixed-geometry row -/

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryUniformMultiplierLevel
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.QuasiEquisingularApproximation
  DemaillyApproximationSequence DemaillyApproximationAnalyticType
  QuantitativeRegularizationFixedCover QuasiEquisingularApproximationDemailly

noncomputable section

/-- The strict dyadic multiplier threshold is chosen before every
actual input row in the same geometry. -/
theorem exists_uniform_multiplier_level
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (hn : 0 < n) (F : FixedChartCover n M) {θ : ClosedRealOneOneForm n M}
    {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j)) {D : ℝ}
    (hdouble : ∀ u : M → EReal, IsThetaPshPotential θ.val u →
      ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
        F.branch ρ u (2 * m) j y ≤ F.branch ρ u m j y + ((D / (m : ℝ) : ℝ) : EReal))
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∃ L : ℕ, ∀ u : M → EReal, IsThetaPshPotential θ.val u → ∀ k : ℕ, L ≤ k →
      MultiplierIdealIncluded (n := n)
        (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) k) d u c := by
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hpow : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
    have hk := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
    exact hk.congr fun k => by push_cast; rfl
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hpow.eventually_ge_atTop (c * d / (d - c)))
  refine ⟨L, ?_⟩
  intro u hu k hk
  have hmcd : c * d ≤ ((2 ^ k : ℕ) : ℝ) * (d - c) :=
    (div_le_iff₀ hdc).mp (hL k hk)
  have hle : ∀ x, u x ≤ DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) k x :=
    fun x => by
      rw [← iInf_seq F hu.1 hρ (hdouble u hu) x]
      exact iInf_le _ k
  exact multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType hu.1.quasiPlurisubharmonic
    hle (by positivity) (hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k) hc hcd hmcd

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryUniformMultiplierLevel
