import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFullQea
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination

set_option autoImplicit false

/-! # Uniform actual full rows in one enlarged background -/

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFixedBackgroundRows
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.QuasiEquisingularApproximation
  DemaillyApproximationSequence QuantitativeRegularizationFixedCover
  DemaillyCommonGeometryFullQea

noncomputable section

/-- One genuine common tail works for every input in the original
background and exports every full QEA clause in a fixed enlargement. -/
theorem exists_common_fixed_background_full_rows
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) :
    ∃ (F : FixedChartCover n M) (ρ : F.t → ComplexModel n → ℝ) (D : ℝ) (K : ℕ),
      0 ≤ D ∧
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
      ∀ u : M → EReal, IsThetaPshPotential θ.val u →
        (∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
          F.branch ρ u (2 * m) j y ≤ F.branch ρ u m j y + ((D / (m : ℝ) : ℝ) : EReal)) ∧
        IsQuasiEquisingularApproximation omega (θ + omega.form) u (fun _ => 0)
          (fun j => DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K)) ∧
        (∀ j, IsThetaPshPotential (θ + (1 / 2 : ℝ) • omega.form).val
          (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K))) ∧
        ∀ j, HasAnalyticSingularitiesOfType (n := n)
          (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K))
          (((2 ^ (j + K) : ℕ) : ℚ)⁻¹)
          (multiplierIdeal (n := n) ((2 ^ (j + K) : ℕ) : ℝ) u) := by
  obtain ⟨F, ρ, D, Cχ, hD, _hCχ, hρ, _hsemi, _hεpos, hall⟩ :=
    exists_common_geometry_full_qea hn omega θ
  let ε : ℕ → ℝ := fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h2 := h1.const_mul ((F.CB + 1) * Cχ)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    dsimp only [ε]
    push_cast
    field_simp
  have hsmall : ∀ᶠ k in atTop, ε k < 1 / 2 :=
    hεlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hsmall
  have htail : Tendsto (fun j : ℕ => j + K) atTop atTop := tendsto_add_atTop_nat K
  refine ⟨F, ρ, D, K, hD, hρ, ?_⟩
  intro u hu
  obtain ⟨hdouble, happ, htype⟩ := hall u hu
  have hhalf (j : ℕ) : IsThetaPshPotential (θ + (1 / 2 : ℝ) • omega.form).val
      (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K)) := by
    have hs : ((1 / 2 - ε (j + K)) • omega.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul omega.isSemipositive
        (sub_nonneg.mpr (hK (j + K) (Nat.le_add_left K j)).le)
    have hform : θ + ε (j + K) • omega.form +
        (1 / 2 - ε (j + K)) • omega.form = θ + (1 / 2 : ℝ) • omega.form := by module
    have hstage : IsThetaPshPotential (θ + ε (j + K) • omega.form).val
        (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K)) :=
      happ.term (j + K)
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hstage hs
  have hterm (j : ℕ) : IsThetaPshPotential (θ + omega.form).val
      (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) (j + K)) := by
    have hform : θ + (1 / 2 : ℝ) • omega.form + (1 / 2 : ℝ) • omega.form =
        θ + omega.form := by module
    simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hhalf j) (KahlerDomination.isSemipositive_smul omega.isSemipositive
        (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have htarget : IsThetaPshPotential (θ + omega.form).val u := by
    simpa only [one_smul] using LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (zero_le_one : (0 : ℝ) ≤ 1))
  refine ⟨hdouble, ⟨htarget, ⟨fun _ => le_rfl, antitone_const, tendsto_const_nhds⟩,
    fun j => by simpa only [zero_smul, add_zero] using hterm j,
    fun j => happ.term_hasAnalyticSingularityType (j + K),
    ⟨fun x i j hij => happ.term_antitone x (Nat.add_le_add_right hij K),
      fun x => (happ.term_tendsto x).comp htail⟩, ?_⟩, hhalf, fun j => htype (j + K)⟩
  intro c d hc hcd
  exact htail.eventually (happ.eventually_multiplierIdealIncluded hc hcd)

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFixedBackgroundRows
