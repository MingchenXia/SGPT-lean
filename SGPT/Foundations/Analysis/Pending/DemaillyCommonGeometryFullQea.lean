import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryMonotonicity

set_option autoImplicit false

/-! # Uniform actual geometry for all full Demailly row approximations -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFullQea
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation DemaillyApproximationSequence
  DemaillyApproximationAnalyticType QuantitativeRegularizationFixedCover
  QuasiEquisingularApproximationDemailly

noncomputable section

/-- One cover, one local-potential family and all correction constants are
chosen before every genuine input. Each literal row is a full QEA. -/
theorem exists_common_geometry_full_qea
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) :
    ∃ (F : FixedChartCover n M) (ρ : F.t → ComplexModel n → ℝ) (D Cχ : ℝ),
      0 ≤ D ∧ 0 < Cχ ∧
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
      (∀ j, (ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j)
        + Cχ • omega.form).val.IsSemipositive) ∧
      (∀ k : ℕ, 0 < (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ) ∧
      ∀ u : M → EReal, IsThetaPshPotential θ.val u →
        (∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
          F.branch ρ u (2 * m) j y ≤ F.branch ρ u m j y + ((D / (m : ℝ) : ℝ) : EReal)) ∧
        IsQuasiEquisingularApproximation omega θ u
          (fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ)
          (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4))) ∧
        ∀ k, HasAnalyticSingularitiesOfType (n := n)
          (DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) k)
          (((2 ^ k : ℕ) : ℚ)⁻¹) (multiplierIdeal (n := n) ((2 ^ k : ℕ) : ℝ) u) := by
  obtain ⟨F⟩ := exists_fixedChartCover (Z := M) hn
  obtain ⟨ρ, hρ⟩ := F.exists_potentials θ
  obtain ⟨D, hD0, hD⟩ := exists_doublingConst F
  obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun j => ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j))
  have hCB := F.CB_nonneg
  refine ⟨F, ρ, D, Cχ, hD0, hCχ, hρ, hsemi, fun k => by positivity, ?_⟩
  intro u hu
  have hdouble := hD θ.val u hu.1 ρ hρ
  refine ⟨hdouble, ⟨hu, ⟨fun k => by positivity, fun a b hab => ?_, ?_⟩,
    fun k => isThetaPshPotential_seq hn F omega hsemi hu hρ _ k,
    fun k => (hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k).hasManifoldAnalyticSingularityType,
    ⟨fun x => antitone_seq F hdouble x, fun x => tendsto_seq F hu.1 hρ _ x⟩, ?_⟩,
    fun k => hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k⟩
  · refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by linarith)
      (by positivity) ?_) hCχ.le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hab
  · have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h2 := h1.const_mul ((F.CB + 1) * Cχ)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    push_cast
    field_simp
  · intro c d hc hcd
    have hdc : 0 < d - c := sub_pos.mpr hcd
    have hK : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
      have hk := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
      exact hk.congr fun k => by push_cast; rfl
    filter_upwards [hK.eventually_ge_atTop (c * d / (d - c))] with k hk
    have hmcd : c * d ≤ ((2 ^ k : ℕ) : ℝ) * (d - c) := (div_le_iff₀ hdc).mp hk
    have hle : ∀ x, u x ≤ DemaillyApproximationSequence.seq F ρ u (2 * (D + 1 / 4)) k x :=
      fun x => by
        rw [← iInf_seq F hu.1 hρ hdouble x]
        exact iInf_le _ k
    exact multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType hu.1.quasiPlurisubharmonic
      hle (by positivity) (hasAnalyticSingularitiesOfType_seq hn F hu hρ _ k) hc hcd hmcd

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFullQea
