import SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallLocalization
import SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallEstimate
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false

/-! # Actual weighted integrability forces positive-power analytic pole growth -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.AnalyticWeightedPoleGrowth

open FirstPass

noncomputable section

/-- A genuine finite weighted integral produces a uniform positive-power
bound near the analytic pole; regularized balls and all constants are internal. -/
theorem exists_pos_local_power_bound
    {n N : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    {g : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}
    (hg : HolomorphicGeneratorsAt g x) (hpole : generatorNormSq g x = 0)
    {B : Set (ComplexModel n)} (hB : IsOpen B) (hxB : x ∈ B)
    {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h B)
    {P : ComplexModel n → EReal} {q c b : ℝ}
    (hq : 0 < q) (hc : 0 < c) (he : 0 < q * c - (n : ℝ))
    (hP : ∀ z ∈ B, P z ≤ (c : EReal) * generatorLog g z + (b : EReal))
    (hfinite : (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧ U ⊆ B ∧
      ∀ y ∈ U, ‖h y‖ ^ 2 ≤ C * generatorNormSq g y ^ (q * c - (n : ℝ)) := by
  obtain ⟨U, hU, hxU, hUB, η₀, A, hη₀, hA, hballs⟩ :=
    AnalyticRegularizedBallLocalization.exists_uniform_regularized_balls hg hpole hB hxB
  let D : ℝ := Real.exp (q * b) * A ^ (q * c) *
    (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)).toReal /
    (volume (ball (0 : ComplexModel n) 1)).toReal
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := D + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, U, hU, hxU, hUB, ?_⟩
  intro y hy
  have hreg : ∀ η ∈ Ioo 0 η₀,
      ‖h y‖ ^ 2 ≤ C * (generatorNormSq g y + η ^ 2) ^ (q * c - (n : ℝ)) := by
    intro η hη
    obtain ⟨hS, hsub, hgen⟩ := hballs y hy η hη
    have hbound := AnalyticRegularizedBallEstimate.norm_sq_le_regularized_power_bound
      hB hh g hq hc hA hS hsub
      (fun z hz => hP z (hsub (ball_subset_closedBall hz))) hgen hfinite
    change ‖h y‖ ^ 2 ≤ D * (generatorNormSq g y + η ^ 2) ^ (q * c - (n : ℝ)) at hbound
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right
    · dsimp [C]; linarith
    · exact Real.rpow_nonneg hS.le _
  have hcont : Continuous (fun η : ℝ =>
      C * (generatorNormSq g y + η ^ 2) ^ (q * c - (n : ℝ))) :=
    continuous_const.mul ((Real.continuous_rpow_const he.le).comp
      (continuous_const.add (continuous_id.pow 2)))
  have hlim : Tendsto (fun η : ℝ =>
      C * (generatorNormSq g y + η ^ 2) ^ (q * c - (n : ℝ))) (𝓝[>] (0 : ℝ))
      (𝓝 (C * generatorNormSq g y ^ (q * c - (n : ℝ)))) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmallη : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), η ∈ Ioo 0 η₀ := Ioo_mem_nhdsGT hη₀
  exact ge_of_tendsto hlim (hsmallη.mono fun η hη => hreg η hη)

end

end SGPT.Foundations.Analysis.Pending.AnalyticWeightedPoleGrowth
