import SGPT.Foundations.Analysis.Pending.AnalyticWeightedPoleGrowth

set_option autoImplicit false

/-! # Actual all-point weighted analytic germ growth -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticWeightedGermGrowth

open FirstPass

noncomputable section

variable {n N : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- Genuine weighted integrability gives positive-power generator growth
at every center, internally covering both poles and nonpoles. -/
theorem exists_pos_power_bound_eventually
    {g : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}
    (hg : HolomorphicGeneratorsAt g x)
    {B : Set (ComplexModel n)} (hB : IsOpen B) (hxB : x ∈ B)
    {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h B)
    {P : ComplexModel n → EReal} {q c b a : ℝ}
    (hq : 0 < q) (hc : 0 < c) (ha : 0 < a) (hae : a ≤ q * c - (n : ℝ))
    (hP : ∀ z ∈ B, P z ≤ (c : EReal) * generatorLog g z + (b : EReal))
    (hfinite : (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
      ‖h y‖ ^ 2 ≤ C * generatorNormSq g y ^ a := by
  classical
  obtain ⟨D, hD, hxD, hgD⟩ := hg
  have hcontg (i : Fin N) : ContinuousAt (g i) x :=
    ((contDiffOn_of_differentiableOn_complex (hgD i) hD).contDiffAt
      (hD.mem_nhds hxD)).continuousAt
  have hcontF : ContinuousAt (generatorNormSq g) x := by
    unfold generatorNormSq
    exact tendsto_finsetSum _ fun i _ => (hcontg i).norm.pow 2
  by_cases hpole : generatorNormSq g x = 0
  · obtain ⟨C, hC, U, hU, hxU, _, hbound⟩ :=
      AnalyticWeightedPoleGrowth.exists_pos_local_power_bound
        ⟨D, hD, hxD, hgD⟩ hpole hB hxB hh hq hc (ha.trans_le hae) hP hfinite
    have hFone : ∀ᶠ y in 𝓝 x, generatorNormSq g y < 1 :=
      hcontF.eventually_lt continuousAt_const (by rw [hpole]; norm_num)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hU.mem_nhds hxU, hFone] with y hy hFy
    apply (hbound y hy).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' (generatorNormSq_nonneg g y) hFy.le ha.le hae) hC.le
  · have hFx : 0 < generatorNormSq g x :=
      lt_of_le_of_ne (generatorNormSq_nonneg g x) (by intro h; exact hpole h.symm)
    let L : ℝ := generatorNormSq g x / 2
    let M : ℝ := ‖h x‖ ^ 2 + 1
    have hL : 0 < L := by dsimp [L]; positivity
    have hM : 0 < M := by dsimp [M]; positivity
    have hpow : 0 < L ^ a := Real.rpow_pos_of_pos hL _
    have hlower : ∀ᶠ y in 𝓝 x, L < generatorNormSq g y :=
      continuousAt_const.eventually_lt hcontF (by dsimp [L]; linarith)
    have hconth : ContinuousAt (fun y => ‖h y‖ ^ 2) x :=
      (hh.continuousOn.continuousAt (hB.mem_nhds hxB)).norm.pow 2
    have hupper : ∀ᶠ y in 𝓝 x, ‖h y‖ ^ 2 < M :=
      hconth.eventually_lt continuousAt_const (by dsimp [M]; linarith)
    refine ⟨M / L ^ a, div_pos hM hpow, ?_⟩
    filter_upwards [hlower, hupper] with y hFy hhy
    calc ‖h y‖ ^ 2 ≤ M := hhy.le
      _ = (M / L ^ a) * L ^ a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hL.le hFy.le ha.le) (div_pos hM hpow).le

/-- The internally produced power bound gives a literal extended-real
bounded holomorphic weight, including all poles and generator zeros. -/
theorem exists_log_weight_bound_eventually
    {g : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}
    (hg : HolomorphicGeneratorsAt g x)
    {B : Set (ComplexModel n)} (hB : IsOpen B) (hxB : x ∈ B)
    {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h B)
    {P : ComplexModel n → EReal} {q c b a : ℝ}
    (hq : 0 < q) (hc : 0 < c) (ha : 0 < a) (hae : a ≤ q * c - (n : ℝ))
    (hP : ∀ z ∈ B, P z ≤ (c : EReal) * generatorLog g z + (b : EReal))
    (hfinite : (∫⁻ z in B, ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤) :
    ∃ D : ℝ, ∀ᶠ y in 𝓝 x,
      logNormSq (h y) ≤ (a : EReal) * generatorLog g y + (D : EReal) := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_power_bound_eventually hg hB hxB hh hq hc ha hae hP hfinite
  refine ⟨Real.log C, hbound.mono fun y hy => ?_⟩
  rw [logNormSq, generatorLog_eq_log_sum]
  calc ENNReal.log (ENNReal.ofReal (‖h y‖ ^ 2))
      ≤ ENNReal.log (ENNReal.ofReal (C * generatorNormSq g y ^ a)) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hy)
    _ = ENNReal.log (ENNReal.ofReal C * ENNReal.ofReal (generatorNormSq g y) ^ a) := by
      rw [ENNReal.ofReal_mul hC.le,
        ENNReal.ofReal_rpow_of_nonneg (generatorNormSq_nonneg g y) ha.le]
    _ = _ := by
      rw [ENNReal.log_mul_add, ENNReal.log_rpow, ENNReal.log_ofReal_of_pos hC]
      simp only [generatorNormSq, add_comm]

end

end SGPT.Foundations.Analysis.Pending.AnalyticWeightedGermGrowth
