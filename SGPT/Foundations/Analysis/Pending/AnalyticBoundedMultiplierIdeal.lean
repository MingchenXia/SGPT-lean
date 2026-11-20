import SGPT.Foundations.Analysis.Pending.AnalyticWeightedGermGrowth
import SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

/-! # Literal bounded weighted holomorphic germs and analytic local inclusion -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal

open FirstPass FirstPass.HolomorphicIdealSheaves

noncomputable section

/-- Literal actual holomorphic germ membership with a finite positive bound
on its extended nonnegative weighted squared norm. Coherence is not assumed. -/
def boundedMultiplierIdeal {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (P : M → EReal) : GermIdeal n M where
  mem x h := HolomorphicAt n h x ∧ ∃ K : ℝ, 0 < K ∧
    ∀ᶠ y in 𝓝 x, multiplierDensity P 1 h y ≤ ENNReal.ofReal K

private theorem density_le_exp_of_log_bound {X : Type*}
    {P : X → EReal} {h : X → ℂ} {y : X} {D : ℝ}
    (hle : logNormSq (h y) ≤ P y + (D : EReal)) :
    multiplierDensity P 1 h y ≤ ENNReal.ofReal (Real.exp D) := by
  by_cases hh0 : h y = 0
  · simp [multiplierDensity, hh0]
  cases hPy : P y with
  | bot =>
    have hbot : logNormSq (h y) = ⊥ := le_bot_iff.mp (by simpa [hPy] using hle)
    exact False.elim (hh0 ((logNormSq_eq_bot_iff _).mp hbot))
  | top => simp [multiplierDensity, hPy]
  | coe t =>
    have hr : Real.log (‖h y‖ ^ 2) ≤ t + D := by
      rw [logNormSq_of_ne_zero hh0, hPy, ← EReal.coe_add] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hsq : 0 < ‖h y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh0)
    have hnorm : ‖h y‖ ^ 2 ≤ Real.exp (t + D) := by
      simpa only [Real.exp_log hsq] using Real.exp_le_exp.mpr hr
    have hreal : ‖h y‖ ^ 2 * Real.exp (-t) ≤ Real.exp D := by
      calc ‖h y‖ ^ 2 * Real.exp (-t) ≤ Real.exp (t + D) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    simpa only [multiplierDensity, hPy, multiplierWeight_coe, one_mul,
      ← ENNReal.ofReal_mul (sq_nonneg (‖h y‖))] using ENNReal.ofReal_le_ofReal hreal

/-- A genuine logarithmic analytic type and genuine local weighted L2
membership internally give literal bounded multiplier-ideal membership. -/
theorem mem_boundedMultiplierIdeal_of_analytic_weighted_integrable
    {n N : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    {P : ComplexModel n → EReal} {g : Fin N → ComplexModel n → ℂ}
    {x : ComplexModel n} {c p q : ℝ} (htype : LogarithmicTypeAt P c g x)
    (hp : 0 < p) (hqp : (n : ℝ) ≤ (q - p) * c)
    {h : ComplexModel n → ℂ} (hf : MultiplierIntegrableAt P q h x volume) :
    (boundedMultiplierIdeal (n := n) (fun y => (p : EReal) * P y)).mem x h := by
  obtain ⟨hc, hg, b, hb, heq⟩ := htype
  obtain ⟨M, hM, hMb⟩ := hb
  obtain ⟨hq, B, hB, hxB, hh, hInt⟩ := hf
  have hupper : ∀ᶠ y in 𝓝 x, P y ≤ (c : EReal) * generatorLog g y + (M : EReal) := by
    filter_upwards [heq, hMb] with y hy hby
    rw [hy]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp hby).2)
  obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp hupper
  have hfinite : (∫⁻ z in B ∩ W,
      ENNReal.ofReal (‖h z‖ ^ 2) * multiplierWeight q (P z)) ≠ ⊤ := by
    simpa only [multiplierDensity] using (hInt.mono inter_subset_left).2.ne
  have hae : p * c ≤ q * c - (n : ℝ) := by nlinarith [hqp]
  obtain ⟨D, hlog⟩ := AnalyticWeightedGermGrowth.exists_log_weight_bound_eventually hg
    (hB.inter hW) ⟨hxB, hxW⟩ (hh.mono inter_subset_left) hq hc (mul_pos hp hc) hae
    (fun z hz => hWsub hz.2) hfinite
  have hlogP : ∀ᶠ y in 𝓝 x,
      logNormSq (h y) ≤ (p : EReal) * P y + ((D + p * M : ℝ) : EReal) := by
    filter_upwards [hlog, heq, hMb] with y hly hPy hby
    apply hly.trans
    rw [hPy]
    cases hgy : generatorLog g y with
    | bot => simp only [EReal.coe_mul_bot_of_pos hp,
        EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_bot_of_pos (mul_pos hp hc),
        EReal.bot_add, le_refl]
    | top => exact False.elim (generatorLog_ne_top g y hgy)
    | coe t =>
      simp only [← EReal.coe_mul, ← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      nlinarith [(abs_le.mp hby).1]
  refine ⟨?_, Real.exp (D + p * M), Real.exp_pos _, ?_⟩
  · unfold HolomorphicAt
    filter_upwards [hB.mem_nhds hxB] with y hy
    exact ((hh y hy).differentiableAt (hB.mem_nhds hy)).mdifferentiableAt
  · exact hlogP.mono fun y hy => density_le_exp_of_log_bound hy

end

end SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal
