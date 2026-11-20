import SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionLocalIntegrability
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

set_option autoImplicit false

/-! # A genuine weighted finite log family gives reverse original multiplier membership -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawWeightedLogFamilyReverseIntegrability

open FirstPass IEquivalentMax ActualMultiplierAdditionWeightBound

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- A stronger literal finite-log source ideal and actual original weighted
family imply the original raw multiplier membership. -/
theorem multiplierIntegrableAt_of_finite_weighted_log_family
    {φ : E → EReal} {x : E} {c δ k : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hkbound : 2 * (c * (1 + δ)) / δ ≤ k) {N : ℕ} {g : Fin N → E → ℂ}
    {f : E → ℂ}
    (hsource : MultiplierIntegrableAt (generatorLog g) (c * (1 + δ) / k) f x μ)
    {O : Set E} (hO : IsOpen O) (hxO : x ∈ O)
    (hφ : QuasiPlurisubharmonicOn φ O)
    (hgL2 : ∀ i, WeightedL2On φ k (g i) O μ) :
    MultiplierIntegrableAt φ c f x μ := by
  have hk : 0 < k := lt_of_lt_of_le (by positivity) hkbound
  let U : E → EReal := fun y => ((k⁻¹ : ℝ) : EReal) * generatorLog g y
  have hUtop (y : E) : U y ≠ ⊤ := by
    dsimp only [U]
    intro ht
    rcases (EReal.mul_eq_top _ _).mp ht with h | h | h | h
    · exact EReal.coe_ne_bot _ h.1
    · exact not_lt_of_ge (EReal.coe_nonneg.mpr (inv_nonneg.mpr hk.le)) h.1
    · exact EReal.coe_ne_top _ h.1
    · exact generatorLog_ne_top g y h.2
  have hweight (y : E) : multiplierWeight (c * (1 + δ)) (U y) =
      multiplierWeight (c * (1 + δ) / k) (generatorLog g y) := by
    unfold multiplierWeight
    dsimp only [U]
    rw [← mul_assoc, ← EReal.coe_mul, ← div_eq_mul_inv]
  have hexp (y : E) : EReal.exp ((k : EReal) * U y) =
      ∑ i, ENNReal.ofReal (‖g i y‖ ^ 2) := by
    have heq : (k : EReal) * U y = generatorLog g y := by
      dsimp only [U]
      rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hk.ne', EReal.coe_one, one_mul]
    rw [heq, generatorLog_eq_log_sum, ENNReal.exp_log]
    exact ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg ‖g i y‖
  obtain ⟨-, W1, hW1, hxW1, hfhol, hfL2⟩ := hsource
  have hfc : ContinuousAt f x := (hfhol.differentiableAt (hW1.mem_nhds hxW1)).continuousAt
  have hbound : ∀ᶠ y in 𝓝 x, ‖f y‖ < ‖f x‖ + 1 :=
    hfc.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨W2, hW2sub, hW2, hxW2⟩ := mem_nhds_iff.mp hbound
  let W := W1 ∩ O ∩ W2 ∩ Metric.ball x 1
  have hW : IsOpen W := ((hW1.inter hO).inter hW2).inter Metric.isOpen_ball
  have hxW : x ∈ W := ⟨⟨⟨hxW1, hxO⟩, hxW2⟩, Metric.mem_ball_self one_pos⟩
  have hWW1 : W ⊆ W1 := fun _ hy => hy.1.1.1
  have hWO : W ⊆ O := fun _ hy => hy.1.1.2
  have hμW : μ W ≠ ⊤ := ((measure_mono (fun _ hy => hy.2)).trans_lt
    (measure_ball_lt_top (μ := μ))).ne
  let K : ℝ≥0∞ := ENNReal.ofReal ((‖f x‖ + 1) ^ 2)
  have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ y ∈ W, multiplierDensity φ c f y ≤
      multiplierDensity (generatorLog g) (c * (1 + δ) / k) f y + K +
        K * ∑ i, multiplierDensity φ k (g i) y + K := by
    intro y hy
    have hfy : ENNReal.ofReal (‖f y‖ ^ 2) ≤ K := ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (hW2sub hy.1.2).le 2)
    have hw := multiplierWeight_le_sum_add_ratios hc hδ hkbound
      ((hφ y (hWO hy)).ne_top) (by simp : (0 : EReal) ≠ ⊤) (hUtop y)
      (by simp : (0 : EReal) ≠ ⊤)
    simp only [add_zero, mul_zero, EReal.exp_zero, multiplierWeight, neg_zero, one_mul] at hw
    change multiplierWeight c (φ y) ≤
      multiplierWeight (c * (1 + δ)) (U y) + 1 +
        EReal.exp ((k : EReal) * U y) * multiplierWeight k (φ y) + 1 at hw
    rw [hweight, hexp] at hw
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y) ≤
          ENNReal.ofReal (‖f y‖ ^ 2) *
            (multiplierWeight (c * (1 + δ) / k) (generatorLog g y) + 1 +
              (∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) * multiplierWeight k (φ y) + 1) := by
                gcongr
      _ ≤ ENNReal.ofReal (‖f y‖ ^ 2) *
            multiplierWeight (c * (1 + δ) / k) (generatorLog g y) + K +
              K * ((∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) * multiplierWeight k (φ y)) + K := by
                rw [mul_add, mul_add, mul_add, mul_one]
                exact add_le_add (add_le_add (add_le_add le_rfl hfy)
                  (mul_le_mul' hfy le_rfl)) hfy
      _ = _ := by rw [Finset.sum_mul]
  refine ⟨hc, W, hW, hxW, hfhol.mono hWW1,
    aemeasurable_multiplierDensity_restrict hW (hφ.mono hWO) hc.ne'
      (hfhol.mono hWW1).continuousOn, ?_⟩
  have hgmeas : ∀ i, AEMeasurable (multiplierDensity φ k (g i)) (μ.restrict W) :=
    fun i => ((hgL2 i).1.mono_measure (Measure.restrict_mono hWO le_rfl))
  have hsummeas := Finset.aemeasurable_fun_sum Finset.univ fun i _ => hgmeas i
  calc
    (∫⁻ y in W, multiplierDensity φ c f y ∂μ) ≤
        ∫⁻ y in W, (multiplierDensity (generatorLog g) (c * (1 + δ) / k) f y + K +
          K * ∑ i, multiplierDensity φ k (g i) y + K) ∂μ :=
      setLIntegral_mono_ae' hW.measurableSet (Eventually.of_forall hpoint)
    _ = (∫⁻ y in W, multiplierDensity (generatorLog g) (c * (1 + δ) / k) f y ∂μ) +
        K * μ W + K * ∑ i, ∫⁻ y in W, multiplierDensity φ k (g i) y ∂μ + K * μ W := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_add_right' _ (hsummeas.const_mul K),
        lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
        lintegral_const_mul' _ _ hK, lintegral_finsetSum' _ fun i _ => hgmeas i]
    _ < ⊤ := by
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
        ⟨ENNReal.add_lt_top.mpr ⟨(hfL2.mono hWW1).2,
          ENNReal.mul_lt_top hK.lt_top hμW.lt_top⟩, ?_⟩,
        ENNReal.mul_lt_top hK.lt_top hμW.lt_top⟩
      exact ENNReal.mul_lt_top hK.lt_top
        (ENNReal.sum_lt_top.mpr fun i _ => ((hgL2 i).mono hWO).2)

end
end SGPT.Foundations.Analysis.Pending.RawWeightedLogFamilyReverseIntegrability
