import SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapWeightBound
import SGPT.Foundations.Analysis.Pending.ActualMultiplierAdditionLocalIntegrability

set_option autoImplicit false

/-! # Actual local sum integrability retaining distinct source and target exponents -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapLocalIntegrability

open FirstPass IEquivalentMax ActualMultiplierFiniteGapWeightBound

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The two weighted families are integrated separately; the actual holomorphic germ
itself supplies its finite local bound and a finite-measure neighborhood. -/
theorem multiplierIntegrableAt_add_of_generators {A B U V : E → EReal}
    {x : E} {c q p m : ℝ} (hc : 0 < c) (hq : 0 < q) (hp : 0 < p)
    (hm : 0 < m) (hgap : 2 * c ≤ p - m * c / q) {f : E → ℂ}
    (hsource : MultiplierIntegrableAt (fun y => U y + V y) q f x μ)
    {O : Set E} (hO : IsOpen O) (hxO : x ∈ O)
    (hA : QuasiPlurisubharmonicOn A O) (hB : QuasiPlurisubharmonicOn B O)
    (hU : QuasiPlurisubharmonicOn U O) (hV : QuasiPlurisubharmonicOn V O)
    (hAB : QuasiPlurisubharmonicOn (fun y => A y + B y) O)
    {N₁ N₂ : ℕ} {g : Fin N₁ → E → ℂ} {h : Fin N₂ → E → ℂ}
    {C D : ℝ≥0∞} (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hgL2 : ∀ l, WeightedL2On A p (g l) O μ)
    (hhL2 : ∀ r, WeightedL2On B p (h r) O μ)
    (hdomU : ∀ y ∈ O, EReal.exp ((m : EReal) * U y) ≤
      C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2))
    (hdomV : ∀ y ∈ O, EReal.exp ((m : EReal) * V y) ≤
      D * ∑ r, ENNReal.ofReal (‖h r y‖ ^ 2)) :
    MultiplierIntegrableAt (fun y => A y + B y) c f x μ := by
  obtain ⟨-, W1, hW1, hxW1, hfhol, hfL2⟩ := hsource
  have hfc : ContinuousAt f x := (hfhol.differentiableAt (hW1.mem_nhds hxW1)).continuousAt
  have hbound : ∀ᶠ y in 𝓝 x, ‖f y‖ < ‖f x‖ + 1 :=
    hfc.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨V2, hV2sub, hV2, hxV2⟩ := mem_nhds_iff.mp hbound
  let W := W1 ∩ O ∩ V2 ∩ Metric.ball x 1
  have hW : IsOpen W := ((hW1.inter hO).inter hV2).inter Metric.isOpen_ball
  have hxW : x ∈ W := ⟨⟨⟨hxW1, hxO⟩, hxV2⟩, Metric.mem_ball_self one_pos⟩
  have hWW1 : W ⊆ W1 := fun _ hy => hy.1.1.1
  have hWO : W ⊆ O := fun _ hy => hy.1.1.2
  have hμW : μ W ≠ ⊤ := ((measure_mono (fun _ hy => hy.2)).trans_lt
    (measure_ball_lt_top (μ := μ))).ne
  let K : ℝ≥0∞ := ENNReal.ofReal ((‖f x‖ + 1) ^ 2)
  have hK : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ y ∈ W, multiplierDensity (fun y => A y + B y) c f y ≤
      multiplierDensity (fun y => U y + V y) q f y + K +
        ∑ l, (K * C) * multiplierDensity A p (g l) y +
        ∑ r, (K * D) * multiplierDensity B p (h r) y := by
    intro y hy
    have hyO := hWO hy
    have hfy : ENNReal.ofReal (‖f y‖ ^ 2) ≤ K := ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (hV2sub hy.1.2).le 2)
    have hw := multiplierWeight_le_sum_add_ratios hc hq hp hm hgap
      (hA y hyO).ne_top (hB y hyO).ne_top (hU y hyO).ne_top (hV y hyO).ne_top
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (A y + B y) ≤
          ENNReal.ofReal (‖f y‖ ^ 2) *
            (multiplierWeight q (U y + V y) + 1 +
              EReal.exp ((m : EReal) * U y) * multiplierWeight p (A y) +
              EReal.exp ((m : EReal) * V y) * multiplierWeight p (B y)) := by gcongr
      _ ≤ ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight q (U y + V y) +
          K + K * ((C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2)) * multiplierWeight p (A y)) +
          K * ((D * ∑ r, ENNReal.ofReal (‖h r y‖ ^ 2)) * multiplierWeight p (B y)) := by
            rw [mul_add, mul_add, mul_add, mul_one]
            exact add_le_add (add_le_add (add_le_add le_rfl hfy)
              (mul_le_mul' hfy (mul_le_mul' (hdomU y hyO) le_rfl)))
              (mul_le_mul' hfy (mul_le_mul' (hdomV y hyO) le_rfl))
      _ = _ := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          congr 1
          · congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨hc, W, hW, hxW, hfhol.mono hWW1,
    aemeasurable_multiplierDensity_restrict hW (hAB.mono hWO) hc.ne'
      (hfhol.mono hWW1).continuousOn, ?_⟩
  have hgmeas := fun l => ((hgL2 l).1.mono_measure
    (Measure.restrict_mono hWO le_rfl)).const_mul (K * C)
  have hhmeas := fun r => ((hhL2 r).1.mono_measure
    (Measure.restrict_mono hWO le_rfl)).const_mul (K * D)
  calc
    (∫⁻ y in W, multiplierDensity (fun y => A y + B y) c f y ∂μ) ≤
        ∫⁻ y in W, (multiplierDensity (fun y => U y + V y) q f y + K +
          ∑ l, (K * C) * multiplierDensity A p (g l) y +
          ∑ r, (K * D) * multiplierDensity B p (h r) y) ∂μ :=
      setLIntegral_mono_ae' hW.measurableSet (Eventually.of_forall hpoint)
    _ = (∫⁻ y in W, multiplierDensity (fun y => U y + V y) q f y ∂μ) +
        K * μ W + ∑ l, (K * C) * ∫⁻ y in W, multiplierDensity A p (g l) y ∂μ +
        ∑ r, (K * D) * ∫⁻ y in W, multiplierDensity B p (h r) y ∂μ := by
      rw [lintegral_add_right' _ (Finset.aemeasurable_fun_sum _ fun r _ => hhmeas r),
        lintegral_add_right' _ (Finset.aemeasurable_fun_sum _ fun l _ => hgmeas l),
        lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
        lintegral_finsetSum' _ fun l _ => hgmeas l,
        lintegral_finsetSum' _ fun r _ => hhmeas r]
      simp_rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hK hC),
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hK hD)]
    _ < ⊤ := by
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
        ⟨ENNReal.add_lt_top.mpr ⟨(hfL2.mono hWW1).2,
          ENNReal.mul_lt_top hK.lt_top hμW.lt_top⟩, ?_⟩, ?_⟩
      · exact ENNReal.sum_lt_top.mpr fun l _ => ENNReal.mul_lt_top
          (ENNReal.mul_ne_top hK hC).lt_top ((hgL2 l).mono hWO).2
      · exact ENNReal.sum_lt_top.mpr fun r _ => ENNReal.mul_lt_top
          (ENNReal.mul_ne_top hK hD).lt_top ((hhL2 r).mono hWO).2


end

end SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapLocalIntegrability
