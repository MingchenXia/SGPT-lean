import SGPT.NPP.LogConcavityDinewDistribution
import SGPT.Foundations.Analysis.BallRotation
import SGPT.Foundations.Analysis.CircleSubmean
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

/-!
# Plurisubharmonic functions lie below their heat flow

For a real plurisubharmonic function `u` on `ℂⁿ` of quadratic growth, `u ≤ heatFlow u t`
(`le_heatFlow_of_psh`): the kernel is invariant under `w ↦ e^{iθ} w`, so the Gaussian average is an
average of circle averages over complex lines, each of which dominates the centre value.

Consequently (`integral_mul_leviSum_ge_of_psh`), a plurisubharmonic function of quadratic growth
which is a viscosity subsolution of `L u ≥ F`, `L = ∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`, satisfies `L u ≥ F` in the sense
of distributions: `∫ u · Lχ ≥ F ∫ χ` for nonnegative compactly supported `C²` functions `χ`. This is
FPT `lem:constant-elliptic-upper-tests` for the operator `L` (the initial layer of the comparison
argument is the circle submean inequality).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

theorem upperSemicontinuous_of_coe {u : ComplexModel n → ℝ}
    (hu : UpperSemicontinuous fun z => (u z : EReal)) : UpperSemicontinuous u := by
  intro x a ha
  filter_upwards [hu x (a : EReal) (EReal.coe_lt_coe_iff.mpr ha)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

theorem upperSemicontinuous_of_psh {u : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (fun z => (u z : EReal)) univ) : UpperSemicontinuous u := by
  have h := (SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn hpsh).upperSemicontinuousOn
  exact upperSemicontinuous_of_coe (upperSemicontinuousOn_univ_iff.mp h)

/-- The circle submean inequality for a plurisubharmonic function on the whole space. -/
theorem le_circleAverage_of_psh {u : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (fun z => (u z : EReal)) univ) {C : ℝ}
    (hC : ∀ y, |u y| ≤ C * (1 + ‖y‖ ^ 2)) (hm : Measurable u) (x v : ComplexModel n) :
    u x ≤ Real.circleAverage (fun ζ : ℂ => u (x + ζ • v)) 0 1 := by
  have hD := SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn hpsh
  obtain ⟨B, hB⟩ := hD.exists_disc_upper_bound x v zero_le_one (subset_univ _)
  have hB' : ∀ y ∈ affineClosedDisc x v 1, u y ≤ B := fun y hy => EReal.coe_le_coe_iff.mp (hB y hy)
  have hint : IntervalIntegrable (fun t : ℝ => u (x + circleMap 0 1 t • v)) volume 0
      (2 * Real.pi) := by
    have hmeas : Measurable fun t : ℝ => u (x + circleMap 0 1 t • v) :=
      hm.comp (by fun_prop : Continuous fun t : ℝ => x + circleMap 0 1 t • v).measurable
    refine (intervalIntegrable_const (c := C * (1 + (‖x‖ + ‖v‖) ^ 2))).mono_fun
      hmeas.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    show ‖u (x + circleMap 0 1 t • v)‖ ≤ ‖C * (1 + (‖x‖ + ‖v‖) ^ 2)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (hC _).trans ?_
    have hC0 : 0 ≤ C := by
      have := hC 0
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_one] at this
      exact (abs_nonneg _).trans this
    have hn : ‖x + circleMap 0 1 t • v‖ ≤ ‖x‖ + ‖v‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_circleMap_zero, abs_one, one_mul]
    rw [abs_of_nonneg (by positivity)]
    gcongr
  refine (circleDeficit_coe_le_iff x v 1 B hint
    (fun t => hB' _ (circle_mem_affineClosedDisc x v zero_le_one t))
    (hB' x (center_mem_affineClosedDisc x v zero_le_one))).mp ?_
  exact hD.submean x v 1 one_pos (subset_univ _) B hB

/-- **Gaussian submean inequality** for plurisubharmonic functions. -/
theorem le_heatFlow_of_psh {u : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (fun z => (u z : EReal)) univ) {C : ℝ}
    (hC : ∀ y, |u y| ≤ C * (1 + ‖y‖ ^ 2)) (hm : Measurable u) {t : ℝ} (ht : 0 < t)
    (x : ComplexModel n) : u x ≤ heatFlow u t x := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  rw [heatFlow_eq_integral_translate]
  set I : ℝ := ∫ w, heatKernel n t w * u (x - w) with hI
  have hint := integrable_heatKernel_mul_translate hC hm ht x
  -- rotation invariance
  have hrot : ∀ θ : ℝ, ∫ w, heatKernel n t w * u (x + circleMap 0 1 θ • (-w)) = I := by
    intro θ
    have hz : ‖circleMap 0 1 θ‖ = 1 := by simp
    have hmp := measurePreserving_smul_of_norm_eq_one (volume : Measure (ComplexModel n))
      (circleMap 0 1 θ) hz
    have hz0 : circleMap 0 1 θ ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    have := hmp.integral_comp (measurableEmbedding_const_smul₀ hz0)
      (fun w => heatKernel n t w * u (x - w))
    rw [hI, ← this]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [heatKernel_smul_of_norm_eq_one t hz, smul_neg, ← sub_eq_add_neg]
  -- the integrand on the product
  set F : ℝ → ComplexModel n → ℝ := fun θ w => heatKernel n t w * u (x + circleMap 0 1 θ • (-w))
    with hF
  have hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    have h1 : Continuous fun p : ℝ × ComplexModel n => heatKernel n t p.2 :=
      (continuous_heatKernel ht.ne').comp continuous_snd
    have h2 : Measurable fun p : ℝ × ComplexModel n => u (x + circleMap 0 1 p.1 • (-p.2)) :=
      hm.comp (by fun_prop : Continuous fun p : ℝ × ComplexModel n =>
        x + circleMap 0 1 p.1 • (-p.2)).measurable
    exact (h1.measurable.mul h2).aestronglyMeasurable
  have hbound : ∀ θ w, |F θ w| ≤ C * (1 + 2 * ‖x‖ ^ 2) * heatKernel n t w +
      2 * C * (heatKernel n t w * ‖w‖ ^ 2) := by
    intro θ w
    simp only [hF]
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht w)]
    have h1 := hC (x + circleMap 0 1 θ • (-w))
    have h2 : ‖x + circleMap 0 1 θ • (-w)‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
      have h3 : ‖x + circleMap 0 1 θ • (-w)‖ ≤ ‖x‖ + ‖w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_circleMap_zero, abs_one, one_mul, norm_neg]
      nlinarith [sq_nonneg (‖x‖ - ‖w‖), norm_nonneg (x + circleMap 0 1 θ • (-w)), norm_nonneg x,
        norm_nonneg w]
    have := heatKernel_nonneg ht w
    calc heatKernel n t w * |u (x + circleMap 0 1 θ • -w)|
        ≤ heatKernel n t w * (C * (1 + ‖x + circleMap 0 1 θ • (-w)‖ ^ 2)) := by gcongr
      _ ≤ heatKernel n t w * (C * (1 + (2 * ‖x‖ ^ 2 + 2 * ‖w‖ ^ 2))) := by gcongr
      _ = _ := by ring
  have hK := integrable_heatKernel (n := n) ht
  have hK2 := integrable_heatKernel_mul_sq (n := n) ht
  have hG : Integrable (fun w : ComplexModel n => C * (1 + 2 * ‖x‖ ^ 2) * heatKernel n t w +
      2 * C * (heatKernel n t w * ‖w‖ ^ 2)) := (hK.const_mul _).add (hK2.const_mul _)
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    refine ((MeasureTheory.Integrable.mul_prod (integrable_const (1 : ℝ)) hG).mono' hFm
      (ae_of_all _ fun p => ?_))
    rw [Real.norm_eq_abs, one_mul]
    exact hbound p.1 p.2
  have hswap := integral_integral_swap hFint
  simp only [hF] at hswap
  -- left side: `2π I`
  have hL : ∫ θ in Ioc 0 (2 * Real.pi), ∫ w, heatKernel n t w * u (x + circleMap 0 1 θ • (-w)) =
      2 * Real.pi * I := by
    simp only [hrot, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      Real.volume_real_Ioc, sub_zero, smul_eq_mul]
    rw [max_eq_left (by positivity)]
  -- right side: circle averages
  have hR : 2 * Real.pi * (Real.pi ^ n * u x) ≤
      ∫ w, ∫ θ in Ioc 0 (2 * Real.pi), heatKernel n t w * u (x + circleMap 0 1 θ • (-w)) := by
    have hpt : ∀ w, heatKernel n t w * (2 * Real.pi * u x) ≤
        ∫ θ in Ioc 0 (2 * Real.pi), heatKernel n t w * u (x + circleMap 0 1 θ • (-w)) := by
      intro w
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg ht w)
      have h := le_circleAverage_of_psh hpsh hC hm x (-w)
      rw [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)] at h
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      have : (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), u (x + circleMap 0 1 θ • (-w)) =
          (∫ θ in Ioc 0 (2 * Real.pi), u (x + circleMap 0 1 θ • (-w))) / (2 * Real.pi) := by
        ring
      rw [this, le_div_iff₀ hpi] at h
      linarith
    have hint2 : Integrable (fun w => ∫ θ in Ioc 0 (2 * Real.pi),
        heatKernel n t w * u (x + circleMap 0 1 θ • (-w))) :=
      MeasureTheory.Integrable.integral_prod_right hFint
    calc 2 * Real.pi * (Real.pi ^ n * u x) = ∫ w, heatKernel n t w * (2 * Real.pi * u x) := by
          rw [integral_mul_const, integral_heatKernel ht]; ring
      _ ≤ _ := integral_mono (hK.mul_const _) hint2 hpt
  rw [hswap] at hL
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have : Real.pi ^ n * u x ≤ I := by nlinarith
  calc u x = (Real.pi ^ n)⁻¹ * (Real.pi ^ n * u x) := by field_simp
    _ ≤ (Real.pi ^ n)⁻¹ * I := mul_le_mul_of_nonneg_left this (by positivity)

/-- **Viscosity subsolutions are distributional subsolutions** (plurisubharmonic case). A
plurisubharmonic function of quadratic growth on `ℂⁿ` which is a viscosity subsolution of
`L u ≥ F` (`F ≥ 0`) satisfies `∫ u · Lχ ≥ F ∫ χ` for nonnegative compactly supported `C²` `χ`. -/
theorem integral_mul_leviSum_ge_of_psh {u : ComplexModel n → ℝ}
    (hpsh : PlurisubharmonicOn (fun z => (u z : EReal)) univ) {C F : ℝ}
    (hC : ∀ y, |u y| ≤ C * (1 + ‖y‖ ^ 2)) (hF : 0 ≤ F) (hvisc : IsViscositySub u F)
    {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) :
    F * ∫ x, χ x ≤ ∫ x, u x * leviSum χ x := by
  have husc := upperSemicontinuous_of_psh hpsh
  have hm : Measurable u := husc.measurable
  have hcomp := le_heatFlow_of_isViscositySub hC hm husc hvisc (C₀ := 0) (fun x t ht _ => by
    have := le_heatFlow_of_psh hpsh hC hm ht x
    simp only [zero_mul]
    linarith)
  exact integral_mul_leviSum_ge hC hm husc hF hcomp hχ hχc hχ0

end SGPT.NPP.LogConcavityDinew
