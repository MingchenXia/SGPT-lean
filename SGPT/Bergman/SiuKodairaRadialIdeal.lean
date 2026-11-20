import SGPT.PSH.GlobalL2PoleFunction
import SGPT.Foundations.Analysis.Pending.ActualMultiplierLogarithmicExponent
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The actual critical logarithmic point ideal

The coefficient is the complex dimension itself.  Finite weighted mass
forces a holomorphic germ to vanish; a holomorphic germ vanishing at the
point has finite weighted mass by its genuine first-order bound.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:radial-ideal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

/-- The precise critical point-pole weight, retaining its negative-infinite value. -/
def criticalPole (n : ℕ) (p z : ComplexModel n) : EReal :=
  ((n : ℝ) : EReal) * logNormSq (z - p)

theorem criticalPole_weight {n : ℕ} (p : ComplexModel n) {z : ComplexModel n} (hz : z ≠ p) :
    multiplierWeight 1 (criticalPole n p z) =
      ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) := by
  have hp : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [criticalPole, logNormSq_of_ne_zero (sub_ne_zero.mpr hz), ← EReal.coe_mul,
    multiplierWeight_coe, one_mul, Real.log_pow, Real.rpow_def_of_pos hp]
  congr 2
  ring

/-- A finite actual multiplier integral at the critical exponent forces zero
value.  This implication uses only continuity of its genuine holomorphic germ. -/
theorem eq_zero_of_multiplierIntegrableAt_criticalPole {n : ℕ} (hn : 0 < n)
    {p : ComplexModel n} {f : ComplexModel n → ℂ}
    (hint : MultiplierIntegrableAt (criticalPole n p) 1 f p volume) : f p = 0 := by
  by_contra hfp
  obtain ⟨_, U, hU, hpU, hfU, hfint⟩ := hint
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpn : 0 < ‖f p‖ := norm_pos_iff.mpr hfp
  have hfc := (hfU.differentiableAt (hU.mem_nhds hpU)).continuousAt
  let c : ℝ := ‖f p‖ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound : ∀ᶠ z in 𝓝 p, c ≤ ‖f z‖ := by
    exact (hfc.norm.eventually (eventually_ge_nhds (by dsimp [c]; linarith : c < ‖f p‖)))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp ((show ∀ᶠ z in 𝓝 p, z ∈ U from hU.mem_nhds hpU).and hbound)
  have hBU : ball p R ⊆ U := fun _ hz => (hball hz).1
  have hpt : ∀ z ∈ ball p R,
      ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) ≤
        ENNReal.ofReal ((c ^ 2)⁻¹) * multiplierDensity (criticalPole n p) 1 f z := by
    intro z hz
    by_cases hzp : z = p
    · subst z
      rw [sub_self, norm_zero, Real.zero_rpow (ne_of_lt (by linarith : -(2 * (n : ℝ)) < 0)),
        ENNReal.ofReal_zero]
      exact zero_le
    have hcoef : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((c ^ 2)⁻¹) * ENNReal.ofReal (‖f z‖ ^ 2) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _)), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hc)]
      have hle := (hball hz).2
      nlinarith [norm_nonneg (f z)]
    calc ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) =
        1 * ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal ((c ^ 2)⁻¹) * ENNReal.ofReal (‖f z‖ ^ 2)) *
          ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcoef zero_le
      _ = _ := by rw [multiplierDensity, criticalPole_weight p hzp]; ring
  have hfin : (∫⁻ z in ball p R, ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ))))) < ⊤ := by
    calc _ ≤ ∫⁻ z in ball p R,
          ENNReal.ofReal ((c ^ 2)⁻¹) * multiplierDensity (criticalPole n p) 1 f z :=
        setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ((c ^ 2)⁻¹) *
          ∫⁻ z in ball p R, multiplierDensity (criticalPole n p) 1 f z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfint.mono hBU).2
  have hmeas : Measurable (fun z : ComplexModel n => ‖z - p‖ ^ (-(2 * (n : ℝ)))) := by fun_prop
  have hi : IntegrableOn (fun z : ComplexModel n => ‖z - p‖ ^ (-(2 * (n : ℝ))))
      (ball p R) volume :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
        Real.rpow_nonneg (norm_nonneg _) _)).mpr hfin⟩
  have : Nontrivial (ComplexModel n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [PointPole.finrank_real_complexModel]; omega)
  have hdim := ActualMultiplierLogarithmicExponent.exponent_lt_finrank_of_integrableOn_norm_sub_rpow
    volume hR hi
  rw [PointPole.finrank_real_complexModel] at hdim
  push_cast at hdim
  exact (lt_irrefl _ hdim)

/-- The actual subcritical radial function is integrable on any centered ball. -/
theorem integrableOn_norm_sub_criticalRemainder {n : ℕ} (hn : 0 < n)
    (p : ComplexModel n) (R : ℝ) :
    IntegrableOn (fun z : ComplexModel n => ‖z - p‖ ^ (2 - 2 * (n : ℝ))) (ball p R) volume := by
  have hd : 1 ≤ Module.finrank ℝ (ComplexModel n) := by
    rw [PointPole.finrank_real_complexModel]; omega
  have hα : 2 * (n : ℝ) - 2 < (Module.finrank ℝ (ComplexModel n) : ℝ) := by
    rw [PointPole.finrank_real_complexModel]; push_cast; linarith
  have hm : Measurable (fun z : ComplexModel n => ‖z‖ ^ (2 - 2 * (n : ℝ))) := by fun_prop
  have hi : IntegrableOn (fun z : ComplexModel n => ‖z‖ ^ (2 - 2 * (n : ℝ))) (ball 0 R) volume := by
    apply integrableOn_ball_of_norm_le_rpow hd hα (C := 1) (α := 2 * (n : ℝ) - 2)
      (h_meas := hm.aestronglyMeasurable)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      rw [show -(2 * (n : ℝ) - 2) = 2 - 2 * (n : ℝ) by ring]
  apply ((measurePreserving_add_right volume p).integrableOn_comp_preimage
    (Homeomorph.addRight p).measurableEmbedding).mp
  change IntegrableOn (fun z : ComplexModel n => ‖z + p - p‖ ^ (2 - 2 * (n : ℝ)))
    ((fun z : ComplexModel n => z + p) ⁻¹' ball p R) volume
  have hs : (fun z : ComplexModel n => z + p) ⁻¹' ball p R = ball 0 R := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
  simpa only [add_sub_cancel_right, hs] using hi

/-- Genuine first-order control gives finite critical-pole weighted mass. -/
theorem weightedL2On_criticalPole_of_linearBound {n : ℕ} (hn : 0 < n)
    {p : ComplexModel n} {R C : ℝ} {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f (ball p R)) (hfp : f p = 0)
    (hbound : ∀ z ∈ ball p R, ‖f z‖ ≤ C * ‖z - p‖) :
    WeightedL2On (criticalPole n p) 1 f (ball p R) volume := by
  have hlog : PlurisubharmonicOn (fun z : ComplexModel n => logNormSq (z - p)) univ := by
    have h := PlurisubharmonicOn.comp_affine (u := logNormSq (E := ComplexModel n))
      (U := univ) (fun x _ => plurisubharmonicAt_logNormSq x)
      (ContinuousLinearMap.id ℂ (ComplexModel n)) (-p)
    intro z _
    refine (h z (by simp)).congr (Eventually.of_forall fun w => ?_)
    simp [neg_add_eq_sub]
  have hpsh : PlurisubharmonicOn (criticalPole n p) univ :=
    hlog.const_mul (by exact_mod_cast hn)
  have hwm : AEMeasurable (fun z => multiplierWeight 1 (criticalPole n p z))
      (volume.restrict (ball p R)) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
    (hpsh.upperSemicontinuousOn.mono (subset_univ _)) (by norm_num : (1 : ℝ) ≠ 0)
  have hfm : AEMeasurable (fun z => ENNReal.ofReal (‖f z‖ ^ 2))
      (volume.restrict (ball p R)) := ENNReal.measurable_ofReal.comp_aemeasurable
    ((hf.continuousOn.aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const 2)
  refine ⟨hfm.mul hwm, ?_⟩
  have hpt : ∀ z ∈ ball p R, multiplierDensity (criticalPole n p) 1 f z ≤
      ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (‖z - p‖ ^ (2 - 2 * (n : ℝ))) := by
    intro z hz
    by_cases hzp : z = p
    · subst z
      rw [multiplierDensity_eq_zero_of_eq_zero _ _ hfp]
      exact zero_le
    have hp : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    rw [multiplierDensity, criticalPole_weight p hzp]
    calc ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) ≤
        ENNReal.ofReal ((C * ‖z - p‖) ^ 2) * ENNReal.ofReal (‖z - p‖ ^ (-(2 * (n : ℝ)))) := by
          gcongr
          exact hbound z hz
      _ = _ := by
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_mul (sq_nonneg _), show 2 - 2 * (n : ℝ) = 2 + -(2 * (n : ℝ)) by ring,
          Real.rpow_add hp, Real.rpow_two]
  calc (∫⁻ z in ball p R, multiplierDensity (criticalPole n p) 1 f z) ≤
        ∫⁻ z in ball p R, ENNReal.ofReal (C ^ 2) *
          ENNReal.ofReal (‖z - p‖ ^ (2 - 2 * (n : ℝ))) := setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (C ^ 2) *
        ∫⁻ z in ball p R, ENNReal.ofReal (‖z - p‖ ^ (2 - 2 * (n : ℝ))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
        Real.rpow_nonneg (norm_nonneg _) _)).mp
          (integrableOn_norm_sub_criticalRemainder hn p R).2)

/-- The complete literal Euclidean critical multiplier criterion. -/
theorem multiplierIntegrableAt_criticalPole_iff {n : ℕ} (hn : 0 < n)
    {p : ComplexModel n} {f : ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hpU : p ∈ U)
    (hf : DifferentiableOn ℂ f U) :
    MultiplierIntegrableAt (criticalPole n p) 1 f p volume ↔ f p = 0 := by
  refine ⟨eq_zero_of_multiplierIntegrableAt_criticalPole hn, fun hfp => ?_⟩
  obtain ⟨C, hCb⟩ := (hf.differentiableAt (hU.mem_nhds hpU)).isBigO_sub.bound
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp ((show ∀ᶠ z in 𝓝 p, z ∈ U from hU.mem_nhds hpU).and hCb)
  have hfB := hf.mono (show ball p R ⊆ U from fun z hz => (hball hz).1)
  refine ⟨one_pos, ball p R, isOpen_ball, mem_ball_self hR, hfB,
    weightedL2On_criticalPole_of_linearBound hn (C := C) hfB hfp ?_⟩
  intro z hz
  simpa only [hfp, sub_zero] using (hball hz).2

end SGPT.Bergman.SiuKodaira
