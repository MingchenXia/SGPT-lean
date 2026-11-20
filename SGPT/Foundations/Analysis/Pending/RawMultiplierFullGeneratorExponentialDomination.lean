import SGPT.Foundations.Analysis.Pending.RawMultiplierFiniteFamilyReverseMembership
import SGPT.Foundations.Analysis.Pending.HolomorphicIdealPowerGeneratorBound
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.LocalBergmanMeasureTransport
import SGPT.Foundations.Analysis.Pending.SNCCoordinateUnitCorrection
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false

/-! # The full original raw multiplier family supplies exponential domination -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierFullGeneratorExponentialDomination

open FirstPass WeightedHolomorphicGermIdealIntegralClosure

noncomputable section

private theorem exists_domination_of_full_span
    {n N : ℕ} {v : ComplexModel n → EReal} (hv : QuasiPlurisubharmonicAt v 0)
    {p : ℕ} (hp : 0 < p) (G : Fin N → ComplexModel n → ℂ)
    (hG : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G j) z)
    (hspan : Ideal.span (range fun j => HolGerm.mk (G j) (hG j)) =
      weightedGermIdeal (by exact_mod_cast hp : (0 : ℝ) < p) hv volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      EReal.exp ((p : EReal) * v z) ≤ C * ∑ j, ENNReal.ofReal (‖G j z‖ ^ 2) := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hv' := hv
  obtain ⟨P, h, ⟨Ω, hΩ, h0Ω, hdisc⟩, hh, heq⟩ := hv
  have hP := hdisc.plurisubharmonicOn hΩ
  obtain ⟨W, hW, h0W, _, L, d, C₀, hC₀, hd, hdL2, hdom⟩ :=
    DemaillyApproximation.exists_weightedL2_generators Ω P hΩ hP 0 h0Ω p hp
  have hdhol : ∀ l, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (d l) z := by
    intro l
    filter_upwards [hW.mem_nhds h0W] with z hz
    exact (hd l).differentiableOn.differentiableAt (hW.mem_nhds hz)
  have hdint : ∀ l, MultiplierIntegrableAt v p (d l) 0 volume := by
    intro l
    have hdP : MultiplierIntegrableAt P p (d l) 0 volume :=
      ⟨hpr, W, hW, h0W, (hd l).differentiableOn, weightedL2On_of_borelVolume (hdL2 l)⟩
    have hdPh := (SNCCoordinateUnitCorrection.multiplierIntegrableAt_add_continuous_iff
      (hh.mono fun _ hz => hz.continuousAt)).mpr hdP
    exact hdPh.congr heq.symm EventuallyEq.rfl
  have hdmem : ∀ l, HolGerm.mk (d l) (hdhol l) ∈
      (Ideal.span (range fun j => HolGerm.mk (G j) (hG j))) ^ 1 := by
    intro l
    rw [pow_one, hspan]
    exact (mem_weightedGermIdeal_iff hpr hv' (hdhol l)).mpr (hdint l)
  choose A hA hb using fun l =>
    HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow
      G hG (d l) (hdhol l) 1 (hdmem l)
  let B : ℝ := (N : ℝ) * ∑ l, A l ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((p : ℝ) * (h 0 + 1)))
  refine ⟨K * C₀ * ENNReal.ofReal B, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀)
      ENNReal.ofReal_ne_top
  have hhB : ∀ᶠ z in 𝓝 (0 : ComplexModel n), h z ≤ h 0 + 1 :=
    (hh.self_of_nhds.continuousAt.eventually_lt continuousAt_const (by linarith)).mono
      fun _ hz => hz.le
  filter_upwards [hW.mem_nhds h0W, heq, hhB, Filter.eventually_all.mpr hb]
    with z hz hvez hhz hbz
  have hsq : (∑ j, ‖G j z‖) ^ 2 ≤ (N : ℝ) * ∑ j, ‖G j z‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin N => ‖G j z‖))
  have hsum : (∑ l, ‖d l z‖ ^ 2) ≤ B * ∑ j, ‖G j z‖ ^ 2 := by
    calc
      _ ≤ ∑ l, (A l * ∑ j, ‖G j z‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro l _
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using hbz l) 2
      _ = (∑ l, A l ^ 2) * (∑ j, ‖G j z‖) ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.sum_mul]
      _ ≤ (∑ l, A l ^ 2) * ((N : ℝ) * ∑ j, ‖G j z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = _ := by dsimp [B]; ring
  have hsumE : (∑ l, ENNReal.ofReal (‖d l z‖ ^ 2)) ≤
      ENNReal.ofReal B * ∑ j, ENNReal.ofReal (‖G j z‖ ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      ← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal hsum
  have hexp : EReal.exp ((p : EReal) * v z) ≤ K * EReal.exp ((p : EReal) * P z) := by
    rw [hvez, EReal.left_distrib_of_nonneg_of_ne_top (by positivity)
      (by rw [← EReal.coe_natCast]; exact EReal.coe_ne_top _),
      EReal.exp_add]
    have hfactor : EReal.exp ((p : EReal) * (h z : EReal)) ≤ K := by
      rw [← EReal.coe_natCast, ← EReal.coe_mul, EReal.exp_coe]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hhz hpr.le))
    calc
      _ ≤ EReal.exp ((p : EReal) * P z) * K := mul_le_mul_right hfactor _
      _ = _ := mul_comm _ _
  calc
    _ ≤ K * EReal.exp ((p : EReal) * P z) := hexp
    _ ≤ K * (C₀ * ∑ l, ENNReal.ofReal (‖d l z‖ ^ 2)) :=
      mul_le_mul_right (hdom z hz) K
    _ ≤ K * (C₀ * (ENNReal.ofReal B * ∑ j, ENNReal.ofReal (‖G j z‖ ^ 2))) := by
      gcongr
    _ = _ := by ac_rfl

/-- The same full original weighted ideal family is fixed before all later
coefficients, margins and tests, and internally controls the raw exponential. -/
theorem exists_full_family_with_exponential_domination
    {n : ℕ} {v : ComplexModel n → EReal} (hv : QuasiPlurisubharmonicAt v 0)
    {p : ℕ} (hp : 0 < p) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ)
      (hg : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (g j) z),
      Ideal.span (range fun j => HolGerm.mk (g j) (hg j)) =
        weightedGermIdeal (by exact_mod_cast hp : (0 : ℝ) < p) hv volume ∧
      (∀ j, MultiplierIntegrableAt v p (g j) 0 volume) ∧
      ∃ O : Set (ComplexModel n), IsOpen O ∧ (0 : ComplexModel n) ∈ O ∧
        QuasiPlurisubharmonicOn v O ∧ (∀ j, WeightedL2On v p (g j) O volume) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          (∀ᶠ z in 𝓝 (0 : ComplexModel n), EReal.exp ((p : EReal) * v z) ≤
            C * ∑ j, ENNReal.ofReal (‖g j z‖ ^ 2)) ∧
          ∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) →
            ∀ f : ComplexModel n → ℂ,
              MultiplierIntegrableAt (generatorLog g) (c * (1 + δ) / p) f 0 volume →
              MultiplierIntegrableAt v c f 0 volume := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨N, g, hg, hspan, hint, O, hO, h0O, hvO, hgO, hreverse⟩ :=
    RawMultiplierFiniteFamilyReverseMembership.exists_full_family_with_reverse_membership
      (μ := volume) hv hpr
  obtain ⟨C, hC, hdom⟩ := exists_domination_of_full_span hv hp g hg hspan
  exact ⟨N, g, hg, hspan, hint, O, hO, h0O, hvO, hgO, C, hC, hdom, hreverse⟩

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierFullGeneratorExponentialDomination
