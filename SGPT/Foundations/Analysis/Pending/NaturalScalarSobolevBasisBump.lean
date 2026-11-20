import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisGradient
import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevL2Smoothing

/-! # Genuine original finite-basis quantitative normalized scalar smoothing

Three entire mathematical statements and proofs precede this source.
The actual coordinate constant is supplied by its internal original-basis construction.
-/

noncomputable section

open Set MeasureTheory Function TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions Convolution Pointwise ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisBump

open NaturalScalarSobolevJet NaturalScalarSobolevBasisGradient
  NaturalScalarSobolevBump NaturalScalarSobolevL2Smoothing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (ν : Measure V) [ν.IsAddHaarMeasure] (η : ContDiffBump (0 : V))
  (L : Compacts V) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)

/-- Genuine normalized-bump square error bounded quantitatively by the actual original first jet. -/
theorem lintegral_normedBump_error_square_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    (∫⁻ x, ENNReal.ofReal (((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2) ∂ν) ≤
      ENNReal.ofReal (η.rOut ^ 2 * basisGradientConstant b * ‖firstJetLinear ν L b f‖ ^ 2) := by
  have hw : Measurable (fun t => ENNReal.ofReal (η.normed ν t)) :=
    ENNReal.measurable_ofReal.comp η.continuous_normed.measurable
  have hw1 : ∫⁻ t, ENNReal.ofReal (η.normed ν t) ∂ν = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal η.integrable_normed
      (Filter.Eventually.of_forall η.nonneg_normed), η.integral_normed, ENNReal.ofReal_one]
  have hf2 : MemLp (f : V → ℝ) 2 ν :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have ht (t : V) : (∫⁻ x, ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂ν) ≤
      ENNReal.ofReal (basisGradientConstant b * ‖t‖ ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2) := by
    have hi : MemLp (fun x => f (x - t) - f x) 2 ν := by
      have heq : (fun x => f (x - t) - f x) =
          (((f : V → ℝ) ∘ fun x => x + -t) - (f : V → ℝ)) := by
        funext x
        simp only [Function.comp_def, Pi.sub_apply, sub_eq_add_neg]
      rw [heq]
      exact (hf2.comp_measurePreserving (measurePreserving_add_right ν (-t))).sub hf2
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [sub_eq_add_neg, norm_neg] using
      integral_translation_square_le_firstJet b L ν f (-t)
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (η.normed ν t) *
        (∫⁻ x, ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂ν) ∂ν :=
      lintegral_normedBump_error_square_le_average ν η L f
    _ ≤ ∫⁻ t, ENNReal.ofReal (η.normed ν t) *
        ENNReal.ofReal (η.rOut ^ 2 * basisGradientConstant b * ‖firstJetLinear ν L b f‖ ^ 2) ∂ν := by
      apply lintegral_mono
      intro t
      by_cases hz : η.normed ν t = 0
      · simp [hz]
      have hb : t ∈ ball (0 : V) η.rOut := by
        rw [← η.support_normed_eq (μ := ν)]
        exact hz
      have hnorm : ‖t‖ ≤ η.rOut := (mem_ball_zero_iff.mp hb).le
      have hs : ‖t‖ ^ 2 ≤ η.rOut ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) η.rOut_pos.le).2 hnorm
      have hbound : basisGradientConstant b * ‖t‖ ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2 ≤
          η.rOut ^ 2 * basisGradientConstant b * ‖firstJetLinear ν L b f‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hs
          (mul_nonneg (basisGradientConstant_nonneg b) (sq_nonneg ‖firstJetLinear ν L b f‖))
        nlinarith
      have hc := (ht t).trans (ENNReal.ofReal_le_ofReal hbound)
      exact mul_le_mul le_rfl hc zero_le zero_le
    _ = _ := by rw [lintegral_mul_const _ hw, hw1, one_mul]

/-- The literal finite real smoothing error integral satisfies the quantitative first-jet estimate. -/
theorem integral_normedBump_error_square_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    (∫ x, ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2 ∂ν) ≤
      η.rOut ^ 2 * basisGradientConstant b * ‖firstJetLinear ν L b f‖ ^ 2 := by
  have hf2 : MemLp (f : V → ℝ) 2 ν :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hg2 : MemLp (η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) 2 ν :=
    (normedBump_contDiff ν η L f).continuous.memLp_of_hasCompactSupport
      (normedBump_hasCompactSupport ν η L f)
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (sq_nonneg _) (basisGradientConstant_nonneg b)) (sq_nonneg _))).mp
  have hi : Integrable (fun x =>
      ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2) ν :=
    (hg2.sub hf2).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_normedBump_error_square_le_firstJet ν η L b f

/-- One actual normalized-bump square approximation error bound for an entire first-jet bounded family. -/
theorem uniform_normedBump_error_square_le (A : Set 𝓓_{L}(V, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear ν L b f‖ ≤ R) (f : 𝓓_{L}(V, ℝ)) (hf : f ∈ A) :
    (∫ x, ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2 ∂ν) ≤ η.rOut ^ 2 * basisGradientConstant b * R ^ 2 := by
  apply (integral_normedBump_error_square_le_firstJet ν η L b f).trans
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).2 (hA f hf))
    (mul_nonneg (sq_nonneg _) (basisGradientConstant_nonneg b))


/-- True global L2 smoothing error in the original arbitrary-basis first-jet norm. -/
theorem norm_smoothingL2_error_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    ‖smoothingL2 ν L η f - scalarStageL2 ν L f‖ ≤
      η.rOut * Real.sqrt (basisGradientConstant b) * ‖firstJetLinear ν L b f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg η.rOut_pos.le (Real.sqrt_nonneg _)) (norm_nonneg _))).mp
  rw [smoothingL2_error_norm_sq]
  calc
    _ ≤ η.rOut ^ 2 * basisGradientConstant b * ‖firstJetLinear ν L b f‖ ^ 2 :=
      integral_normedBump_error_square_le_firstJet ν η L b f
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (basisGradientConstant_nonneg b)]

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisBump
