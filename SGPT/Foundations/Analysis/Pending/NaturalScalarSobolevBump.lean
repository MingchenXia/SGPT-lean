import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevGradient
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Actual normalized scalar bump smoothing and quantitative first-jet approximation

Five complete mathematical statements and ENTIRE proofs precede this source.
All convolutions use the actual normalized real bump and original Haar measure.
-/

noncomputable section

open Set MeasureTheory Function TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions Convolution Pointwise ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBump

open NaturalScalarSobolevJet NaturalScalarSobolevGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))

/-- Entire continuous scalar factors are genuinely integrable against the normalized compact kernel. -/
theorem normedBump_integrable_mul {g : E → ℝ} (hg : Continuous g) :
    Integrable (fun t => ρ.normed μ t * g t) μ :=
  (ρ.continuous_normed.mul hg).integrable_of_hasCompactSupport
    (ρ.hasCompactSupport_normed.mul_right)

/-- True square Jensen for the actual normalized-bump probability measure. -/
theorem normedBump_square_average_le {g : E → ℝ} (hg : Continuous g) :
    (∫ t, ρ.normed μ t * g t ∂μ) ^ 2 ≤ ∫ t, ρ.normed μ t * g t ^ 2 ∂μ := by
  let w : E → ℝ≥0∞ := fun t => ENNReal.ofReal (ρ.normed μ t)
  let ν : Measure E := μ.withDensity w
  have hw : Measurable w := ENNReal.measurable_ofReal.comp ρ.continuous_normed.measurable
  have ht : ∀ᵐ t ∂μ, w t < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hw1 : ∫⁻ t, w t ∂μ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal ρ.integrable_normed
      (Filter.Eventually.of_forall ρ.nonneg_normed), ρ.integral_normed, ENNReal.ofReal_one]
  have : IsProbabilityMeasure ν := ⟨by simp [ν, withDensity_apply, hw1]⟩
  have hgi : Integrable g ν := by
    apply (integrable_withDensity_iff_integrable_smul' hw ht).mpr
    simpa only [w, ENNReal.toReal_ofReal (ρ.nonneg_normed _), smul_eq_mul, Pi.pow_apply] using
      normedBump_integrable_mul μ ρ hg
  have hgsi : Integrable (fun t => g t ^ 2) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hw ht).mpr
    simpa only [w, ENNReal.toReal_ofReal (ρ.nonneg_normed _), smul_eq_mul, Pi.pow_apply] using
      normedBump_integrable_mul μ ρ (hg.pow 2)
  have hsq : ConvexOn ℝ univ (fun y : ℝ => y ^ 2) :=
    (by norm_num : Even (2 : ℕ)).convexOn_pow
  have hj := hsq.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hgi hgsi
  simp only [ν, integral_withDensity_eq_integral_toReal_smul hw ht,
    w, ENNReal.toReal_ofReal (ρ.nonneg_normed _), smul_eq_mul] at hj
  exact hj

variable (K : Compacts E)

/-- Exact normalized scalar smoothing error as the genuine weighted original difference. -/
theorem normedBump_error_integral (f : 𝓓_{K}(E, ℝ)) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x - f x =
      ∫ t, ρ.normed μ t * (f (x - t) - f x) ∂μ := by
  have hi : Integrable (fun t => ρ.normed μ t * f (x - t)) μ :=
    normedBump_integrable_mul μ ρ (f.continuous.comp (continuous_const.sub continuous_id))
  simp only [convolution_def, lsmul_apply, smul_eq_mul, mul_sub]
  rw [integral_sub hi (ρ.integrable_normed.mul_const (f x)), integral_mul_const,
    ρ.integral_normed, one_mul]

/-- Pointwise square Jensen for the actual original smoothing error. -/
theorem normedBump_error_square_le (f : 𝓓_{K}(E, ℝ)) (x : E) :
    ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x - f x) ^ 2 ≤
      ∫ t, ρ.normed μ t * (f (x - t) - f x) ^ 2 ∂μ := by
  rw [normedBump_error_integral]
  exact normedBump_square_average_le μ ρ
    ((f.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const)

/-- The literal normalized scalar convolution is genuinely entire C∞. -/
theorem normedBump_contDiff (f : 𝓓_{K}(E, ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
    (f.continuous.locallyIntegrable)

/-- Genuine compact support of the literal normalized scalar smoothing. -/
theorem normedBump_hasCompactSupport (f : 𝓓_{K}(E, ℝ)) :
    HasCompactSupport (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) :=
  ρ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) f.hasCompactSupport

/-- Actual closed support stays in the original compact set enlarged by the true kernel radius. -/
theorem normedBump_tsupport_subset (f : 𝓓_{K}(E, ℝ)) :
    tsupport (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) ⊆
      (K : Set E) + closedBall 0 ρ.rOut := by
  apply closure_minimal ((support_convolution_subset_swap (lsmul ℝ ℝ)).trans ?_)
    (K.isCompact.add (isCompact_closedBall 0 _)).isClosed
  rw [ρ.support_normed_eq]
  exact Set.add_subset_add f.support_subset ball_subset_closedBall


/-- Actual nonnegative Tonelli average of genuine original scalar translation errors. -/
theorem lintegral_normedBump_error_square_le_average (f : 𝓓_{K}(E, ℝ)) :
    (∫⁻ x, ENNReal.ofReal (((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → ℝ)) x - f x) ^ 2) ∂μ) ≤
      ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) *
        (∫⁻ x, ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂μ) ∂μ := by
  have hm : Measurable (fun z : E × E => ENNReal.ofReal (ρ.normed μ z.2) *
      ENNReal.ofReal ((f (z.1 - z.2) - f z.1) ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (ρ.continuous_normed.comp continuous_snd).measurable).mul
      (ENNReal.measurable_ofReal.comp (((f.continuous.comp (continuous_fst.sub continuous_snd)).sub
        (f.continuous.comp continuous_fst)).pow 2).measurable)
  have he (x : E) : ENNReal.ofReal (∫ t, ρ.normed μ t * (f (x - t) - f x) ^ 2 ∂μ) =
      ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) * ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂μ := by
    have hi : Integrable (fun t => ρ.normed μ t * (f (x - t) - f x) ^ 2) μ := by
      simpa only [Pi.pow_apply, Function.comp_def, Pi.sub_apply, id_eq] using normedBump_integrable_mul μ ρ
        (((f.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).pow 2)
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun t =>
      mul_nonneg (ρ.nonneg_normed t) (sq_nonneg _))]
    simp_rw [ENNReal.ofReal_mul (ρ.nonneg_normed _)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ.normed μ t) *
        ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂μ ∂μ := by
      apply lintegral_mono
      intro x
      exact (ENNReal.ofReal_le_ofReal (normedBump_error_square_le μ ρ K f x)).trans_eq (he x)
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ.normed μ t) *
        ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂μ ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      congr 1
      ext t
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (ν : Measure V) [ν.IsAddHaarMeasure] (η : ContDiffBump (0 : V))
  (L : Compacts V) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)

/-- Genuine normalized-bump square error bounded quantitatively by the actual original first jet. -/
theorem lintegral_normedBump_error_square_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    (∫⁻ x, ENNReal.ofReal (((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2) ∂ν) ≤
      ENNReal.ofReal (η.rOut ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2) := by
  have hw : Measurable (fun t => ENNReal.ofReal (η.normed ν t)) :=
    ENNReal.measurable_ofReal.comp η.continuous_normed.measurable
  have hw1 : ∫⁻ t, ENNReal.ofReal (η.normed ν t) ∂ν = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal η.integrable_normed
      (Filter.Eventually.of_forall η.nonneg_normed), η.integral_normed, ENNReal.ofReal_one]
  have hf2 : MemLp (f : V → ℝ) 2 ν :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have ht (t : V) : (∫⁻ x, ENNReal.ofReal ((f (x - t) - f x) ^ 2) ∂ν) ≤
      ENNReal.ofReal (‖t‖ ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2) := by
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
        ENNReal.ofReal (η.rOut ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2) ∂ν := by
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
      have hc := (ht t).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖firstJetLinear ν L b f‖)))
      exact mul_le_mul le_rfl hc zero_le zero_le
    _ = _ := by rw [lintegral_mul_const _ hw, hw1, one_mul]

/-- The literal finite real smoothing error integral satisfies the quantitative first-jet estimate. -/
theorem integral_normedBump_error_square_le_firstJet (f : 𝓓_{L}(V, ℝ)) :
    (∫ x, ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2 ∂ν) ≤
      η.rOut ^ 2 * ‖firstJetLinear ν L b f‖ ^ 2 := by
  have hf2 : MemLp (f : V → ℝ) 2 ν :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hg2 : MemLp (η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) 2 ν :=
    (normedBump_contDiff ν η L f).continuous.memLp_of_hasCompactSupport
      (normedBump_hasCompactSupport ν η L f)
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp
  have hi : Integrable (fun x =>
      ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2) ν :=
    (hg2.sub hf2).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_normedBump_error_square_le_firstJet ν η L b f

/-- One actual normalized-bump square approximation error bound for an entire first-jet bounded family. -/
theorem uniform_normedBump_error_square_le (A : Set 𝓓_{L}(V, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear ν L b f‖ ≤ R) (f : 𝓓_{L}(V, ℝ)) (hf : f ∈ A) :
    (∫ x, ((η.normed ν ⋆[lsmul ℝ ℝ, ν] (f : V → ℝ)) x - f x) ^ 2 ∂ν) ≤ η.rOut ^ 2 * R ^ 2 := by
  apply (integral_normedBump_error_square_le_firstJet ν η L b f).trans
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).2 (hA f hf)) (sq_nonneg _)

end InnerProduct

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBump
