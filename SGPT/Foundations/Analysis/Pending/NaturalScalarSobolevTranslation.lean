import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevJet
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual scalar Haar square-integral translation estimates

The four entire mathematical proofs were captured before this source.
The affine derivative is the ordinary derivative of the original smooth test.
-/

noncomputable section

open Set MeasureTheory Function TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevTranslation

open NaturalScalarSobolevJet

/-- Square Jensen on the actual unit interval, with its genuine probability restriction. -/
theorem unit_interval_square_le {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in Ioc (0 : ℝ) 1, g t ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hgi : Integrable g ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hg.intervalIntegrable 0 1)
  have hgsi : Integrable (fun t => g t ^ 2) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      ((hg.pow 2).intervalIntegrable 0 1)
  have hsq : ConvexOn ℝ univ (fun y : ℝ => y ^ 2) :=
    (by norm_num : Even (2 : ℕ)).convexOn_pow
  have hj := hsq.map_integral_le (continuous_id.pow 2).continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _ ) hgi hgsi
  simpa only [ν, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (K : Compacts E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual original scalar affine-line derivative, at every real parameter. -/
theorem line_hasDerivAt (f : 𝓓_{K}(E, ℝ)) (x h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + t • h) h) t := by
  have hf : HasFDerivAt f (fderiv ℝ f (x + t • h)) (x + t • h) :=
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h |>.const_add x)
  exact hf.comp_hasDerivAt t hl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The true ordinary derivative integral gives the entire original endpoint difference. -/
theorem line_integral_eq_sub (f : 𝓓_{K}(E, ℝ)) (x h : E) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • h) h) = f (x + h) - f x := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • h) h) := by
    simp_rw [← directionalStageCLM_apply K h f]
    exact (directionalStageCLM K h f).continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => line_hasDerivAt K f x h t) (hc.intervalIntegrable 0 1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise quantitative square translation bound for the actual whole smooth function. -/
theorem translation_square_le_line_average (f : 𝓓_{K}(E, ℝ)) (x h : E) :
    (f (x + h) - f x) ^ 2 ≤ ∫ t in Ioc (0 : ℝ) 1,
      (fderiv ℝ f (x + t • h) h) ^ 2 := by
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • h) h) := by
    simp_rw [← directionalStageCLM_apply K h f]
    exact (directionalStageCLM K h f).continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))
  simpa only [line_integral_eq_sub K f x h] using unit_interval_square_le hc


variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Actual whole-space square translation bound in nonnegative extended integrals. -/
theorem lintegral_translation_square_le (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫⁻ x, ENNReal.ofReal ((f (x + h) - f x) ^ 2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal ((fderiv ℝ f x h) ^ 2) ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hc (x : E) : Continuous (fun t : ℝ => fderiv ℝ f (x + t • h) h) := by
    simp_rw [← directionalStageCLM_apply K h f]
    exact (directionalStageCLM K h f).continuous.comp (continuous_const.add
      (continuous_id.smul continuous_const))
  have hi (x : E) : Integrable (fun t : ℝ => (fderiv ℝ f (x + t • h) h) ^ 2) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (((hc x).pow 2).intervalIntegrable 0 1)
  have hm : Measurable (fun z : E × ℝ =>
      ENNReal.ofReal ((fderiv ℝ f (z.1 + z.2 • h) h) ^ 2)) := by
    simp_rw [← directionalStageCLM_apply K h f]
    exact ENNReal.measurable_ofReal.comp (((directionalStageCLM K h f).continuous.comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).pow 2).measurable
  calc
    _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal ((fderiv ℝ f (x + t • h) h) ^ 2) ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact (ENNReal.ofReal_le_ofReal (translation_square_le_line_average K f x h)).trans_eq
        (ofReal_integral_eq_lintegral_ofReal (hi x)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _))
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal ((fderiv ℝ f (x + t • h) h) ^ 2) ∂μ ∂ν :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal ((fderiv ℝ f x h) ^ 2) ∂μ := by
      simp_rw [lintegral_add_right_eq_self (fun x =>
        ENNReal.ofReal ((fderiv ℝ f x h) ^ 2))]
      simp

/-- The same actual finite square translation inequality for real integrals. -/
theorem integral_translation_square_le (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤ ∫ x, (fderiv ℝ f x h) ^ 2 ∂μ := by
  have hf : MemLp (f : E → ℝ) 2 μ :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hd : MemLp (fun x => fderiv ℝ f x h) 2 μ := by
    simp_rw [← directionalStageCLM_apply K h f]
    exact (directionalStageCLM K h f).continuous.memLp_of_hasCompactSupport
      (directionalStageCLM K h f).hasCompactSupport
  have ht : MemLp (fun x => f (x + h) - f x) 2 μ :=
    (hf.comp_measurePreserving (measurePreserving_add_right μ h)).sub hf
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal ht.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hd.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_translation_square_le K μ f h

/-- Literal readback of the actual compact-test derivative L² norm in the translation bound. -/
theorem integral_translation_square_le_directional_norm (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
      ‖scalarStageL2 μ K (directionalStageCLM K h f)‖ ^ 2 := by
  rw [scalarStageL2_norm_sq]
  simpa only [directionalStageCLM_apply] using integral_translation_square_le K μ f h

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevTranslation
