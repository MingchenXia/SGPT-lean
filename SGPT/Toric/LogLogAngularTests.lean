import SGPT.Toric.LogLogRadialMeasure
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The actual angular average of an original signed complex test. -/
def logLogAngularAverage (η : ℂ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, η (logLogRadialPoint (x, t)) ∂logLogAngularMeasure

/-- One produced compact-test bound dominates all angles and all radial parameters. -/
theorem continuous_logLogAngularAverage {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η) :
    Continuous (logLogAngularAverage η) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuous hη
  unfold logLogAngularAverage
  apply continuous_of_dominated (bound := fun _ : ℝ => C)
  · intro x
    exact (hη.comp (continuous_logLogRadialPoint.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun t => hC (logLogRadialPoint (x, t))
  · exact integrable_const C
  · exact Eventually.of_forall fun t => hη.comp
      (continuous_logLogRadialPoint.comp (continuous_id.prodMk continuous_const))

/-- The true punctured support supplies a compact radial window, including the zero test. -/
theorem exists_logLogRadial_test_window {η : ℂ → ℝ}
    (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) :
    ∃ a b : ℝ, ∀ x t : ℝ, η (logLogRadialPoint (x, t)) ≠ 0 → x ∈ Icc a b := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport η).isOpen_compl.mem_nhds hzero)
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨2 * Real.log ε, 2 * Real.log R, ?_⟩
  intro x t hη
  have hmem : logLogRadialPoint (x, t) ∈ tsupport η := subset_tsupport η hη
  have hlow : ε ≤ ‖logLogRadialPoint (x, t)‖ := by
    by_contra hn
    have hin : logLogRadialPoint (x, t) ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hn
    exact hball hin hmem
  have hupp := hbound (logLogRadialPoint (x, t)) hmem
  rw [norm_logLogRadialPoint] at hlow hupp
  have hlo := (Real.log_le_iff_le_exp hε).2 hlow
  have hhi := (Real.le_log_iff_exp_le hR).2 hupp
  exact ⟨by linarith, by linarith⟩

/-- Actual vanishing outside the produced radial interval gives genuine compact support. -/
theorem hasCompactSupport_logLogAngularAverage {η : ℂ → ℝ}
    (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) :
    HasCompactSupport (logLogAngularAverage η) := by
  obtain ⟨a, b, hwindow⟩ := exists_logLogRadial_test_window hK hzero
  apply HasCompactSupport.intro (K := Icc a b) isCompact_Icc
  intro x hx
  have hz : (fun t : ℝ => η (logLogRadialPoint (x, t))) = fun _ => 0 := by
    funext t
    by_contra hn
    exact hx (hwindow x t hn)
  unfold logLogAngularAverage
  rw [hz]
  simp

/-- Bounded original compact tests are truly integrable for every finite radial input. -/
theorem integrable_logLogRadial_test {η : ℂ → ℝ} (hη : Continuous η)
    (hK : HasCompactSupport η) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun p : ℝ × ℝ => η (logLogRadialPoint p))
      (μ.prod logLogAngularMeasure) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuous hη
  apply Integrable.of_bound (hη.comp continuous_logLogRadialPoint).aestronglyMeasurable C
  exact Eventually.of_forall fun p => hC (logLogRadialPoint p)

/-- Fubini produces integrability of the genuine angular average. -/
theorem integrable_logLogAngularAverage {η : ℂ → ℝ} (hη : Continuous η)
    (hK : HasCompactSupport η) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (logLogAngularAverage η) μ := by
  exact (integrable_logLogRadial_test hη hK μ).integral_prod_left

/-- The actual product-map integral reduces every signed test to its true angular average. -/
theorem integral_map_logLogRadialPoint {η : ℂ → ℝ} (hη : Continuous η)
    (hK : HasCompactSupport η) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ z, η z ∂Measure.map logLogRadialPoint (μ.prod logLogAngularMeasure)) =
      ∫ x, logLogAngularAverage η x ∂μ := by
  rw [integral_map_of_stronglyMeasurable continuous_logLogRadialPoint.measurable
    hη.stronglyMeasurable, integral_prod _ (integrable_logLogRadial_test hη hK μ)]
  rfl

/-- Specialization to the actual checked Alexandrov radial measure; no complex identity is input. -/
theorem integral_logLogRadialMeasure {η : ℂ → ℝ} (hη : Continuous η)
    (hK : HasCompactSupport η) :
    (∫ z, η z ∂logLogRadialMeasure) =
      ∫ x, logLogAngularAverage η x ∂logLogAlexandrovMeasure :=
  integral_map_logLogRadialPoint hη hK logLogAlexandrovMeasure

end SGPT.Toric
