import SGPT.Toric.LogLogAlexandrovMass
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory
open scoped ENNReal Topology

/-- A true angular probability, with the original full circle and standard real Lebesgue measure. -/
def logLogAngularMeasure : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ • volume.restrict (Ioc (-Real.pi) Real.pi)

theorem logLogAngularMeasure_univ : logLogAngularMeasure univ = 1 := by
  rw [logLogAngularMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))]
  rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)]
  simp

instance logLogAngularMeasure_isProbabilityMeasure : IsProbabilityMeasure logLogAngularMeasure :=
  ⟨logLogAngularMeasure_univ⟩

instance logLogAlexandrovMeasure_isProbabilityMeasure : IsProbabilityMeasure logLogAlexandrovMeasure :=
  ⟨logLogAlexandrovMeasure_univ⟩

/-- The genuine radial point map, with squared-log coordinate x and literal angular parameter t. -/
def logLogRadialPoint (p : ℝ × ℝ) : ℂ :=
  Complex.exp ((p.1 / 2 : ℝ) + (p.2 : ℂ) * Complex.I)

theorem continuous_logLogRadialPoint : Continuous logLogRadialPoint := by
  unfold logLogRadialPoint
  fun_prop

theorem norm_logLogRadialPoint (p : ℝ × ℝ) :
    ‖logLogRadialPoint p‖ = Real.exp (p.1 / 2) := by
  simp [logLogRadialPoint, Complex.norm_exp, Complex.add_re, Complex.mul_re]

theorem logLogRadialPoint_ne_zero (p : ℝ × ℝ) : logLogRadialPoint p ≠ 0 := by
  intro h
  have hn := norm_logLogRadialPoint p
  rw [h, norm_zero] at hn
  exact (Real.exp_pos (p.1 / 2)).ne' hn.symm

/-- This actual map is kept distinct from the original complex product until full calibration. -/
def logLogRadialMeasure : Measure ℂ :=
  Measure.map logLogRadialPoint (logLogAlexandrovMeasure.prod logLogAngularMeasure)

theorem logLogRadialMeasure_univ : logLogRadialMeasure univ = 1 := by
  rw [logLogRadialMeasure,
    Measure.map_apply continuous_logLogRadialPoint.measurable MeasurableSet.univ,
    preimage_univ, measure_univ]

instance logLogRadialMeasure_isProbabilityMeasure : IsProbabilityMeasure logLogRadialMeasure :=
  ⟨logLogRadialMeasure_univ⟩

theorem logLogRadialMeasure_origin : logLogRadialMeasure {0} = 0 := by
  rw [logLogRadialMeasure,
    Measure.map_apply continuous_logLogRadialPoint.measurable (measurableSet_singleton 0)]
  have hempty : logLogRadialPoint ⁻¹' ({0} : Set ℂ) = ∅ := by
    ext p
    simp [logLogRadialPoint_ne_zero p]
  rw [hempty, measure_empty]

/-- The actual norm-level preimage is the whole angular line over the true corner. -/
theorem preimage_logLogRadialPoint_cornerCircle :
    logLogRadialPoint ⁻¹' {z : ℂ | ‖z‖ = Real.exp (-logLogLambda / 2)} =
      {-logLogLambda} ×ˢ (univ : Set ℝ) := by
  ext p
  simp only [mem_preimage, mem_ofPred_eq, norm_logLogRadialPoint,
    mem_prod, mem_singleton_iff, mem_univ, and_true]
  constructor
  · intro h
    have hr := Real.exp_injective h
    linarith
  · intro h
    rw [h]

/-- Exact positive circle mass, not an AE density substitution. -/
theorem logLogRadialMeasure_cornerCircle :
    logLogRadialMeasure {z : ℂ | ‖z‖ = Real.exp (-logLogLambda / 2)} =
      ENNReal.ofReal (1 - logLogLambda⁻¹) := by
  rw [logLogRadialMeasure,
    Measure.map_apply continuous_logLogRadialPoint.measurable
      ((isClosed_eq continuous_norm continuous_const).measurableSet),
    preimage_logLogRadialPoint_cornerCircle, Measure.prod_prod,
    logLogAngularMeasure_univ, mul_one, logLogAlexandrovMeasure_corner]

end SGPT.Toric
