import SGPT.Toric.ProjectiveLineLogSingularity
import SGPT.Toric.ProjectiveLineSection
import SGPT.PSH.VariableLelong
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

/-!
# The key example of `ex:Lelongcurrent`

Source: `ex:Lelongcurrent` of the chapter *Plurisubharmonic functions*. Besides the convention
`ν(T, x) = ν(φ, x)` for `T = θ + ddᶜφ ∈ 𝒵₊(X)` (which needs the space of closed positive currents,
not formalized), the example records two computations:

* `(i/2π) ∂∂̄ log |z|² = δ₀` on `ℂ` (`ddC_log_normSq_eq_zeroCurrent`,
  `ddC_log_normSq_apply_standard`): in the project's normalization `ddᶜ = (i/2π)∂∂̄`, the
  distributional `ddᶜ log |z|²` is the integration current `[0]`, whose value on the oriented
  pair `(1, i)` is the Dirac mass at `0`;
* `ν([0], 0) = 1` on `ℙ¹` (`sourceLelong_projectiveLogSingularity_zero`): the current of
  integration `[0] = ω_FS + ddᶜφ` (Lelong–Poincaré, `ex:LPP1`, with the potential
  `φ = log (|z|²/(1+|z|²))` of `ex:logsingP1`) and the source Lelong number of `φ` at `0` is `1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate ENNReal Distributions

namespace SGPT.PSH.LelongCurrentExample

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Toric
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

/-- `ddᶜ log |z|² = [0]` on `ℂ`, as distribution-valued two-forms (`ddᶜ = (i/2π)∂∂̄`). -/
theorem ddC_log_normSq_eq_zeroCurrent :
    LocalCurrents.ddC (regularDistribution volume (fun z : ComplexModel 1 ↦
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) locallyIntegrable_projectiveCoordinateLog) =
      projectiveCoordinateZeroCurrent := by
  have hlog := Pending.DivisorIntegrationCurrent.ddC_log_normSq_eq_divisorCurrent
    (Ω := (⊤ : TopologicalSpace.Opens (ComplexModel 1)))
    projectiveModelEquiv.symm.differentiable.differentiableOn
    (fun z _ ↦ projectiveCoordinate_frequently_ne_zero z)
  exact hlog

/-- `(i/2π) ∂∂̄ log |z|² = δ₀`: on the standard oriented real basis `(1, i)` of `ℂ`, the current
`ddᶜ log |z|²` is the Dirac distribution at `0`; on a general pair `(v, w)` it is
`Im(v̄ w) δ₀`. -/
theorem ddC_log_normSq_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun z : ComplexModel 1 ↦
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) locallyIntegrable_projectiveCoordinateLog)
      ![v, w] φ = φ 0 * (conj (v 0) * w 0).im := by
  rw [ddC_log_normSq_eq_zeroCurrent, projectiveCoordinateZeroCurrent_apply]

theorem ddC_log_normSq_apply_standard
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun z : ComplexModel 1 ↦
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) locallyIntegrable_projectiveCoordinateLog)
      ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I] φ = φ 0 := by
  rw [ddC_log_normSq_eq_zeroCurrent, projectiveCoordinateZeroCurrent_apply_standard]

/-- On `ℙ¹`, `[0] = ω_FS + ddᶜφ` with `φ = log (|z|²/(1+|z|²))` on the affine chart
(`ex:LPP1`, `ex:logsingP1`); `φ` is `ω_FS`-psh. -/
theorem zeroCurrent_eq_fubiniStudy_add_ddC :
    projectiveFSCurvatureCurrent + projectiveCoordinateMetricLogCurrent =
      projectiveCoordinateZeroCurrent ∧
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogSingularity :=
  ⟨projectiveCoordinateSection_lelongPoincare, isThetaPSH_projectiveLogSingularity⟩

theorem projectiveModelChart_target (b : Bool) : (projectiveModelChart b).target = univ := by
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

/-- The point `0 = [0 : 1]` of `ℙ¹` in the affine chart. -/
def projectiveZero : Projectivization ℂ (Fin 2 → ℂ) := (projectiveModelChart false).symm 0

theorem norm_eq_coord (z : ComplexModel 1) : ‖z‖ = ‖z 0‖ := by
  rw [← projectiveModelEquiv_symm_norm, projectiveModelEquiv_symm_apply]

/-- `ν([0], 0) = 1`: the source Lelong number at `0 ∈ ℙ¹` of the potential `φ` of `[0]`. -/
theorem sourceLelong_projectiveLogSingularity_zero :
    projectiveLineAtlas.sourceLelong projectiveLogSingularity projectiveZero = 1 := by
  have hsrc : projectiveZero ∈ (projectiveModelChart false).source :=
    (projectiveModelChart false).map_target (by rw [projectiveModelChart_target]; trivial)
  have hchart : projectiveModelChart false projectiveZero = 0 :=
    (projectiveModelChart false).right_inv (by rw [projectiveModelChart_target]; trivial)
  rw [projectiveLineAtlas.sourceLelong_eq_chart projectiveLogSingularity projectiveZero false hsrc]
  change squaredLogLelongNumber (n := 1)
    (fun z => projectiveLogSingularity ((projectiveModelChart false).symm z))
    (projectiveModelChart false projectiveZero) = 1
  rw [hchart]
  -- the chart expression is `log |z|²` plus a continuous real function
  set h : ComplexModel 1 → ℝ := fun z => -Real.log (1 + Complex.normSq (z 0)) with hh
  have hexpr : (fun z => projectiveLogSingularity ((projectiveModelChart false).symm z)) =
      fun z : ComplexModel 1 => ENNReal.log (ENNReal.ofReal (‖z‖ ^ 2)) + (h z : EReal) := by
    funext z
    rw [projectiveLogSingularity_finite, norm_eq_coord]
    have hpos : 0 < 1 + Complex.normSq (z 0) := by
      have := Complex.normSq_nonneg (z 0); linarith
    have hsplit : Complex.normSq (z 0) / (1 + Complex.normSq (z 0)) =
        ‖z 0‖ ^ 2 * (1 + Complex.normSq (z 0))⁻¹ := by
      rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
    rw [hsplit, ENNReal.ofReal_mul (by positivity), ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos (inv_pos.mpr hpos), Real.log_inv]
  rw [hexpr]
  have hcont : ContinuousAt h 0 := by
    have : Continuous h := by
      apply Continuous.neg
      apply Continuous.log
      · exact continuous_const.add
          (Complex.continuous_normSq.comp ((continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)))
      · intro z
        have := Complex.normSq_nonneg (z 0)
        exact ne_of_gt (by linarith)
    exact this.continuousAt
  have h2 := Pending.SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (n := 1) (M := ComplexModel 1) one_ne_zero
  have hadd := Pending.LelongChartReaderInvariance.lelongNumber_add_continuous_eq (n := 1)
    (M := ComplexModel 1) (u := fun z : ComplexModel 1 => ENNReal.log (ENNReal.ofReal (‖z‖ ^ 2)))
    (x := 0) hcont
  rw [h2, h2] at hadd
  have hone := VariableComplexAtlas.squaredLogLelongNumber_radial_square_eq_one (n := 1) one_ne_zero
  have hcancel := (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hadd
  rw [hcancel, hone]

end SGPT.PSH.LelongCurrentExample
