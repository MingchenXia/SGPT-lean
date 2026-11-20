import SGPT.Trace.OptimalNormalRegularization
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable

/-!
# Exact pi mass and convergence of the actual sharp normal kernel

This is the literal rational normal kernel with ordinary complex Lebesgue
measure, obtained from the exact half-scaled existing PL kernel. Intrinsic
canonical/residue/Hodge density remains a separate dictionary.
Blueprint: work/sgpt-resume-20261114/bert-e2-residue-kernel/blueprint/bert-e2-residue-kernel.tex.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNormalResidueKernel
open Set Filter MeasureTheory
open scoped Topology ContDiff Laplacian
open SGPT.Trace.OptimalNormalRegularization
open SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable

/-- Exactly the rational normal data kernel already produced by the
original scalar normal regularization, on ordinary complex Lebesgue space. -/
def residueKernel (ε : ℝ) (z : ℂ) : ℝ := normalKernel ε (‖z‖ ^ 2)

theorem residueKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    0 ≤ residueKernel ε z := normalKernel_nonneg hε

/-- The literal kernel dictionary carries the exact one-half factor. -/
theorem residueKernel_half_laplacian {a : ℝ} (ha : 0 < a) (z : ℂ) :
    residueKernel (a ^ 2) z = (1 / 2 : ℝ) * Δ (regLog a) z := by
  rw [laplacian_regLog ha]
  unfold residueKernel normalKernel
  rw [add_comm (a ^ 2)]
  ring

/-- Actual normal change of variables, with no normalization certificate. -/
theorem integral_squared_residueKernel_mul {a : ℝ} (ha : 0 < a) (χ : ℂ → ℝ) :
    (∫ z, residueKernel (a ^ 2) z * χ z) =
      (1 / 2 : ℝ) * ∫ w, kernel w * χ (a • w) := by
  have he : (fun z => residueKernel (a ^ 2) z * χ z) =
      (fun z => (1 / 2 : ℝ) * (Δ (regLog a) z * χ z)) := by
    funext z
    rw [residueKernel_half_laplacian ha]
    ring
  rw [he, integral_const_mul, integral_laplacian_regLog_mul ha χ]

theorem integral_residueKernel_mul {ε : ℝ} (hε : 0 < ε) (χ : ℂ → ℝ) :
    (∫ z, residueKernel ε z * χ z) =
      (1 / 2 : ℝ) * ∫ w, kernel w * χ (Real.sqrt ε • w) := by
  have h := integral_squared_residueKernel_mul (Real.sqrt_pos.mpr hε) χ
  simpa only [Real.sq_sqrt hε.le] using h

/-- The original ordinary complex normal mass is pi exactly. -/
theorem integral_residueKernel {ε : ℝ} (hε : 0 < ε) :
    (∫ z, residueKernel ε z) = Real.pi := by
  calc
    _ = (1 / 2 : ℝ) * ∫ w, kernel w := by
      simpa only [mul_one] using integral_residueKernel_mul hε (fun _ => 1)
    _ = _ := by rw [integral_kernel]; ring

theorem integrable_residueKernel {ε : ℝ} (hε : 0 < ε) : Integrable (residueKernel ε) := by
  by_contra h
  have hz : (∫ z, residueKernel ε z) = 0 := integral_undef h
  rw [integral_residueKernel hε] at hz
  exact Real.pi_ne_zero hz

theorem integrable_residueKernel_mul {ε : ℝ} (hε : 0 < ε) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => residueKernel ε z * χ z) := by
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hK := integrable_residueKernel hε
  refine (hK.mul_const C).mono'
    (hK.aestronglyMeasurable.mul hχ.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun z => by
    rw [norm_mul, Real.norm_of_nonneg (residueKernel_nonneg hε.le z)]
    exact mul_le_mul_of_nonneg_left (hC z) (residueKernel_nonneg hε.le z)

/-- The actual scalar Lebesgue kernel has the exact sharp residue limit.
No intrinsic canonical/Hodge density identification is asserted here. -/
theorem tendsto_integral_residueKernel_mul {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun ε : ℝ => ∫ z, residueKernel ε z * χ z)
      (𝓝[>] 0) (𝓝 (Real.pi * χ 0)) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      ((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hlim := ((tendsto_integral_kernel_mul hχ hχc).comp hsqrt).const_mul (1 / 2 : ℝ)
  have he : (1 / 2 : ℝ) * (2 * Real.pi * χ 0) = Real.pi * χ 0 := by ring
  rw [he] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_residueKernel_mul hε χ).symm

end SGPT.Trace.OptimalNormalResidueKernel
