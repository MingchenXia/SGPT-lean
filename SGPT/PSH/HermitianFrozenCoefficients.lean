import SGPT.PSH.HermitianQuadratic
import SGPT.Foundations.Analysis.FirstPass.StandardHermitianTwoForm
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform freezing of smooth coordinate coefficients

On a fixed smaller coordinate ball, one derivative bound gives a uniform
linear-in-radius error about every centre. Constant real `(1,1)` forms
admit genuine global smooth quadratic potentials, including dimension zero.
These are the coefficient estimates used in FPT's extremal mass-support step.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianFrozenCoefficients

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open KahlerDomination LocalBedfordTaylorCollar LocalProductCurrents SmoothPotentialDomination
  StronglyPositiveForms
open scoped Topology ContDiff

variable {n : ℕ}

/-- The normalization of the actual full flat quadratic Hessian. -/
theorem smoothDDC_flat_quadratic (z : ComplexModel n) :
    smoothDDC (fun y : ComplexModel n => Real.pi * ‖y‖ ^ 2) z = kahlerForm n := by
  have hscaled : smoothDDC (fun y : ComplexModel n => Real.pi * ‖y‖ ^ 2) z =
      Real.pi • smoothDDC (fun y : ComplexModel n => ‖y‖ ^ 2) z := by
    simpa only [smul_eq_mul] using smoothDDC_smul isOpen_univ
      (contDiff_norm_sq ℝ).contDiffOn Real.pi (mem_univ z)
  have hnorm : smoothDDC (fun y : ComplexModel n => ‖y‖ ^ 2) z =
      Real.pi⁻¹ • kahlerForm n := by
    simpa only [sub_zero] using smoothDDC_norm_sub_sq (0 : ComplexModel n) z
  rw [hscaled, hnorm, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]

/-- Every constant real `(1,1)` two-form is the full Hessian of a global
smooth quadratic. A semipositive shift and an actual complex-linear map
give a concrete norm-square difference; no local-potential radius is used. -/
theorem exists_global_constant_potential
    (A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hA : IsOneOne A) :
    ∃ q : ComplexModel n → ℝ, ContDiff ℝ ∞ q ∧ ∀ z, smoothDDC q z = A := by
  let B := ‖A‖ • kahlerForm n + A
  have hB : IsSemipositiveOneOne B := (isSemipositiveOneOne_norm_smul_kahlerForm hA).2
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hB.1 hB.2
  let Sℂ : ComplexModel n →L[ℂ] ComplexModel n := LinearMap.toContinuousLinearMap S
  let Sℝ : ComplexModel n →L[ℝ] ComplexModel n :=
    LinearMap.toContinuousLinearMap (S.restrictScalars ℝ)
  let f : ComplexModel n → ℝ := fun z => Real.pi * ‖z‖ ^ 2
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hcomp : ContDiff ℝ ∞ (fun z => f (S z)) := hf.comp Sℝ.contDiff
  have hscaled : ContDiff ℝ ∞ (fun z => ‖A‖ * f z) := contDiff_const.mul hf
  have hddcS (z : ComplexModel n) : smoothDDC (fun y => f (S y)) z = B := by
    change smoothDDC (fun y => f (Sℂ y)) z = B
    rw [HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ
      Sℂ.contDiff.contDiffOn hf.contDiffOn (fun _ _ => mem_univ _) (mem_univ z)]
    have hder : fderiv ℝ (Sℂ : ComplexModel n → ComplexModel n) z = Sℝ :=
      Sℝ.hasFDerivAt.fderiv
    rw [show smoothDDC f (Sℂ z) = kahlerForm n from smoothDDC_flat_quadratic _, hder]
    exact hS.symm
  refine ⟨fun z => f (S z) - ‖A‖ * f z, hcomp.sub hscaled, fun z => ?_⟩
  rw [PositiveClasses.smoothDDC_sub isOpen_univ hcomp.contDiffOn hscaled.contDiffOn
    (mem_univ z), hddcS z]
  have hddcScale : smoothDDC (fun y => ‖A‖ * f y) z = ‖A‖ • kahlerForm n := by
    have hs := smoothDDC_smul isOpen_univ hf.contDiffOn (‖A‖) (mem_univ z)
    calc
      smoothDDC (fun y => ‖A‖ * f y) z = ‖A‖ • smoothDDC f z := by
        simpa only [smul_eq_mul] using hs
      _ = ‖A‖ • kahlerForm n := congrArg (fun T => ‖A‖ • T) (smoothDDC_flat_quadratic z)
  rw [hddcScale]
  dsimp only [B]
  abel

/-- One compact derivative bound controls all centres and all sufficiently
small radii in the same coordinate neighborhood. -/
theorem exists_uniform_local_norm_error
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ closedBall z₀ (4 * R) ⊆ U ∧
      ∀ x ∈ closedBall z₀ R, ∀ r : ℝ, 0 ≤ r → r ≤ R →
        ∀ z ∈ closedBall x (2 * r), ‖a z - a x‖ ≤ C * r := by
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  let R := s / 8
  have hR : 0 < R := by dsimp [R]; positivity
  have h4 : closedBall z₀ (4 * R) ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hball
  have h3 : closedBall z₀ (3 * R) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans h4
  have had : ContDiffOn ℝ ∞ (fderiv ℝ a) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp ha).2
  have hdnorm : ContinuousOn (fun y : ComplexModel n => ‖fderiv ℝ a y‖) U :=
    (continuous_norm (E :=
      ComplexModel n →L[ℝ] ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ))).comp_continuousOn
      had.continuousOn
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall z₀ (3 * R)).exists_bound_of_continuousOn
    (hdnorm.mono h3)
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ y ∈ closedBall z₀ (3 * R), ‖fderiv ℝ a y‖ ≤ B := by
    intro y hy
    have hb : ‖fderiv ℝ a y‖ ≤ B₀ := (Real.le_norm_self _).trans (hB₀ y hy)
    exact hb.trans (le_max_left _ _)
  have hdiff : ∀ y ∈ closedBall z₀ (3 * R), DifferentiableAt ℝ a y := fun y hy =>
    ((ha y (h3 hy)).contDiffAt (hU.mem_nhds (h3 hy))).differentiableAt (by simp)
  refine ⟨R, 2 * (B + 1), hR, by positivity, h4, ?_⟩
  intro x hx r hr hrR z hz
  have hx3 : x ∈ closedBall z₀ (3 * R) :=
    (closedBall_subset_closedBall (by linarith : R ≤ 3 * R)) hx
  have hz3 : z ∈ closedBall z₀ (3 * R) := by
    rw [mem_closedBall] at hx hz ⊢
    exact (dist_triangle z x z₀).trans (by linarith)
  have hlip := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall z₀ (3 * R)) hx3 hz3
  have hdist : ‖z - x‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  exact hlip.trans ((mul_le_mul_of_nonneg_left hdist hB).trans (by nlinarith))

/-- The frozen-form error is uniformly `O(r)` in every complex tangent
direction. No positivity or closedness of the original form is assumed. -/
theorem exists_uniform_local_line_error
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a U) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ closedBall z₀ (4 * R) ⊆ U ∧
      ∀ x ∈ closedBall z₀ R, ∀ r : ℝ, 0 ≤ r → r ≤ R →
        ∀ z ∈ closedBall x (2 * r), ∀ v : ComplexModel n,
          |a z ![v, Complex.I • v] - a x ![v, Complex.I • v]| ≤
            C * r * ‖v‖ ^ 2 := by
  obtain ⟨R, C, hR, hC, hball, herr⟩ := exists_uniform_local_norm_error hU a ha hz₀
  refine ⟨R, C, hR, hC, hball, fun x hx r hr hrR z hz v => ?_⟩
  have hop := abs_lineValue_le (a z - a x) v
  simp only [ContinuousAlternatingMap.sub_apply] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right (herr x hx r hr hrR z hz) (sq_nonneg _))

end SGPT.PSH.HermitianFrozenCoefficients
