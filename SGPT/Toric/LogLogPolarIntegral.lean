import SGPT.Toric.LogLogPolarCoordinates
import SGPT.Toric.LogLogLogarithmicSubstitution
import SGPT.Toric.LogLogAngularTests
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Literal normalized scalar density paired with an original signed test. -/
def radialScalarTestDensity (ρ : ℝ → ℝ) (η : ℂ → ℝ) (z : ℂ) : ℝ :=
  ρ (Real.log (Complex.normSq z)) * η z / (Real.pi * Complex.normSq z)

/-- Actual off-zero continuity and genuine vanishing near zero preserve the total function. -/
theorem continuous_radialScalarTestDensity {ρ : ℝ → ℝ} {η : ℂ → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hzero : (0 : ℂ) ∉ tsupport η) :
    Continuous (radialScalarTestDensity ρ η) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), z ∉ tsupport η :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hzero
    have heq : radialScalarTestDensity ρ η =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
      filter_upwards [hev] with z hz
      have hηz : η z = 0 := by
        by_contra hn
        exact hz (subset_tsupport η hn)
      simp [radialScalarTestDensity, hηz]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have hns : Complex.normSq z ≠ 0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hlog : ContinuousAt (fun w : ℂ => Real.log (Complex.normSq w)) z :=
      (Real.continuousAt_log hns).comp Complex.continuous_normSq.continuousAt
    exact ((hρ.continuousAt.comp hlog).mul hη.continuousAt).div
      (continuous_const.mul Complex.continuous_normSq).continuousAt
      (mul_ne_zero Real.pi_ne_zero hns)

/-- The actual topological support is contained in the original compact test support. -/
theorem hasCompactSupport_radialScalarTestDensity (ρ : ℝ → ℝ) {η : ℂ → ℝ}
    (hK : HasCompactSupport η) : HasCompactSupport (radialScalarTestDensity ρ η) := by
  apply HasCompactSupport.intro (K := tsupport η) hK
  intro z hz
  have hηz : η z = 0 := by
    by_contra hn
    exact hz (subset_tsupport η hn)
  simp [radialScalarTestDensity, hηz]

/-- Genuine integrability follows from actual continuity and compact support. -/
theorem integrable_radialScalarTestDensity {ρ : ℝ → ℝ} {η : ℂ → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) : Integrable (radialScalarTestDensity ρ η) :=
  (continuous_radialScalarTestDensity hρ hη hzero).integrable_of_hasCompactSupport
    (hasCompactSupport_radialScalarTestDensity ρ hK)

/-- The produced real angular test has true compact-support integrability. -/
theorem integrable_scalarAngular_test {ρ : ℝ → ℝ} {η : ℂ → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) :
    Integrable (fun x : ℝ => ρ x * logLogAngularAverage η x) := by
  have hA := hasCompactSupport_logLogAngularAverage hK hzero
  have hcomp : HasCompactSupport (fun x : ℝ => ρ x * logLogAngularAverage η x) := by
    apply HasCompactSupport.intro (K := tsupport (logLogAngularAverage η)) hA
    intro x hx
    have hz : logLogAngularAverage η x = 0 := by
      by_contra hn
      exact hx (subset_tsupport (logLogAngularAverage η) hn)
    simp [hz]
  exact (hρ.mul (continuous_logLogAngularAverage hη hK)).integrable_of_hasCompactSupport hcomp

/-- The original probability normalization supplies the literal full-angle integral. -/
theorem integral_angle_eq_logLogAngularAverage (η : ℂ → ℝ) (x : ℝ) :
    (∫ t in Ioo (-Real.pi) Real.pi, η (logLogRadialPoint (x, t))) =
      (2 * Real.pi) * logLogAngularAverage η x := by
  unfold logLogAngularAverage logLogAngularMeasure
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi)),
    integral_Ioc_eq_integral_Ioo]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    Real.pi_ne_zero), one_mul]

/-- The genuine polar Jacobian theorem manufactures signed pullback integrability. -/
theorem integrableOn_polar_scalar_test {ρ : ℝ → ℝ} {η : ℂ → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 *
      radialScalarTestDensity ρ η (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  let f : ℂ → ℝ := radialScalarTestDensity ρ η
  have hf : Integrable f := integrable_radialScalarTestDensity hρ hη hK hzero
  have hreal : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf
  have H := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (s := polarCoord.target) (f := polarCoord.symm) (f' := fderivPolarCoordSymm)
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn (f ∘ Complex.measurableEquivRealProd.symm)
  have hi := H.mp hreal.integrableOn
  apply hi.congr_fun _ polarCoord.open_target.measurableSet
  intro p hp
  change |(fderivPolarCoordSymm p).det| •
      f (Complex.measurableEquivRealProd.symm (polarCoord.symm p)) = _
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1, smul_eq_mul,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply]

/-- Every original signed punctured compact test has the exact full scalar integral. -/
theorem integral_radialScalarTestDensity {ρ : ℝ → ℝ} {η : ℂ → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hzero : (0 : ℂ) ∉ tsupport η) :
    (∫ z : ℂ, radialScalarTestDensity ρ η z) =
      ∫ x : ℝ, ρ x * logLogAngularAverage η x := by
  have hi := integrableOn_polar_scalar_test hρ hη hK hzero
  rw [← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 * radialScalarTestDensity ρ η (Complex.polarCoord.symm p)) = _
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ hi]
  calc
    (∫ r in Ioi (0 : ℝ), ∫ t in Ioo (-Real.pi) Real.pi,
      r * radialScalarTestDensity ρ η (Complex.polarCoord.symm (r, t))) =
        ∫ r in Ioi (0 : ℝ), 2 * (r⁻¹ *
          (ρ (2 * Real.log r) * logLogAngularAverage η (2 * Real.log r))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change 0 < r at hr
      change (∫ t in Ioo (-Real.pi) Real.pi,
        r * radialScalarTestDensity ρ η (Complex.polarCoord.symm (r, t))) =
        2 * (r⁻¹ * (ρ (2 * Real.log r) * logLogAngularAverage η (2 * Real.log r)))
      have heq : (fun t : ℝ => r *
          radialScalarTestDensity ρ η (Complex.polarCoord.symm (r, t))) =
          fun t => (ρ (2 * Real.log r) / (Real.pi * r)) *
            η (logLogRadialPoint (2 * Real.log r, t)) := by
        funext t
        unfold radialScalarTestDensity
        calc
          _ = (r * (ρ (Real.log (Complex.normSq (Complex.polarCoord.symm (r, t)))) /
            (Real.pi * Complex.normSq (Complex.polarCoord.symm (r, t))))) *
              η (Complex.polarCoord.symm (r, t)) := by ring
          _ = _ := by rw [polarJacobian_scalarDensity ρ hr,
            polarCoord_symm_eq_logLogRadialPoint hr]
      rw [heq, integral_const_mul, integral_angle_eq_logLogAngularAverage]
      field_simp [hr.ne', Real.pi_ne_zero]
    _ = 2 * ∫ r in Ioi (0 : ℝ), r⁻¹ *
        (ρ (2 * Real.log r) * logLogAngularAverage η (2 * Real.log r)) :=
      integral_const_mul _ _
    _ = ∫ x : ℝ, ρ x * logLogAngularAverage η x := by
      rw [integral_squaredLog_substitution (fun x => ρ x * logLogAngularAverage η x)]
      ring

end SGPT.Toric
