import SGPT.Toric.LogLogScalarHessianMeasure
import SGPT.Toric.LogLogPolarIntegral
import SGPT.Toric.LogLogRadialContinuity
import SGPT.Convex.SmoothMixedAlexandrov

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Convex SGPT.Foundations.Analysis
open scoped Topology ContDiff ENNReal RealInnerProductSpace

/-- Actual singleton Hessian continuity reuses the complete original matrix producer. -/
theorem continuous_scalarHessian {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    Continuous (fun x : ℝ => realHessian h x 1 1) := by
  have H := (continuous_hessianMatrix_of_contDiff (E := ℝ) (n := 1)
    (OrthonormalBasis.singleton (Fin 1) ℝ) hh).matrix_det
  exact H.congr (fun x => det_scalarHessianMatrix h x)

/-- Genuine smooth convex PSD, rather than an assumed scalar density sign. -/
theorem scalarHessian_nonneg_of_convex_smooth {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) (x : ℝ) :
    0 ≤ realHessian h x 1 1 := by
  have H := (hessianMatrix_posSemidef_of_contDiff_convex (E := ℝ) (n := 1)
    (OrthonormalBasis.singleton (Fin 1) ℝ) hc hh x).det_nonneg
  exact (det_scalarHessianMatrix h x).symm ▸ H

/-- The genuine original rank-one density transfers the same signed function. -/
theorem integral_scalarAlexandrov_eq_hessian {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) (F : ℝ → ℝ) :
    (∫ x, F x ∂alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))) =
      ∫ x : ℝ, realHessian h x 1 1 * F x := by
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (realHessian h x 1 1)) :=
    (ENNReal.continuous_ofReal.comp (continuous_scalarHessian hh)).measurable
  rw [alexandrovMeasure_scalar_eq_withDensity_hessian hc hh,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (ENNReal.ofReal (realHessian h x 1 1)).toReal • F x = realHessian h x 1 1 * F x
    rw [ENNReal.toReal_ofReal (scalarHessian_nonneg_of_convex_smooth hc hh x), smul_eq_mul]

/-- Full signed punctured compact tests identify the original smooth coefficient and radial map. -/
theorem integral_smoothScalarDensity_eq_radialAlexandrov {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) :
    (∫ z : ℂ, radialScalarTestDensity (fun x => realHessian h x 1 1) η z) =
      ∫ z, η z ∂Measure.map logLogRadialPoint
        ((alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))).prod
          logLogAngularMeasure) := by
  let : IsLocallyFiniteMeasure
      (alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))) :=
    isLocallyFiniteMeasure_alexandrovMeasure_coe scalarPairing hc
  rw [integral_map_logLogRadialPoint_of_locallyFinite hη hK hzero]
  exact (integral_radialScalarTestDensity (continuous_scalarHessian hh) hη hK hzero).trans
    (integral_scalarAlexandrov_eq_hessian hc hh (logLogAngularAverage η)).symm

/-- The genuine whole scalar density test limit retains the actual corner circle atom. -/
theorem tendsto_integral_smoothScalarDensity_logLog {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) :
    Tendsto (fun j => ∫ z : ℂ, radialScalarTestDensity
      (fun x => realHessian (finiteConvexSmoothApprox volume logLogProfile j) x 1 1) η z)
      atTop (𝓝 (∫ z, η z ∂logLogRadialMeasure)) := by
  have heq (j : ℕ) := integral_smoothScalarDensity_eq_radialAlexandrov
    (convexOn_finiteConvexSmoothApprox volume convexOn_logLogProfile j)
    (contDiff_finiteConvexSmoothApprox volume convexOn_logLogProfile j) hη hK hzero
  simp_rw [heq]
  exact tendsto_integral_radialMap_smooth_logLog hη hK hzero

end SGPT.Toric
