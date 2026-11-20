import SGPT.Toric.ScalarPuncturedBedfordTaylor
import SGPT.Toric.ProjectiveLogLogPuncturedPatch

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
open scoped Topology ContDiff Distributions ENNReal

local notation "D" => projectiveLogLogPuncturedDomain

private def logLogSmoothProfile (j : ℕ) : ℝ → ℝ :=
  finiteConvexSmoothApprox volume logLogProfile j

private theorem scalarPuncturedProfile_logLog_eq :
    scalarPuncturedProfile logLogProfile = projectiveLogLogCorrectedProfile := by
  funext z
  rw [scalarPuncturedProfile, tropicalization_apply_eq_log_norm_sq,
    projectiveLogLogCorrectedProfile]

theorem tendstoLocallyUniformlyOn_scalarPuncturedProfile_smooth_logLog :
    TendstoLocallyUniformlyOn (fun j => scalarPuncturedProfile (logLogSmoothProfile j))
      projectiveLogLogCorrectedProfile atTop D := by
  simpa only [logLogSmoothProfile, scalarPuncturedProfile_logLog_eq,
    scalarPuncturedBTDomain, projectiveLogLogPuncturedDomain]
    using tendstoLocallyUniformlyOn_scalarPuncturedProfile_smoothApprox convexOn_logLogProfile

/-- The original canonical construction is retained literally. -/
def logLogCanonicalBTMeasure : Measure (ComplexModel 1) :=
  canonicalMixedBedfordTaylorMeasure D
    (fun _ : Fin 1 => projectiveLogLogCorrectedProfile)
    (fun _ => isLocallyBoundedPshOn_projectiveLogLogCorrectedProfile)

private theorem logLogCanonicalBTMeasure_eq_scalar :
    logLogCanonicalBTMeasure = scalarCanonicalBTMeasure convexOn_logLogProfile := by
  simp only [logLogCanonicalBTMeasure, scalarCanonicalBTMeasure,
    scalarPuncturedProfile_logLog_eq, scalarPuncturedBTDomain,
    projectiveLogLogPuncturedDomain]

theorem tendsto_integral_canonicalBT_smooth_logLog {g : ComplexModel 1 → ℝ}
    (hg : Continuous g) (hK : HasCompactSupport g) (hU : tsupport g ⊆ D) :
    Tendsto (fun j => ∫ z, g z ∂scalarPuncturedSmoothMeasure
      (convexOn_finiteConvexSmoothApprox volume convexOn_logLogProfile j)
      (contDiff_finiteConvexSmoothApprox volume convexOn_logLogProfile j)) atTop
      (𝓝 (∫ z, g z ∂logLogCanonicalBTMeasure)) := by
  rw [logLogCanonicalBTMeasure_eq_scalar]
  exact tendsto_integral_scalarCanonicalBT_smoothApprox convexOn_logLogProfile hg hK hU

theorem integral_logLogCanonicalBT_eq_radial {g : ComplexModel 1 → ℝ}
    (hg : Continuous g) (hK : HasCompactSupport g) (hU : tsupport g ⊆ D) :
    (∫ z, g z ∂logLogCanonicalBTMeasure) =
      ∫ z, g (projectiveModelEquiv z) ∂logLogRadialMeasure := by
  rw [logLogCanonicalBTMeasure_eq_scalar]
  exact integral_scalarCanonicalBT_eq_radial convexOn_logLogProfile hg hK hU

theorem logLogCanonicalBT_eq_map_radial :
    logLogCanonicalBTMeasure = Measure.map projectiveModelEquiv logLogRadialMeasure := by
  rw [logLogCanonicalBTMeasure_eq_scalar]
  exact scalarCanonicalBT_eq_map_radial convexOn_logLogProfile

end SGPT.Toric
