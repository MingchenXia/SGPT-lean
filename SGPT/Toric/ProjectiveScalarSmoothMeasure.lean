import SGPT.Toric.LogLogSmoothDensity
import SGPT.Toric.LogLogSmoothCalibration
import SGPT.Foundations.Analysis.Pending.CoordinateDensityLowDim
import SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ContDiff ENNReal

private def scalarPuncturedDomain : TopologicalSpace.Opens (ComplexModel 1) :=
  ⟨complexTorus 1, isOpen_complexTorus 1⟩

local notation "D" => scalarPuncturedDomain

/-- The original singleton orthonormal coordinate, with its produced real isometry. -/
def projectiveModelRealIsometry : ℂ ≃ₗᵢ[ℝ] ComplexModel 1 where
  toLinearEquiv := projectiveModelEquiv.toLinearEquiv.restrictScalars ℝ
  norm_map' z := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.norm_map z

theorem measurePreserving_projectiveModelRealIsometry :
    MeasurePreserving projectiveModelRealIsometry :=
  projectiveModelRealIsometry.measurePreserving

/-- Literal squared-log scalar profile in the actual native model. -/
def scalarPuncturedProfile (h : ℝ → ℝ) (z : ComplexModel 1) : ℝ :=
  h (tropicalization z 0)

theorem convexOn_scalarTropicalProfile {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) :
    ConvexOn ℝ univ (scalarTropicalProfile h) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa [scalarTropicalProfile, PiLp.add_apply, PiLp.smul_apply]
    using hc.2 (mem_univ (x 0)) (mem_univ (y 0)) ha hb hab

theorem plurisubharmonicOn_scalarPuncturedProfile {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) :
    PlurisubharmonicOn (fun z => (scalarPuncturedProfile h z : EReal)) D := by
  exact plurisubharmonicOn_tropicalPullback_of_convexOn
    (convexOn_scalarTropicalProfile hc)

theorem contDiffOn_scalarPuncturedProfile {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞ (scalarPuncturedProfile h) D := by
  intro z hz
  have hn : ContDiff ℝ ∞ (fun y : ComplexModel 1 => ‖y 0‖ ^ 2) := by
    simpa only [projectiveModelEquiv_symm_apply, ← Complex.sq_norm]
      using contDiff_projectiveModel_normSq
  have hlog := hn.contDiffAt.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hz 0)))
  have heq : scalarPuncturedProfile h = (fun y => h (Real.log (‖y 0‖ ^ 2))) := by
    funext y
    rw [scalarPuncturedProfile, tropicalization_apply_eq_log_norm_sq]
  rw [heq]
  exact (hh.contDiffAt.comp z hlog).contDiffWithinAt

/-- Actual exterior-power and determinant identities reuse the full ddC coefficient. -/
theorem smoothDensity_scalarPuncturedProfile {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {z : ComplexModel 1} (hz : z ∈ D) :
    smoothDensity (scalarPuncturedProfile h) z =
      realHessian h (Real.log (Complex.normSq (z 0))) 1 1 /
        (Real.pi * Complex.normSq (z 0)) := by
  have hsmooth := (contDiffOn_scalarPuncturedProfile hh z hz).contDiffAt
    (scalarPuncturedDomain.isOpen.mem_nhds hz)
  have h2 := hsmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [← normalizedTopPowerDensity_smoothDDC h2,
    ← actualTopPowerDensity_eq_normalizedTopPowerDensity_one,
    actualTopPowerDensity_one]
  have hv : coordinateVector (0 : Fin 1) = projectiveModelEquiv 1 := by
    ext i
    have hi := Fin.eq_zero i
    subst i
    simp [coordinateVector, projectiveModelEquiv_apply_zero]
  have hw : Complex.I • coordinateVector (0 : Fin 1) =
      projectiveModelEquiv Complex.I := by
    rw [hv]
    exact (projectiveModelEquiv.map_smul Complex.I 1).symm.trans (by simp)
  rw [hw, hv]
  exact smoothDDC_scalarTropicalProfile_standard hh (hz 0)

/-- The actual existing smooth mixed measure; all its fields are internally produced. -/
def scalarPuncturedSmoothMeasure {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) : Measure (ComplexModel 1) :=
  smoothMixedMeasure D (fun _ : Fin 1 => scalarPuncturedProfile h)
    (isSmoothMixedPshOn_of_components (fun _ => isSmoothPshOn_of_psh
      (contDiffOn_scalarPuncturedProfile hh)
      (plurisubharmonicOn_scalarPuncturedProfile hc)))

theorem scalarPuncturedSmoothMeasure_eq_withDensity {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) :
    scalarPuncturedSmoothMeasure hc hh = volume.withDensity
      (fun z : ComplexModel 1 => ENNReal.ofReal
        (realHessian h (Real.log (Complex.normSq (z 0))) 1 1 /
          (Real.pi * Complex.normSq (z 0)))) := by
  unfold scalarPuncturedSmoothMeasure smoothMixedMeasure
  simp only [mixedDensity_diagonal]
  calc
    _ = (volume.restrict (D : Set (ComplexModel 1))).withDensity
        (fun z : ComplexModel 1 => ENNReal.ofReal
          (realHessian h (Real.log (Complex.normSq (z 0))) 1 1 /
            (Real.pi * Complex.normSq (z 0)))) := by
      apply withDensity_congr_ae
      apply ae_restrict_of_forall_mem scalarPuncturedDomain.isOpen.measurableSet
      intro z hz
      change ENNReal.ofReal (smoothDensity (scalarPuncturedProfile h) z) = _
      rw [smoothDensity_scalarPuncturedProfile hh hz]
    _ = _ := by
      have hD : ∀ᵐ z : ComplexModel 1 ∂volume, z ∈ D := by
        filter_upwards [volume.ae_ne (0 : ComplexModel 1)] with z hz
        intro i
        have hi := Fin.eq_zero i
        subst i
        intro hzero
        apply hz
        ext j
        have hj := Fin.eq_zero j
        subst j
        exact hzero
      rw [Measure.restrict_eq_self_of_ae_mem hD]

/-- Full original signed punctured compact tests, without a radial symmetry premise. -/
theorem integral_scalarPuncturedSmoothMeasure_eq_radial {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (hh : ContDiff ℝ ∞ h) {η : ℂ → ℝ}
    (hη : Continuous η) (hK : HasCompactSupport η) (hzero : (0 : ℂ) ∉ tsupport η) :
    (∫ z, η (projectiveModelEquiv.symm z) ∂scalarPuncturedSmoothMeasure hc hh) =
      ∫ z, η z ∂Measure.map logLogRadialPoint
        ((alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))).prod
          logLogAngularMeasure) := by
  let d : ComplexModel 1 → ℝ := fun z =>
    realHessian h (Real.log (Complex.normSq (z 0))) 1 1 /
      (Real.pi * Complex.normSq (z 0))
  have hnorm : Measurable (fun z : ComplexModel 1 => Complex.normSq (z 0)) := by
    simpa only [projectiveModelEquiv_symm_apply] using
      contDiff_projectiveModel_normSq.continuous.measurable
  have hd : Measurable d :=
    ((continuous_scalarHessian hh).measurable.comp (Real.measurable_log.comp hnorm)).div
      (measurable_const.mul hnorm)
  have hn (z : ComplexModel 1) : 0 ≤ d z :=
    div_nonneg (scalarHessian_nonneg_of_convex_smooth hc hh _)
      (mul_nonneg Real.pi_pos.le (Complex.normSq_nonneg _))
  rw [scalarPuncturedSmoothMeasure_eq_withDensity hc hh]
  change (∫ z, η (projectiveModelEquiv.symm z) ∂volume.withDensity
    (ENNReal.ofReal ∘ d)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (ENNReal.measurable_ofReal.comp hd)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (hn _), smul_eq_mul]
  have hm := measurePreserving_projectiveModelRealIsometry.integral_comp
    projectiveModelRealIsometry.toHomeomorph.measurableEmbedding
    (fun z => d z * η (projectiveModelEquiv.symm z))
  rw [← hm]
  have heq : (fun z : ℂ => d (projectiveModelRealIsometry z) *
      η (projectiveModelEquiv.symm (projectiveModelRealIsometry z))) =
      radialScalarTestDensity (fun x => realHessian h x 1 1) η := by
    funext z
    change realHessian h (Real.log (Complex.normSq (projectiveModelEquiv z 0))) 1 1 /
      (Real.pi * Complex.normSq (projectiveModelEquiv z 0)) *
      η (projectiveModelEquiv.symm (projectiveModelEquiv z)) = _
    rw [projectiveModelEquiv_apply_zero, projectiveModelEquiv.symm_apply_apply]
    unfold radialScalarTestDensity
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [heq]
  exact integral_smoothScalarDensity_eq_radialAlexandrov hc hh hη hK hzero

end SGPT.Toric
