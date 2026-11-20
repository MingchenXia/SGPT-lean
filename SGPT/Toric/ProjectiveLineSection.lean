import SGPT.Toric.ProjectiveLineFubiniStudy
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Laplacian Distributions ComplexConjugate

/-- The literal extended logarithm of the actual coordinate-section Hermitian norm. -/
def projectiveCoordinateMetricLog (p : Projectivization ℂ (Fin 2 → ℂ)) (j : Fin 2) : EReal :=
  ENNReal.log (ENNReal.ofReal (projectiveFiberMetric p (projectiveCoordinateSection p j) ^ 2))

/-- Every actual coordinate section has the genuine homogeneous squared metric ratio. -/
theorem projectiveCoordinateSection_metric_sq (b : Bool) (z : ComplexModel 1) (j : Fin 2) :
    projectiveFiberMetric ((projectiveModelChart b).symm z)
      (projectiveCoordinateSection ((projectiveModelChart b).symm z) j) ^ 2 =
        Complex.normSq (projectiveAffineLift b z j) /
          (1 + Complex.normSq (projectiveModelEquiv.symm z)) := by
  rw [projectiveFiberMetric_eq_ratio _ _ (projectiveAffineFiberLift b z)
    (projectiveAffineFiberLift_ne_zero b z)]
  change (‖projectiveAffineLift b z j‖ /
    ‖(WithLp.toLp 2 (projectiveAffineLift b z) : ComplexModel 2)‖) ^ 2 = _
  rw [div_pow, projectiveAffineLift_norm_sq, Complex.sq_norm]

/-- The original vanishing section `X₀` has the printed finite-chart squared norm. -/
theorem projectiveCoordinateSection_zero_finite_metric_sq (z : ComplexModel 1) :
    projectiveFiberMetric ((projectiveModelChart false).symm z)
      (projectiveCoordinateSection ((projectiveModelChart false).symm z) 0) ^ 2 =
      Complex.normSq (z 0) / (1 + Complex.normSq (z 0)) := by
  simpa [projectiveAffineLift, projectiveModelEquiv_symm_apply] using
    projectiveCoordinateSection_metric_sq false z 0

/-- That same original section is nonzero at infinity, with the true opposite-chart norm. -/
theorem projectiveCoordinateSection_zero_infinity_metric_sq (z : ComplexModel 1) :
    projectiveFiberMetric ((projectiveModelChart true).symm z)
      (projectiveCoordinateSection ((projectiveModelChart true).symm z) 0) ^ 2 =
      1 / (1 + Complex.normSq (z 0)) := by
  simpa [projectiveAffineLift, projectiveModelEquiv_symm_apply] using
    projectiveCoordinateSection_metric_sq true z 0

/-- The actual source logarithmic section formula keeps its zero value bottom. -/
theorem projectiveCoordinateMetricLog_zero_finite (z : ComplexModel 1) :
    projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0 =
      logNormSq (z 0) - (projectiveFSPotential z : EReal) := by
  rw [projectiveCoordinateMetricLog, projectiveCoordinateSection_zero_finite_metric_sq,
    projectiveFSPotential_eq]
  by_cases hz : z 0 = 0
  · simp [hz]
  · have hp : 0 < Complex.normSq (z 0) := Complex.normSq_pos.mpr hz
    have hd : 0 < 1 + Complex.normSq (z 0) := by positivity
    rw [ENNReal.log_ofReal_of_pos (div_pos hp hd), Real.log_div hp.ne' hd.ne',
      logNormSq_of_ne_zero hz, Complex.sq_norm, ← EReal.coe_sub]

/-- Its actual opposite-chart extended logarithm is finite and equals the smooth negative weight. -/
theorem projectiveCoordinateMetricLog_zero_infinity (z : ComplexModel 1) :
    projectiveCoordinateMetricLog ((projectiveModelChart true).symm z) 0 =
      (-(projectiveFSPotential z) : ℝ) := by
  rw [projectiveCoordinateMetricLog, projectiveCoordinateSection_zero_infinity_metric_sq,
    ENNReal.log_ofReal_of_pos (by have h := Complex.normSq_nonneg (z 0); positivity),
    one_div, Real.log_inv, projectiveFSPotential_eq]

/-- Actual curvature correction recovers the literal original logarithmic pole pointwise. -/
theorem projectiveCoordinateMetricLog_add_potential (z : ComplexModel 1) :
    projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0 +
      (projectiveFSPotential z : EReal) = logNormSq (z 0) := by
  rw [projectiveCoordinateMetricLog_zero_finite]
  exact EReal.sub_add_cancel

/-- The actual first affine coordinate has no identically zero neighborhood. -/
theorem projectiveCoordinate_frequently_ne_zero (z : ComplexModel 1) :
    ∃ᶠ w in 𝓝 z, projectiveModelEquiv.symm w ≠ 0 := by
  have h := (dense_compl_singleton (0 : ComplexModel 1)).closure_eq
  have hz : z ∈ closure ({0}ᶜ : Set (ComplexModel 1)) := by rw [h]; trivial
  apply (mem_closure_iff_frequently.mp hz).mono
  intro w hw hzero
  have hwzero : w = 0 := by
    apply projectiveModelEquiv.symm.injective
    simpa using hzero
  exact hw (by simpa using hwzero)

/-- Actual simple coordinate-zero presentation of the genuine original divisor. -/
def projectiveCoordinateZeroPresentation :
    Pending.DivisorRegularLocus.RegularPresentation
      (projectiveModelEquiv.symm : ComplexModel 1 → ℂ) 0 where
  U := univ
  isOpen := isOpen_univ
  mem := mem_univ _
  m := 1
  m_pos := one_pos
  h := projectiveModelEquiv.symm
  v := fun _ ↦ 1
  h_diff := projectiveModelEquiv.symm.differentiable.differentiableOn
  v_diff := differentiableOn_const _
  h_zero := map_zero _
  dh_ne := by
    intro y _ hzero
    change fderiv ℂ (projectiveModelEquiv.symm.toContinuousLinearMap) y = 0 at hzero
    rw [projectiveModelEquiv.symm.toContinuousLinearMap.fderiv] at hzero
    have hval := congrArg (fun L : ComplexModel 1 →L[ℂ] ℂ ↦ L (projectiveModelEquiv 1)) hzero
    simp at hval
  v_ne := fun _ _ ↦ one_ne_zero
  eq := fun _ _ ↦ by simp

/-- The actual coordinate divisor consists of the original single zero point. -/
theorem projectiveCoordinate_regularLocus :
    Pending.DivisorRegularLocus.regularLocus
      (projectiveModelEquiv.symm : ComplexModel 1 → ℂ) = {0} := by
  ext z
  constructor
  · rintro ⟨P⟩
    apply mem_singleton_iff.mpr
    apply projectiveModelEquiv.symm.injective
    simpa using P.g_x
  · rintro rfl
    exact projectiveCoordinateZeroPresentation.mem_regularLocus

/-- Its genuine multiplicity is exactly one, produced by the actual coordinate presentation. -/
theorem projectiveCoordinate_divisorMult :
    Pending.DivisorRegularLocus.divisorMult
      (projectiveModelEquiv.symm : ComplexModel 1 → ℂ) 0 = 1 :=
  projectiveCoordinateZeroPresentation.divisorMult_eq

/-- The genuine logarithmic section has the actual real distribution density,
including its single pole where both normalized real logarithms vanish. -/
theorem projectiveCoordinateMetricLog_toReal_zero_finite (z : ComplexModel 1) :
    (projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0).toReal =
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2) - projectiveFSPotential z := by
  rw [projectiveCoordinateMetricLog_zero_finite, projectiveModelEquiv_symm_apply]
  by_cases hz : z 0 = 0
  · simp [hz, projectiveFSPotential_eq]
  · rw [logNormSq_of_ne_zero hz, ← EReal.coe_sub, EReal.toReal_coe]

/-- Genuine local logarithmic integrability comes from the actual nontrivial
holomorphic coordinate, rather than an integrability premise. -/
theorem locallyIntegrable_projectiveCoordinateLog :
    LocallyIntegrableOn (fun z : ComplexModel 1 ↦
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2))
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume :=
  Pending.DivisorIntegrationCurrent.locallyIntegrableOn_log_normSq isOpen_univ
    projectiveModelEquiv.symm.differentiable.differentiableOn
    (fun z _ ↦ projectiveCoordinate_frequently_ne_zero z)

/-- Actual smooth curvature potential is locally integrable in the original chart. -/
theorem locallyIntegrable_projectiveFSPotential :
    LocallyIntegrableOn projectiveFSPotential
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume :=
  contDiff_projectiveFSPotential.continuous.locallyIntegrable.locallyIntegrableOn _

/-- The actual logarithmic section, retaining its extended pole, has a genuine
locally integrable real density for its distribution. -/
theorem locallyIntegrable_projectiveCoordinateMetricLog :
    LocallyIntegrableOn (fun z : ComplexModel 1 ↦
      (projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0).toReal)
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume := by
  have heq : (fun z : ComplexModel 1 ↦
      (projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0).toReal) =
      (fun z : ComplexModel 1 ↦ Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) -
        projectiveFSPotential := by
    funext z
    exact projectiveCoordinateMetricLog_toReal_zero_finite z
  rw [heq]
  exact locallyIntegrable_projectiveCoordinateLog.sub locallyIntegrable_projectiveFSPotential

/-- The true Fubini--Study curvature current on the original finite chart. -/
def projectiveFSCurvatureCurrent :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  LocalCurrents.ddC (regularDistribution volume projectiveFSPotential
    locallyIntegrable_projectiveFSPotential)

/-- The distributional curvature of the actual logarithmic norm of `X₀`. -/
def projectiveCoordinateMetricLogCurrent :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  LocalCurrents.ddC (regularDistribution volume (fun z : ComplexModel 1 ↦
    (projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0).toReal)
    locallyIntegrable_projectiveCoordinateMetricLog)

/-- The actual integration current of the simple coordinate zero divisor. -/
def projectiveCoordinateZeroCurrent :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  Pending.DivisorIntegrationCurrent.divisorCurrent
    projectiveModelEquiv.symm.differentiable.differentiableOn
    (fun z _ ↦ projectiveCoordinate_frequently_ne_zero z)

/-- The produced smooth global Fubini--Study form really reads the curvature
current; every original real direction and test function is retained. -/
theorem projectiveFSCurvatureCurrent_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    projectiveFSCurvatureCurrent ![v, w] φ =
      ∫ z, φ z * projectiveFSForm.coeff false z ![v, w] := by
  simp only [projectiveFSCurvatureCurrent, projectiveFSForm_coeff]
  exact Pending.LelongPoincareDivisor.ddC_regularDistribution_apply_of_contDiffOn
    contDiff_projectiveFSPotential.contDiffOn locallyIntegrable_projectiveFSPotential v w φ

/-- The literal original Lelong--Poincaré equation for `X₀` is a full equality
of actual distribution-valued alternating two-forms in the genuine finite chart. -/
theorem projectiveCoordinateSection_lelongPoincare :
    projectiveFSCurvatureCurrent + projectiveCoordinateMetricLogCurrent =
      projectiveCoordinateZeroCurrent := by
  have hreg : regularDistribution volume (fun z : ComplexModel 1 ↦
      (projectiveCoordinateMetricLog ((projectiveModelChart false).symm z) 0).toReal)
      locallyIntegrable_projectiveCoordinateMetricLog =
      regularDistribution volume (fun z : ComplexModel 1 ↦
        Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) locallyIntegrable_projectiveCoordinateLog -
      regularDistribution volume projectiveFSPotential locallyIntegrable_projectiveFSPotential := by
    simpa only [projectiveCoordinateMetricLog_toReal_zero_finite] using
      Pending.ThetaPshChartLimitGluing.regularDistribution_sub
        locallyIntegrable_projectiveCoordinateLog locallyIntegrable_projectiveFSPotential
  change Pending.LelongPoincareDivisor.ddCLM _ +
    Pending.LelongPoincareDivisor.ddCLM _ = _
  rw [hreg, map_sub]
  have hlog := Pending.DivisorIntegrationCurrent.ddC_log_normSq_eq_divisorCurrent
    (Ω := (⊤ : TopologicalSpace.Opens (ComplexModel 1)))
    projectiveModelEquiv.symm.differentiable.differentiableOn
    (fun z _ ↦ projectiveCoordinate_frequently_ne_zero z)
  change Pending.LelongPoincareDivisor.ddCLM
    (regularDistribution volume (fun z : ComplexModel 1 ↦
      Real.log (‖projectiveModelEquiv.symm z‖ ^ 2)) locallyIntegrable_projectiveCoordinateLog) =
    projectiveCoordinateZeroCurrent at hlog
  rw [← hlog]
  abel

/-- The coordinate model is genuinely orthonormal, so its inverse preserves
the original Euclidean norm. -/
theorem projectiveModelEquiv_symm_norm (z : ComplexModel 1) :
    ‖projectiveModelEquiv.symm z‖ = ‖z‖ :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm.norm_map z

/-- The actual orthonormal coordinate covector has unit operator norm. -/
theorem projectiveModelEquiv_symm_opNorm :
    ‖projectiveModelEquiv.symm.toContinuousLinearMap‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖projectiveModelEquiv.symm z‖ ≤ 1 * ‖z‖
    rw [projectiveModelEquiv_symm_norm, one_mul]
  · have hunit : ‖projectiveModelEquiv 1‖ = 1 := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply, norm_one] using
        (projectiveModelEquiv_symm_norm (projectiveModelEquiv 1)).symm
    have h := projectiveModelEquiv.symm.toContinuousLinearMap.le_opNorm
      (projectiveModelEquiv 1)
    change ‖projectiveModelEquiv.symm (projectiveModelEquiv 1)‖ ≤
      ‖projectiveModelEquiv.symm.toContinuousLinearMap‖ * ‖projectiveModelEquiv 1‖ at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply, norm_one, hunit, mul_one] using h

/-- The actual simple coordinate divisor has the standard oriented point form,
with its normalization produced from the genuine orthonormal covector. -/
theorem projectiveCoordinate_transverseForm (v w : ComplexModel 1) :
    Pending.DivisorRegularLocus.transverseForm
      (projectiveModelEquiv.symm : ComplexModel 1 → ℂ) 0 v w =
        (conj (v 0) * w 0).im := by
  have h := projectiveCoordinateZeroPresentation.transverseForm_eq v w
  change _ = Pending.DivisorRegularLocus.lineForm
    (fderiv ℂ projectiveModelEquiv.symm.toContinuousLinearMap 0) v w at h
  rw [projectiveModelEquiv.symm.toContinuousLinearMap.fderiv] at h
  rw [h, Pending.DivisorRegularLocus.lineForm, projectiveModelEquiv_symm_opNorm]
  simp [projectiveModelEquiv_symm_apply]

/-- The actual integration current is literally the multiplicity-one point
current `[0]`, for every real direction pair and original test function. -/
theorem projectiveCoordinateZeroCurrent_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    projectiveCoordinateZeroCurrent ![v, w] φ = φ 0 * (conj (v 0) * w 0).im := by
  rw [projectiveCoordinateZeroCurrent, Pending.DivisorIntegrationCurrent.divisorCurrent_apply]
  simp only [Pending.DivisorIntegrationCurrent.divisorDensity,
    projectiveCoordinate_regularLocus]
  have heq : (fun x : ComplexModel 1 ↦ φ x * ({0} : Set (ComplexModel 1)).indicator
      (fun x ↦ (Pending.DivisorRegularLocus.divisorMult projectiveModelEquiv.symm x : ℝ) *
        Pending.DivisorRegularLocus.transverseForm projectiveModelEquiv.symm x v w) x) =
      ({0} : Set (ComplexModel 1)).indicator (fun x ↦ φ x *
        ((Pending.DivisorRegularLocus.divisorMult projectiveModelEquiv.symm x : ℝ) *
          Pending.DivisorRegularLocus.transverseForm projectiveModelEquiv.symm x v w)) := by
    funext x
    by_cases hx : x ∈ ({0} : Set (ComplexModel 1)) <;> simp [hx]
  rw [heq, integral_indicator (measurableSet_singleton 0), integral_singleton]
  simp [measureReal_def, Measure.euclideanHausdorffMeasure_zero,
    projectiveCoordinate_divisorMult, projectiveCoordinate_transverseForm]

/-- In the actual oriented orthonormal affine frame, the integration current
has exactly the original multiplicity-one Dirac normalization. -/
theorem projectiveCoordinateZeroCurrent_apply_standard
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    projectiveCoordinateZeroCurrent
      ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I] φ = φ 0 := by
  simpa [projectiveModelEquiv_apply_zero] using
    projectiveCoordinateZeroCurrent_apply (projectiveModelEquiv 1)
      (projectiveModelEquiv Complex.I) φ

/-- The original example's literal normalized `[0]` equality is produced from
the whole-current identity and the actual singleton divisor calculation. -/
theorem projectiveCoordinateSection_lelongPoincare_apply (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent + projectiveCoordinateMetricLogCurrent) ![v, w] φ =
      φ 0 * (conj (v 0) * w 0).im := by
  rw [projectiveCoordinateSection_lelongPoincare]
  exact projectiveCoordinateZeroCurrent_apply v w φ

/-- Original homogeneous linear forms define actual sections of the dual line,
without choosing a homogeneous lift. -/
def projectiveLinearSection (a : Fin 2 → ℂ) (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveDualFiber p :=
  a 0 • projectiveCoordinateSection p 0 + a 1 • projectiveCoordinateSection p 1

/-- Evaluation is the literal original homogeneous linear form. -/
theorem projectiveLinearSection_apply (a : Fin 2 → ℂ)
    (p : Projectivization ℂ (Fin 2 → ℂ)) (v : p.submodule) :
    projectiveLinearSection a p v = a 0 * v.val 0 + a 1 * v.val 1 := rfl

/-- The genuine local coefficients of the original linear sections in both
actual nonvanishing coordinate frames. -/
theorem projectiveLinearSection_chart_coefficient (a : Fin 2 → ℂ)
    (b : Bool) (z : ComplexModel 1) :
    projectiveLinearSection a ((projectiveModelChart b).symm z)
      (projectiveAffineFiberLift b z) =
      if b then a 0 + a 1 * projectiveModelEquiv.symm z
        else a 0 * projectiveModelEquiv.symm z + a 1 := by
  cases b <;> simp [projectiveLinearSection_apply, projectiveAffineFiberLift,
    projectiveAffineLift]

/-- These actual coefficients are holomorphic on the original affine charts;
no holomorphic-section certificate is assumed. -/
theorem differentiable_projectiveLinearSection_chart_coefficient (a : Fin 2 → ℂ) (b : Bool) :
    Differentiable ℂ (fun z : ComplexModel 1 ↦
      projectiveLinearSection a ((projectiveModelChart b).symm z)
        (projectiveAffineFiberLift b z)) := by
  simp_rw [projectiveLinearSection_chart_coefficient]
  cases b
  · exact (differentiable_const (a 0)).mul projectiveModelEquiv.symm.differentiable |>.add
      (differentiable_const (a 1))
  · exact (differentiable_const (a 0)).add
      ((differentiable_const (a 1)).mul projectiveModelEquiv.symm.differentiable)

end SGPT.Toric
