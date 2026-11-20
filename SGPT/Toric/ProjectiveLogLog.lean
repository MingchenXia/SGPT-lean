import SGPT.Toric.LogLogProfile
import SGPT.Toric.ProjectiveToricBottomExample

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- The actual one-coordinate real function, rather than an assumed growth datum. -/
def logLogEuclideanProfile (x : EuclideanSpace ℝ (Fin 1)) : ℝ := logLogProfile (x 0)

theorem logLogEuclideanProfile_mem_realGrowthClass :
    logLogEuclideanProfile ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
  refine ⟨?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simpa only [logLogEuclideanProfile, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      using convexOn_logLogProfile.2 (mem_univ (x 0)) (mem_univ (y 0)) ha hb hab
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨2, fun x ↦ ?_⟩
    rw [support_projectiveMomentInterval, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (logLogProfile_le_support_add_two (x 0))

/-- The genuine source inverse extends the manufactured original convex growth function. -/
def projectiveLogLogPotential : Projectivization ℂ (Fin 2 → ℂ) → EReal :=
  projectiveToricExtension logLogEuclideanProfile logLogEuclideanProfile_mem_realGrowthClass

theorem isThetaPSH_projectiveLogLogPotential :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogLogPotential :=
  (projectiveToricExtension_spec _ logLogEuclideanProfile_mem_realGrowthClass).1

theorem projectiveLogLogPotential_offPotential :
    EqOn projectiveLogLogPotential (projectiveToricOffPotential logLogEuclideanProfile)
      projectiveToricBoundaryᶜ :=
  (projectiveToricExtension_spec _ logLogEuclideanProfile_mem_realGrowthClass).2

theorem projectiveLogLogPotential_circleInvariant :
    ProjectiveCircleInvariant projectiveLogLogPotential :=
  projectiveToricExtension_circleInvariant logLogEuclideanProfile_mem_realGrowthClass
    isThetaPSH_projectiveLogLogPotential projectiveLogLogPotential_offPotential

theorem projectiveLogLogPotential_correctedDescent :
    projectiveToricCorrectedDescent projectiveLogLogPotential =
      fun x ↦ (sourceLogLogProfile (x 0) : EReal) := by
  rw [projectiveToricCorrectedDescent_eq_of_extension projectiveLogLogPotential_offPotential]
  funext x
  exact congrArg (fun r : ℝ ↦ (r : EReal)) (logLogProfile_eq_source (x 0))

/-- Actual surjective coordinate reindexing identifies the literal Euclidean conjugate. -/
theorem conjugate_logLogEuclideanProfile (m : EuclideanSpace ℝ (Fin 1)) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin 1)))
      (fun x ↦ (logLogEuclideanProfile x : EReal)) m = logLogConjugate (m 0) := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) := by
    intro r
    exact ⟨WithLp.toLp 2 (fun _ : Fin 1 ↦ r), rfl⟩
  calc
    _ = ⨆ x : EuclideanSpace ℝ (Fin 1),
        ((m 0 * x 0 - logLogProfile (x 0) : ℝ) : EReal) := by
      unfold conjugate logLogEuclideanProfile
      congr 1
      funext x
      simp [innerₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    _ = logLogConjugate (m 0) := hsurj.iSup_comp
      (fun r : ℝ ↦ ((m 0 * r - logLogProfile r : ℝ) : EReal))

theorem projectiveLogLogPotential_legendre (m : EuclideanSpace ℝ (Fin 1)) :
    projectiveToricLegendre projectiveLogLogPotential m = sourceLogLogConjugate (m 0) := by
  unfold projectiveToricLegendre
  rw [projectiveToricCorrectedDescent_eq_of_extension projectiveLogLogPotential_offPotential,
    conjugate_logLogEuclideanProfile, logLogConjugate_eq_source]

end SGPT.Toric

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

theorem logLogProfile_ge_linear_add_two (x : ℝ) : x + 2 ≤ logLogProfile x := by
  rw [logLogProfile_eq_source]
  unfold sourceLogLogProfile
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

/-- The manufactured support bound supplies the original constant upper bound on the torus. -/
theorem projectiveLogLogPotential_le_two_off
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    projectiveLogLogPotential p ≤ (2 : EReal) := by
  let z := projectiveModelChart false p
  have hz : z ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
  have hpart := max_le_projectiveLineLogPartition (tropicalization z 0)
  rw [projectiveLineLogPartition_tropicalization (hz 0), ← projectiveFSPotential_eq] at hpart
  rw [projectiveLogLogPotential_offPotential hp]
  change ((logLogProfile (tropicalization z 0) - projectiveFSPotential z : ℝ) : EReal) ≤ 2
  have hreal : logLogProfile (tropicalization z 0) - projectiveFSPotential z ≤ (2 : ℝ) := by
    linarith [logLogProfile_le_support_add_two (tropicalization z 0)]
  exact EReal.coe_le_coe hreal

/-- Actual upper regularization preserves that produced bound at both original boundary points. -/
theorem projectiveLogLogPotential_le_two (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveLogLogPotential p ≤ (2 : EReal) := by
  calc
    _ = analyticExtension projectiveToricBoundary projectiveLogLogPotential p :=
      congrFun (projectiveThetaPSH_eq_analyticExtension isThetaPSH_projectiveLogLogPotential) p
    _ ≤ (2 : EReal) := by
      apply uscRegularization_le_of_eventually_le
        (g := fun _ ↦ (2 : EReal)) continuous_const.continuousAt.upperSemicontinuousAt
      exact Eventually.of_forall fun q ↦ by
        by_cases hq : q ∈ projectiveToricBoundary
        · simp [hq]
        · simpa only [if_neg hq] using projectiveLogLogPotential_le_two_off hq

/-- The true affine lower profile bound transfers through the source analytic filling comparison. -/
theorem projectiveLogSingularity_le_logLog_add_neg_two
    (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveLogSingularity p ≤ projectiveLogLogPotential p + (-2 : EReal) := by
  apply projectiveThetaPSH_le_add_of_le_off isThetaPSH_projectiveLogSingularity
    isThetaPSH_projectiveLogLogPotential (-2) ?_ p
  intro q hq
  rw [projectiveLogSingularity_offPotential hq, projectiveLogLogPotential_offPotential hq]
  change ((tropicalization (projectiveModelChart false q) 0 -
      projectiveFSPotential (projectiveModelChart false q) : ℝ) : EReal) ≤
    ((logLogProfile (tropicalization (projectiveModelChart false q) 0) -
      projectiveFSPotential (projectiveModelChart false q) : ℝ) : EReal) + ((-2 : ℝ) : EReal)
  rw [← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr (by
    linarith [logLogProfile_ge_linear_add_two (tropicalization (projectiveModelChart false q) 0)])

/-- The actual infinity value follows from two produced global bounds, without a boundary-value premise. -/
theorem projectiveLogLogPotential_infinity :
    projectiveLogLogPotential projectiveInfinity = (2 : EReal) := by
  apply le_antisymm (projectiveLogLogPotential_le_two _)
  have h := projectiveLogSingularity_le_logLog_add_neg_two projectiveInfinity
  rw [projectiveLogSingularity_infinity] at h
  have hs := add_le_add h (le_refl (2 : EReal))
  have hcancel : (-2 : EReal) + (2 : EReal) = 0 := by
    change (((-2 : ℝ) : EReal) + ((2 : ℝ) : EReal)) = 0
    rw [← EReal.coe_add]
    norm_num
  simpa only [zero_add, add_assoc, hcancel, add_zero] using hs

end SGPT.Toric

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- The actual raw boundary-filled coordinate function, independently of its regularization. -/
def projectiveLogLogRawCoordinate (b : Bool) (z : ComplexModel 1) : EReal :=
  if z 0 = 0 then ⊥ else projectiveLogLogPotential ((projectiveModelChart b).symm z)

/-- The true chart covariance of the original filling recovers the produced potential. -/
theorem uscRegularization_projectiveLogLogRawCoordinate (b : Bool) (z : ComplexModel 1) :
    uscRegularization (projectiveLogLogRawCoordinate b) z =
      projectiveLogLogPotential ((projectiveModelChart b).symm z) := by
  have hz : z ∈ (projectiveModelChart b).target := by
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  calc
    _ = uscRegularization
        ((fun p ↦ if p ∈ projectiveToricBoundary then (⊥ : EReal)
          else projectiveLogLogPotential p) ∘ (projectiveModelChart b).symm) z := by
      congr 1
      funext w
      simp only [projectiveLogLogRawCoordinate, Function.comp_def,
        projectiveToricBoundary_chart_iff]
    _ = analyticExtension projectiveToricBoundary projectiveLogLogPotential
        ((projectiveModelChart b).symm z) :=
      uscRegularization_comp_openPartialHomeomorph_apply _ (projectiveModelChart b).symm hz
    _ = projectiveLogLogPotential ((projectiveModelChart b).symm z) :=
      congrFun (projectiveThetaPSH_eq_analyticExtension isThetaPSH_projectiveLogLogPotential).symm _

/-- Literal finite-chart values on the original punctured coordinate domain. -/
theorem projectiveLogLogPotential_finite {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    projectiveLogLogPotential ((projectiveModelChart false).symm z) =
      ((logLogProfile (Real.log (‖z 0‖ ^ 2)) - Real.log (1 + ‖z 0‖ ^ 2) : ℝ) : EReal) := by
  have hzT : z ∈ complexTorus 1 := by
    simpa only [complexTorus, mem_ofPred_eq, Fin.forall_fin_one] using hz
  have hOff := (projectiveToricBoundary_chart_off_iff false z).mpr hzT
  have hzTarget : z ∈ (projectiveModelChart false).target := by
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  rw [projectiveLogLogPotential_offPotential hOff]
  simp only [projectiveToricOffPotential, (projectiveModelChart false).right_inv hzTarget,
    logLogEuclideanProfile, tropicalization_apply_eq_log_norm_sq,
    projectiveFSPotential_eq, ← Complex.sq_norm]

/-- Actual small coordinate neighborhoods bound the raw filled values by every original real constant. -/
theorem projectiveLogLogRawCoordinate_eventually_le (C : ℝ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel 1), projectiveLogLogRawCoordinate false z ≤ (C : EReal) := by
  let T : ℝ := max logLogLambda (Real.exp (-C)) + 1
  have hT : logLogLambda < T := by dsimp [T]; linarith [le_max_left logLogLambda (Real.exp (-C))]
  have hTexp : Real.exp (-C) < T := by dsimp [T]; linarith [le_max_right logLogLambda (Real.exp (-C))]
  have hO : IsOpen {z : ComplexModel 1 | ‖z 0‖ ^ 2 < Real.exp (-T)} :=
    isOpen_lt (by fun_prop) continuous_const
  have hzero : (0 : ComplexModel 1) ∈ {z : ComplexModel 1 | ‖z 0‖ ^ 2 < Real.exp (-T)} := by
    simpa only [mem_ofPred_eq, PiLp.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      using Real.exp_pos (-T)
  filter_upwards [hO.mem_nhds hzero] with z hzSmall
  by_cases hz : z 0 = 0
  · simp only [projectiveLogLogRawCoordinate, if_pos hz, bot_le]
  · have hq : 0 < ‖z 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
    have hx := Real.log_lt_log hq hzSmall
    rw [Real.log_exp] at hx
    have hcut : Real.log (‖z 0‖ ^ 2) ≤ -logLogLambda := by linarith
    have hexp : Real.exp (-C) < -Real.log (‖z 0‖ ^ 2) := by linarith
    have hlog := Real.log_lt_log (Real.exp_pos (-C)) hexp
    rw [Real.log_exp] at hlog
    have hfs : 0 ≤ Real.log (1 + ‖z 0‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖z 0‖])
    rw [projectiveLogLogRawCoordinate, if_neg hz, projectiveLogLogPotential_finite hz,
      logLogProfile, if_pos hcut]
    exact EReal.coe_le_coe (by linarith)

/-- Genuine analytic filling, rather than upper semicontinuity alone, gives the original origin pole. -/
theorem projectiveLogLogPotential_origin :
    projectiveLogLogPotential projectiveOrigin = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro C
  have hle : uscRegularization (projectiveLogLogRawCoordinate false) (0 : ComplexModel 1) ≤
      ((C - 1 : ℝ) : EReal) :=
    uscRegularization_le_of_eventually_le
      (g := fun _ ↦ ((C - 1 : ℝ) : EReal))
      continuous_const.continuousAt.upperSemicontinuousAt
      (projectiveLogLogRawCoordinate_eventually_le (C - 1))
  rw [uscRegularization_projectiveLogLogRawCoordinate] at hle
  change projectiveLogLogPotential projectiveOrigin ≤ ((C - 1 : ℝ) : EReal) at hle
  exact hle.trans_lt (EReal.coe_lt_coe (by linarith : C - 1 < C))

end SGPT.Toric

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- The printed source radius is exactly its genuine squared-log coordinate cutoff. -/
theorem log_norm_sq_lt_neg_log_two_iff {z : ℂ} (hz : z ≠ 0) :
    Real.log (‖z‖ ^ 2) < -Real.log 2 ↔ ‖z‖ < 1 / Real.sqrt 2 := by
  have hq : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
  have hs : (1 / Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num), one_div]
  rw [← Real.log_inv (2 : ℝ), Real.log_lt_log_iff hq (by positivity), ← hs]
  exact sq_lt_sq₀ (norm_nonneg z) (by positivity)

/-- The literal original finite-chart piecewise function, with the actual log-log pole retained. -/
def sourceProjectiveLogLogValue (z : ℂ) : EReal :=
  if z = 0 then ⊥ else
    if ‖z‖ < 1 / Real.sqrt 2 then
      ((-Real.log (‖z‖ ^ 2 + 1) +
        max (-Real.log (-Real.log (‖z‖ ^ 2))) (2 + Real.log (‖z‖ ^ 2)) : ℝ) : EReal)
    else ((2 + Real.log (‖z‖ ^ 2 / (‖z‖ ^ 2 + 1)) : ℝ) : EReal)

/-- Every finite original chart point, including zero and the true cutoff sphere, has the printed value. -/
theorem projectiveLogLogPotential_eq_source_finite (z : ComplexModel 1) :
    projectiveLogLogPotential ((projectiveModelChart false).symm z) =
      sourceProjectiveLogLogValue (z 0) := by
  by_cases hz : z 0 = 0
  · have hz0 : z = 0 := by
      ext i
      fin_cases i
      simpa using hz
    rw [hz0]
    change projectiveLogLogPotential projectiveOrigin = sourceProjectiveLogLogValue 0
    simpa [sourceProjectiveLogLogValue] using projectiveLogLogPotential_origin
  · rw [sourceProjectiveLogLogValue, if_neg hz, projectiveLogLogPotential_finite hz,
      logLogProfile_eq_source]
    unfold sourceLogLogProfile
    have hcut := log_norm_sq_lt_neg_log_two_iff hz
    by_cases hsmall : ‖z 0‖ < 1 / Real.sqrt 2
    · rw [if_pos hsmall, if_pos (hcut.mpr hsmall)]
      congr 1
      rw [add_comm (‖z 0‖ ^ 2) 1, add_comm (2 : ℝ) (Real.log (‖z 0‖ ^ 2))]
      ring
    · rw [if_neg hsmall, if_neg (fun h ↦ hsmall (hcut.mp h))]
      have hq : 0 < ‖z 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
      rw [Real.log_div hq.ne' (by positivity : ‖z 0‖ ^ 2 + 1 ≠ 0)]
      congr 1
      rw [add_comm (‖z 0‖ ^ 2) 1]
      ring

/-- Literal original exponential-coordinate function in ex:FGsimplevarphi. -/
def sourceLogLogTorusValue (n : ℝ) : ℝ :=
  if n < -Real.log 2 then
    -Real.log (Real.exp n + 1) + max (-Real.log (-n)) (n + 2)
  else 2 + Real.log (Real.exp n / (1 + Real.exp n))

theorem logLogProfile_sub_partition_eq_source_torus (n : ℝ) :
    logLogProfile n - projectiveLineLogPartition n = sourceLogLogTorusValue n := by
  rw [logLogProfile_eq_source]
  unfold sourceLogLogProfile sourceLogLogTorusValue projectiveLineLogPartition
  by_cases hn : n < -Real.log 2
  · rw [if_pos hn, if_pos hn, add_comm (Real.exp n) 1]
    ring
  · rw [if_neg hn, if_neg hn,
      Real.log_div (Real.exp_pos n).ne' (by positivity : 1 + Real.exp n ≠ 0), Real.log_exp]
    ring

/-- The actual potential evaluated at true positive exponential coordinates gives the printed f(n). -/
theorem projectiveLogLogPotential_expCoordinates (x : EuclideanSpace ℝ (Fin 1)) :
    projectiveLogLogPotential
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)) =
      (sourceLogLogTorusValue (x 0) : EReal) := by
  have h := congrFun
    (projectiveToricCorrectedDescent_eq_of_extension projectiveLogLogPotential_offPotential) x
  change projectiveLogLogPotential
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)) +
    (projectiveLineLogPartition (x 0) : EReal) = (logLogProfile (x 0) : EReal) at h
  have hs := congrArg (fun r : EReal ↦ r + ((-projectiveLineLogPartition (x 0) : ℝ) : EReal)) h
  have hcancel := corrected_add_sub
    (projectiveLogLogPotential
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)))
    (projectiveLineLogPartition (x 0)) 0
  simp only [zero_sub, EReal.coe_zero, add_zero] at hcancel
  rw [hcancel, ← EReal.coe_add] at hs
  simpa only [← sub_eq_add_neg, logLogProfile_sub_partition_eq_source_torus] using hs

/-- The actual one-dimensional Legendre pairing has precisely the original scalar coordinate formula. -/
theorem projectiveLogLogPotential_legendre_scalar (m : ℝ) :
    projectiveToricLegendre projectiveLogLogPotential
      (WithLp.toLp 2 (fun _ : Fin 1 ↦ m)) = sourceLogLogConjugate m :=
  projectiveLogLogPotential_legendre _

end SGPT.Toric

namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- The first original printed f(n), from the true coordinate section at actual exponential points. -/
theorem projectiveLogSingularity_expCoordinates (x : EuclideanSpace ℝ (Fin 1)) :
    projectiveLogSingularity
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)) =
      ((Real.log (Real.exp (x 0) / (1 + Real.exp (x 0))) : ℝ) : EReal) := by
  have h := congrFun projectiveToricCorrectedDescent_logSingularity x
  change projectiveLogSingularity
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)) +
    (projectiveLineLogPartition (x 0) : EReal) = (x 0 : EReal) at h
  have hs := congrArg (fun r : EReal ↦ r + ((-projectiveLineLogPartition (x 0) : ℝ) : EReal)) h
  have hcancel := corrected_add_sub
    (projectiveLogSingularity
      (OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)))
    (projectiveLineLogPartition (x 0)) 0
  simp only [zero_sub, EReal.coe_zero, add_zero] at hcancel
  rw [hcancel, ← EReal.coe_add] at hs
  rw [Real.log_div (Real.exp_pos (x 0)).ne'
    (by positivity : 1 + Real.exp (x 0) ≠ 0), Real.log_exp]
  simpa only [← sub_eq_add_neg, projectiveLineLogPartition] using hs

end SGPT.Toric
