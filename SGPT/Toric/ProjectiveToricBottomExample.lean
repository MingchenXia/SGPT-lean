import SGPT.Toric.ProjectiveToricRooftop

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- Actual homogeneous coordinate swap on the original quotient line. -/
def projectiveCoordinateSwap :
    Projectivization ℂ (Fin 2 → ℂ) ≃ₜ Projectivization ℂ (Fin 2 → ℂ) :=
  (projectiveLineHomeomorph.symm.trans projectiveReciprocalHomeomorph).trans
    projectiveLineHomeomorph

/-- The genuine reciprocal point formulas interchange the two original charts. -/
theorem projectiveCoordinateSwap_chart (b : Bool) (z : ComplexModel 1) :
    projectiveCoordinateSwap ((projectiveModelChart b).symm z) =
      (projectiveModelChart (!b)).symm z := by
  rw [projectiveModelChart_symm_onePoint, projectiveModelChart_symm_onePoint]
  change projectiveLineHomeomorph (projectiveReciprocal
    (projectiveLineHomeomorph.symm (projectiveLineHomeomorph
      (if b then projectiveReciprocal ((z 0 : ℂ) : OnePoint ℂ)
        else ((z 0 : ℂ) : OnePoint ℂ))))) = _
  rw [projectiveLineHomeomorph.symm_apply_apply]
  cases b
  · rfl
  · exact congrArg projectiveLineHomeomorph
      (projectiveReciprocal_involutive ((z 0 : ℂ) : OnePoint ℂ))

/-- The actual opposite sections have equal Hermitian squares in swapped charts. -/
theorem projectiveCoordinateMetricLog_opposite_chart (b : Bool) (z : ComplexModel 1) :
    projectiveCoordinateMetricLog ((projectiveModelChart b).symm z) 1 =
      projectiveCoordinateMetricLog ((projectiveModelChart (!b)).symm z) 0 := by
  simp only [projectiveCoordinateMetricLog, projectiveCoordinateSection_metric_sq]
  cases b <;> rfl

/-- Literal original X₁ coordinate-section metric logarithm. -/
def projectiveOppositeLogSingularity (p : Projectivization ℂ (Fin 2 → ℂ)) : EReal :=
  projectiveCoordinateMetricLog p 1

/-- Actual chart cover identifies the opposite potential with the genuine swap pullback. -/
theorem projectiveOppositeLogSingularity_eq_swap
    (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveOppositeLogSingularity p = projectiveLogSingularity (projectiveCoordinateSwap p) := by
  obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
  change Bool at b
  rw [← (projectiveModelChart b).left_inv hb, projectiveCoordinateSwap_chart]
  exact projectiveCoordinateMetricLog_opposite_chart b ((projectiveModelChart b) p)

/-- Original finite and infinity chart corrections, retaining the true infinity pole. -/
theorem projectiveOppositeLogSingularity_corrected_chart (b : Bool) (z : ComplexModel 1) :
    projectiveOppositeLogSingularity ((projectiveModelChart b).symm z) +
      (projectiveFSPotential z : EReal) = if b then logNormSq (z 0) else 0 := by
  rw [projectiveOppositeLogSingularity_eq_swap, projectiveCoordinateSwap_chart,
    projectiveLogSingularity_corrected_chart]
  cases b <;> rfl

/-- Never-top is transported through the genuine coordinate swap. -/
theorem projectiveOppositeLogSingularity_ne_top (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveOppositeLogSingularity p ≠ ⊤ := by
  rw [projectiveOppositeLogSingularity_eq_swap]
  exact projectiveLogSingularity_ne_top _

/-- Open-image transport of true nonbottom witnesses proves source local nondegeneracy. -/
theorem projectiveOppositeLogSingularity_locallyNondegenerate :
    LocallyNondegenerateOn projectiveOppositeLogSingularity univ := by
  intro p _ O hO hpO
  obtain ⟨y, hy, hn⟩ := projectiveLogSingularity_locallyNondegenerate
    (projectiveCoordinateSwap p) (mem_univ _) (projectiveCoordinateSwap '' O)
    (projectiveCoordinateSwap.isOpenMap O hO) ⟨p, hpO, rfl⟩
  obtain ⟨q, hq, rfl⟩ := hy.2
  refine ⟨q, ⟨mem_univ _, hq⟩, ?_⟩
  rwa [projectiveOppositeLogSingularity_eq_swap]

/-- Opposite preferred chart PSH and genuine potential independence supply every source test. -/
theorem isThetaPSH_projectiveOppositeLogSingularity :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveOppositeLogSingularity := by
  apply isThetaPSH_of_chart_corrected (fun _ ↦ projectiveFSPotential)
    (fun _ ↦ contDiff_projectiveFSPotential.contDiffOn)
    (fun _ _ _ ↦ rfl) ?_ projectiveOppositeLogSingularity_ne_top
    projectiveOppositeLogSingularity_locallyNondegenerate
  intro b z _
  change Bool at b
  change ComplexModel 1 at z
  have hz : z ∈ (projectiveModelChart (!b)).target := by
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  have h := isThetaPSH_projectiveLogSingularity.preferred_chart_corrected (!b)
    (ρ := projectiveFSPotential) contDiff_projectiveFSPotential.contDiffOn
    (fun _ _ ↦ rfl) z hz
  have hpsh : PlurisubharmonicAt
      (fun w : ComplexModel 1 ↦ projectiveLogSingularity ((projectiveModelChart (!b)).symm w) +
        (projectiveFSPotential w : EReal)) z := h
  apply hpsh.congr
  exact Eventually.of_forall fun w ↦ by
    change projectiveLogSingularity ((projectiveModelChart (!b)).symm w) +
      (projectiveFSPotential w : EReal) =
        projectiveOppositeLogSingularity ((projectiveModelChart b).symm w) +
          (projectiveFSPotential w : EReal)
    rw [projectiveOppositeLogSingularity_eq_swap, projectiveCoordinateSwap_chart]

/-- The original X₁ finite-chart function is the smooth negative FS weight. -/
theorem projectiveOppositeLogSingularity_finite (z : ComplexModel 1) :
    projectiveOppositeLogSingularity ((projectiveModelChart false).symm z) =
      (-(projectiveFSPotential z) : ℝ) := by
  rw [projectiveOppositeLogSingularity, projectiveCoordinateMetricLog_opposite_chart]
  exact projectiveCoordinateMetricLog_zero_infinity z

/-- The genuine opposite coordinate section vanishes at the original infinity point. -/
theorem projectiveOppositeLogSingularity_infinity :
    projectiveOppositeLogSingularity projectiveInfinity = ⊥ := by
  rw [projectiveInfinity, projectiveOppositeLogSingularity,
    projectiveCoordinateMetricLog_opposite_chart]
  simpa [projectiveLogSingularity, projectiveOrigin] using projectiveLogSingularity_origin

/-- The literal original opposite potential is zero at the finite origin. -/
theorem projectiveOppositeLogSingularity_origin :
    projectiveOppositeLogSingularity projectiveOrigin = 0 := by
  rw [projectiveOrigin, projectiveOppositeLogSingularity_finite, projectiveFSPotential_eq]
  simp

/-- The linear endpoint cost is genuinely in the original real support-growth class. -/
theorem projectiveLinearEndpoint_mem_realGrowthClass :
    (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
  refine ⟨(EuclideanSpace.projₗ (0 : Fin 1)).convexOn convex_univ, ?_⟩
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨0, fun x ↦ ?_⟩
  rw [support_projectiveMomentInterval, EReal.coe_zero, add_zero]
  exact EReal.coe_le_coe_iff.mpr (le_max_right 0 (x 0))

/-- The zero endpoint cost has genuine original growth constant zero. -/
theorem projectiveZeroEndpoint_mem_realGrowthClass :
    (fun _ : EuclideanSpace ℝ (Fin 1) ↦ (0 : ℝ)) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin 1))) projectiveMomentInterval := by
  refine ⟨convexOn_const 0 convex_univ, ?_⟩
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨0, fun x ↦ ?_⟩
  rw [support_projectiveMomentInterval, EReal.coe_zero, add_zero]
  exact EReal.coe_le_coe_iff.mpr (le_max_left 0 (x 0))

/-- The actual X₀ section formula agrees with the original linear reverse potential on the torus. -/
theorem projectiveLogSingularity_offPotential :
    EqOn projectiveLogSingularity
      (projectiveToricOffPotential (fun x ↦ x 0)) projectiveToricBoundaryᶜ := by
  intro p hp
  let e := projectiveModelChart false
  have hs := projectiveToricBoundary_compl_subset_finite_source hp
  have hz : (e p) 0 ≠ 0 := (projectiveFiniteCoordinate_mem_torus_of_off_boundary hp) 0
  have h : projectiveLogSingularity p =
      logNormSq ((e p) 0) - (projectiveFSPotential (e p) : EReal) := by
    conv_lhs => rw [← e.left_inv hs]
    exact projectiveCoordinateMetricLog_zero_finite (e p)
  rw [h, logNormSq_of_ne_zero hz, ← EReal.coe_sub]
  change ((Real.log (‖(e p) 0‖ ^ 2) - projectiveFSPotential (e p) : ℝ) : EReal) =
    ((tropicalization (e p) 0 - projectiveFSPotential (e p) : ℝ) : EReal)
  rw [tropicalization_apply_eq_log_norm_sq]

/-- The actual X₁ section formula agrees with the original zero reverse potential on the torus. -/
theorem projectiveOppositeLogSingularity_offPotential :
    EqOn projectiveOppositeLogSingularity
      (projectiveToricOffPotential (fun _ ↦ 0)) projectiveToricBoundaryᶜ := by
  intro p hp
  let e := projectiveModelChart false
  have hs := projectiveToricBoundary_compl_subset_finite_source hp
  have h : projectiveOppositeLogSingularity p = (-(projectiveFSPotential (e p)) : ℝ) := by
    conv_lhs => rw [← e.left_inv hs]
    exact projectiveOppositeLogSingularity_finite (e p)
  simpa [projectiveToricOffPotential, e] using h

/-- Original circle invariance follows from genuine extension uniqueness, including the pole. -/
theorem projectiveLogSingularity_circleInvariant :
    ProjectiveCircleInvariant projectiveLogSingularity :=
  projectiveToricExtension_circleInvariant projectiveLinearEndpoint_mem_realGrowthClass
    isThetaPSH_projectiveLogSingularity projectiveLogSingularity_offPotential

/-- Original circle invariance of the opposite pole is likewise produced, not assumed. -/
theorem projectiveOppositeLogSingularity_circleInvariant :
    ProjectiveCircleInvariant projectiveOppositeLogSingularity :=
  projectiveToricExtension_circleInvariant projectiveZeroEndpoint_mem_realGrowthClass
    isThetaPSH_projectiveOppositeLogSingularity projectiveOppositeLogSingularity_offPotential

/-- The literal source X₀ corrected descent is the original real linear coordinate. -/
theorem projectiveToricCorrectedDescent_logSingularity :
    projectiveToricCorrectedDescent projectiveLogSingularity =
      fun x ↦ (x 0 : EReal) :=
  projectiveToricCorrectedDescent_eq_of_extension projectiveLogSingularity_offPotential

/-- The literal source X₁ corrected descent is the original zero function. -/
theorem projectiveToricCorrectedDescent_oppositeLogSingularity :
    projectiveToricCorrectedDescent projectiveOppositeLogSingularity =
      fun _ ↦ (0 : EReal) :=
  projectiveToricCorrectedDescent_eq_of_extension projectiveOppositeLogSingularity_offPotential

/-- The printed finite-chart formula determines the original opposite theta-PSH function uniquely. -/
theorem projectiveOppositeLogSingularity_unique
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hfinite : ∀ z : ComplexModel 1,
      u ((projectiveModelChart false).symm z) = (-(projectiveFSPotential z) : ℝ)) :
    u = projectiveOppositeLogSingularity := by
  have hoff : EqOn u (projectiveToricOffPotential (fun _ ↦ 0)) projectiveToricBoundaryᶜ := by
    intro p hp
    rw [← projectiveOppositeLogSingularity_offPotential hp]
    rw [← (projectiveModelChart false).left_inv
      (projectiveToricBoundary_compl_subset_finite_source hp)]
    rw [hfinite, projectiveOppositeLogSingularity_finite]
  obtain ⟨w, _hw, huniq⟩ := existsUnique_projectiveToricExtension projectiveZeroEndpoint_mem_realGrowthClass
  exact (huniq u ⟨hu, hoff⟩).trans
    (huniq projectiveOppositeLogSingularity
      ⟨isThetaPSH_projectiveOppositeLogSingularity,
        projectiveOppositeLogSingularity_offPotential⟩).symm

/-- The actual one endpoint in the original Euclidean moment coordinate. -/
def projectiveMomentOne : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))

/-- Direct evaluation of the genuine singleton gives the literal linear endpoint cost. -/
theorem support_projectiveMomentOne :
    support (innerₗ (EuclideanSpace ℝ (Fin 1))).flip {projectiveMomentOne} =
      fun x ↦ (x 0 : EReal) := by
  funext x
  simp [support, innerₗ_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, projectiveMomentOne]

/-- The genuine zero singleton has exactly zero support, without a separation assumption. -/
theorem support_projectiveMomentZero :
    support (innerₗ (EuclideanSpace ℝ (Fin 1))).flip {0} =
      fun _ ↦ (0 : EReal) := by
  funext x
  simp [support]

/-- The original X₀ Legendre function is the actual singleton-one indicator. -/
theorem projectiveToricLegendre_logSingularity :
    projectiveToricLegendre projectiveLogSingularity = indicator {projectiveMomentOne} := by
  unfold projectiveToricLegendre
  rw [projectiveToricCorrectedDescent_logSingularity, ← support_projectiveMomentOne]
  exact conjugate_support_of_isContPerfPair _ (convex_singleton _) isClosed_singleton

/-- The original X₁ Legendre function is the actual singleton-zero indicator. -/
theorem projectiveToricLegendre_oppositeLogSingularity :
    projectiveToricLegendre projectiveOppositeLogSingularity =
      indicator ({0} : Set (EuclideanSpace ℝ (Fin 1))) := by
  unfold projectiveToricLegendre
  rw [projectiveToricCorrectedDescent_oppositeLogSingularity, ← support_projectiveMomentZero]
  exact conjugate_support_of_isContPerfPair _ (convex_singleton _) isClosed_singleton

/-- Actual distinct endpoint singletons have everywhere-top pointwise maximum. -/
theorem max_projectiveEndpointIndicators (m : EuclideanSpace ℝ (Fin 1)) :
    max (indicator {projectiveMomentOne} m)
      (indicator ({0} : Set (EuclideanSpace ℝ (Fin 1))) m) = ⊤ := by
  have h10 : projectiveMomentOne ≠ 0 := by
    intro h
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) h
    norm_num [projectiveMomentOne] at he
  by_cases hm : m = projectiveMomentOne
  · subst m
    simp [SGPT.Convex.indicator, h10]
  · simp [SGPT.Convex.indicator, hm]

/-- The complete original example: the actual two logarithmic coordinate
potentials have identically bottom raw theta rooftop. -/
theorem projectiveLogSingularity_thetaRooftop_eq_bot :
    thetaRooftop projectiveFSForm projectiveLogSingularity
      projectiveOppositeLogSingularity = ⊥ := by
  by_contra hne
  let R := thetaRooftop projectiveFSForm projectiveLogSingularity projectiveOppositeLogSingularity
  have hR : projectiveLineAtlas.IsThetaPSH projectiveFSForm R :=
    isThetaPSH_projective_thetaRooftop isThetaPSH_projectiveLogSingularity
      isThetaPSH_projectiveOppositeLogSingularity hne
  have hiR : ProjectiveCircleInvariant R := projectiveCircleInvariant_thetaRooftop
    projectiveLogSingularity_circleInvariant projectiveOppositeLogSingularity_circleInvariant
  have hF := projectiveToricCorrectedDescent_mem_growthClass hR hiR
  obtain ⟨m, hm⟩ := (isProper_conjugate_of_isContPerfPair
    (innerₗ (EuclideanSpace ℝ (Fin 1))) hF.1).2.1
  have hG := congrFun (projectiveToricLegendre_thetaRooftop
    isThetaPSH_projectiveLogSingularity isThetaPSH_projectiveOppositeLogSingularity
    projectiveLogSingularity_circleInvariant projectiveOppositeLogSingularity_circleInvariant hne) m
  rw [projectiveToricLegendre_logSingularity,
    projectiveToricLegendre_oppositeLogSingularity, max_projectiveEndpointIndicators] at hG
  change projectiveToricLegendre R m < ⊤ at hm
  rw [hG] at hm
  exact lt_irrefl _ hm

end SGPT.Toric
