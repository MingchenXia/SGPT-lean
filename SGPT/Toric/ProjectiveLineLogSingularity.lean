import SGPT.Toric.ProjectiveLineSection
import SGPT.PSH.GlobalQPSH
import SGPT.Toric.RelativeThetaCriterion
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff NNReal ENNReal Classical

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual preferred chart potentials suffice for the original universal
local-potential definition, through genuine smooth-potential independence. -/
theorem isThetaPSH_of_chart_corrected
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (ρ : (i : A.Index) → ComplexModel (A.dimension i) → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (A.chart i).target)
    (hform : ∀ i, EqOn (smoothDDC (ρ i)) (θ.coeff i) (A.chart i).target)
    (hpsh : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (fun z ↦ A.coordinate u i z + (ρ i z : EReal)) (A.chart i).target)
    (htop : ∀ x, u x ≠ ⊤)
    (hnd : LocallyNondegenerateOn u univ) : A.IsThetaPSH θ u := by
  exact isThetaPSH_global_from_relative ρ hρ hform hpsh htop hnd

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff NNReal ENNReal Classical

/-- The original actual X₀ logarithmic singular potential on the quotient line. -/
def projectiveLogSingularity (p : Projectivization ℂ (Fin 2 → ℂ)) : EReal :=
  projectiveCoordinateMetricLog p 0

/-- Each actual chart correction is the genuine log pole or the constant zero. -/
theorem projectiveLogSingularity_corrected_chart (b : Bool) (z : ComplexModel 1) :
    projectiveLogSingularity ((projectiveModelChart b).symm z) +
      (projectiveFSPotential z : EReal) =
        if b then 0 else logNormSq (z 0) := by
  cases b
  · exact projectiveCoordinateMetricLog_add_potential z
  · rw [projectiveLogSingularity, projectiveCoordinateMetricLog_zero_infinity,
      ← EReal.coe_add]
    simp

/-- The actual original pole function is never top in either genuine chart. -/
theorem projectiveLogSingularity_ne_top (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveLogSingularity p ≠ ⊤ := by
  obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
  have hp : (projectiveModelChart b).symm ((projectiveModelChart b) p) = p :=
    (projectiveModelChart b).left_inv hb
  rw [← hp, projectiveLogSingularity]
  cases b
  · rw [projectiveCoordinateMetricLog_zero_finite]
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_top (logNormSq_ne_top _) (EReal.coe_ne_top _)
  · rw [projectiveCoordinateMetricLog_zero_infinity]
    exact EReal.coe_ne_top _

/-- The actual dense nonzero coordinate points give genuine source
nondegeneracy on every original quotient neighborhood. -/
theorem projectiveLogSingularity_locallyNondegenerate :
    SGPT.PSH.LocallyNondegenerateOn projectiveLogSingularity univ := by
  intro p _ O hO hpO
  obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
  cases b
  · let z := projectiveModelChart false p
    let D := (projectiveModelChart false).target ∩
      (projectiveModelChart false).symm ⁻¹' O
    have hz : z ∈ D := ⟨(projectiveModelChart false).map_source hb,
      by change (projectiveModelChart false).symm ((projectiveModelChart false) p) ∈ O
         rwa [(projectiveModelChart false).left_inv hb]⟩
    have hD : IsOpen D := (projectiveModelChart false).isOpen_inter_preimage_symm hO
    obtain ⟨w, hw, hwD⟩ := (projectiveCoordinate_frequently_ne_zero z).and_eventually
      (hD.mem_nhds hz) |>.exists
    refine ⟨(projectiveModelChart false).symm w, ⟨mem_univ _, hwD.2⟩, ?_⟩
    rw [projectiveLogSingularity, projectiveCoordinateMetricLog_zero_finite,
      logNormSq_of_ne_zero (by simpa only [projectiveModelEquiv_symm_apply] using hw),
      ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  · refine ⟨p, ⟨mem_univ _, hpO⟩, ?_⟩
    rw [← (projectiveModelChart true).left_inv hb, projectiveLogSingularity,
      projectiveCoordinateMetricLog_zero_infinity]
    exact EReal.coe_ne_bot _

/-- The original logarithmic example satisfies every genuine local potential
PSH test for the actual global Fubini--Study form. -/
theorem isThetaPSH_projectiveLogSingularity :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm projectiveLogSingularity := by
  apply SGPT.PSH.VariableComplexAtlas.isThetaPSH_of_chart_corrected
    (fun _ ↦ projectiveFSPotential)
    (fun _ ↦ contDiff_projectiveFSPotential.contDiffOn)
    (fun _ _ _ ↦ rfl) ?_ projectiveLogSingularity_ne_top
    projectiveLogSingularity_locallyNondegenerate
  intro b z _
  cases b
  · have hpsh : PlurisubharmonicAt (fun w : ComplexModel 1 ↦ logNormSq (w 0)) z := by
      have h := (show PlurisubharmonicOn (logNormSq (E := ℂ)) univ from
        fun w _ ↦ plurisubharmonicAt_logNormSq w).comp_continuousLinearMap
          projectiveModelEquiv.symm.toContinuousLinearMap
      have hz := h z (mem_univ _)
      change PlurisubharmonicAt (fun y ↦ logNormSq (projectiveModelEquiv.symm y)) z at hz
      simpa only [projectiveModelEquiv_symm_apply] using hz
    apply hpsh.congr
    exact Eventually.of_forall fun w ↦ (projectiveLogSingularity_corrected_chart false w).symm
  · apply (plurisubharmonicAt_const (0 : EReal) (by simp) z).congr
    exact Eventually.of_forall fun w ↦ (projectiveLogSingularity_corrected_chart true w).symm


/-- The actual extended singular norm is the quotient of the two genuine
reference norms, so its zero fiber vector remains zero at the pole. -/
def projectiveLogMetricNorm (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : ℝ≥0∞ :=
  ENNReal.ofReal (projectiveFiberMetric p ell) /
    ENNReal.ofReal (projectiveFiberMetric p (projectiveCoordinateSection p 0))

/-- The original Hermitian metric is quadratic; its actual squared norm is
independently constructed before identifying the exponential twist. -/
def projectiveLogMetricSquared (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : ℝ≥0∞ := projectiveLogMetricNorm p ell ^ 2

/-- The actual fiber zero remains zero even at the singular point. -/
theorem projectiveLogMetricNorm_zero (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveLogMetricNorm p 0 = 0 := by
  simp [projectiveLogMetricNorm, projectiveFiberMetric]

/-- Squared extended division equals the quotient of actual Hermitian squares. -/
theorem projectiveLogMetricSquared_eq_ratio (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) :
    projectiveLogMetricSquared p ell =
      ENNReal.ofReal (projectiveFiberMetric p ell ^ 2) /
        ENNReal.ofReal (projectiveFiberMetric p (projectiveCoordinateSection p 0) ^ 2) := by
  rw [projectiveLogMetricSquared, projectiveLogMetricNorm, div_eq_mul_inv, mul_pow,
    ← ENNReal.inv_pow, ← div_eq_mul_inv,
    ← ENNReal.ofReal_pow (projectiveFiberMetric_nonneg p ell),
    ← ENNReal.ofReal_pow (projectiveFiberMetric_nonneg p (projectiveCoordinateSection p 0))]

/-- The actual constructed metric is the source exponential twist of
Hermitian squared norms, retaining both the pole and the zero vector. -/
theorem projectiveLogMetricSquared_eq_twist (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) :
    projectiveLogMetricSquared p ell =
      ENNReal.ofReal (projectiveFiberMetric p ell ^ 2) *
        EReal.exp (-projectiveLogSingularity p) := by
  rw [projectiveLogMetricSquared_eq_ratio, projectiveLogSingularity,
    projectiveCoordinateMetricLog, EReal.exp_neg, ENNReal.exp_log, div_eq_mul_inv]

/-- Every genuine nonzero homogeneous lift produces the literal singular
norm ratio away from its original zero coordinate. -/
theorem projectiveLogMetricNorm_eq_homogeneous (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) (v : p.submodule) (hv : v ≠ 0)
    (hv0 : v.val 0 ≠ 0) :
    projectiveLogMetricNorm p ell = ENNReal.ofReal (‖ell v‖ / ‖v.val 0‖) := by
  have hn : 0 < ‖(WithLp.toLp 2 v.val : ComplexModel 2)‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hv
    exact Subtype.ext (congrArg WithLp.ofLp h)
  have h0 : 0 < ‖v.val 0‖ := norm_pos_iff.mpr hv0
  rw [projectiveLogMetricNorm, projectiveFiberMetric_eq_ratio p ell v hv,
    projectiveFiberMetric_eq_ratio p (projectiveCoordinateSection p 0) v hv,
    projectiveCoordinateSection_apply, ← ENNReal.ofReal_div_of_pos (div_pos h0 hn)]
  congr 1
  field_simp

/-- The exact printed norm formula holds on the actual nonzero finite chart. -/
theorem projectiveLogMetricNorm_finite (z : ComplexModel 1) (hz : z 0 ≠ 0)
    (ell : projectiveDualFiber ((projectiveModelChart false).symm z)) :
    projectiveLogMetricNorm ((projectiveModelChart false).symm z) ell =
      ENNReal.ofReal (‖ell (projectiveAffineFiberLift false z)‖ / ‖z 0‖) := by
  simpa [projectiveAffineFiberLift, projectiveAffineLift, projectiveModelEquiv_symm_apply] using
    projectiveLogMetricNorm_eq_homogeneous _ ell (projectiveAffineFiberLift false z)
      (projectiveAffineFiberLift_ne_zero false z)
      (by simpa [projectiveAffineFiberLift, projectiveAffineLift,
        projectiveModelEquiv_symm_apply] using hz)

/-- The original infinity point is the zero of the genuine opposite chart. -/
def projectiveInfinity : Projectivization ℂ (Fin 2 → ℂ) :=
  (projectiveModelChart true).symm 0

/-- The original zero point is the zero of the genuine finite chart. -/
def projectiveOrigin : Projectivization ℂ (Fin 2 → ℂ) :=
  (projectiveModelChart false).symm 0

/-- The literal original potential value at infinity is zero. -/
theorem projectiveLogSingularity_infinity : projectiveLogSingularity projectiveInfinity = 0 := by
  rw [projectiveInfinity, projectiveLogSingularity, projectiveCoordinateMetricLog_zero_infinity,
    projectiveFSPotential_eq]
  simp

/-- The genuine original pole is retained at zero. -/
theorem projectiveLogSingularity_origin : projectiveLogSingularity projectiveOrigin = ⊥ := by
  rw [projectiveOrigin, projectiveLogSingularity, projectiveCoordinateMetricLog_zero_finite,
    projectiveFSPotential_eq]
  simp

/-- Every original nonzero dual-fiber vector has genuinely infinite norm at zero. -/
theorem projectiveLogMetricNorm_origin (ell : projectiveDualFiber projectiveOrigin)
    (hell : ell ≠ 0) : projectiveLogMetricNorm projectiveOrigin ell = ⊤ := by
  have hs : projectiveFiberMetric projectiveOrigin (projectiveCoordinateSection projectiveOrigin 0) = 0 := by
    have h := projectiveCoordinateSection_zero_finite_metric_sq (0 : ComplexModel 1)
    simpa only [projectiveOrigin, PiLp.zero_apply, Complex.normSq_zero, add_zero,
      zero_div, pow_eq_zero_iff (by decide : 2 ≠ 0)] using h
  rw [projectiveLogMetricNorm, hs, ENNReal.ofReal_zero]
  apply ENNReal.div_zero
  rw [ne_eq, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (lt_of_le_of_ne (projectiveFiberMetric_nonneg _ _) (by
    intro h
    exact hell ((projectiveFiberMetric_eq_zero_iff _ _).mp h.symm)))

/-- At infinity the actual twisted norm is exactly the actual reference norm. -/
theorem projectiveLogMetricNorm_infinity (ell : projectiveDualFiber projectiveInfinity) :
    projectiveLogMetricNorm projectiveInfinity ell =
      ENNReal.ofReal (projectiveFiberMetric projectiveInfinity ell) := by
  have hs : projectiveFiberMetric projectiveInfinity (projectiveCoordinateSection projectiveInfinity 0) = 1 := by
    have h := projectiveCoordinateSection_zero_infinity_metric_sq (0 : ComplexModel 1)
    have hsq : projectiveFiberMetric projectiveInfinity
        (projectiveCoordinateSection projectiveInfinity 0) ^ 2 = 1 := by
      simpa only [projectiveInfinity, PiLp.zero_apply, Complex.normSq_zero, add_zero, div_one] using h
    nlinarith [projectiveFiberMetric_nonneg projectiveInfinity (projectiveCoordinateSection projectiveInfinity 0)]
  simp [projectiveLogMetricNorm, hs]


/-- Actual linear evaluation rescaled by the genuine norm of X₀. It is
faithful exactly where this original section does not vanish. -/
def projectiveLogDualEvaluation (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveDualFiber p →ₗ[ℂ] ℂ where
  toFun := fun ell ↦ projectiveDualEvaluation p ell /
    (projectiveFiberMetric p (projectiveCoordinateSection p 0) : ℂ)
  map_add' := by intro ell eta; simp [add_div]
  map_smul' := by intro a ell; simp [mul_div_assoc]

/-- Original fiber positivity makes the rescaling genuinely nonzero. -/
theorem projectiveCoordinateMetric_pos {p : Projectivization ℂ (Fin 2 → ℂ)}
    (hsec : projectiveCoordinateSection p 0 ≠ 0) :
    0 < projectiveFiberMetric p (projectiveCoordinateSection p 0) := by
  exact lt_of_le_of_ne (projectiveFiberMetric_nonneg _ _) (by
    intro h
    exact hsec ((projectiveFiberMetric_eq_zero_iff _ _).mp h.symm))

/-- Genuine nonzero scalar division preserves faithful actual fiber evaluation. -/
theorem projectiveLogDualEvaluation_injective {p : Projectivization ℂ (Fin 2 → ℂ)}
    (hsec : projectiveCoordinateSection p 0 ≠ 0) :
    Function.Injective (projectiveLogDualEvaluation p) := by
  intro ell eta h
  apply projectiveDualEvaluation_injective p
  change projectiveDualEvaluation p ell / _ = projectiveDualEvaluation p eta / _ at h
  exact (div_left_inj' (Complex.ofReal_ne_zero.mpr
    (projectiveCoordinateMetric_pos hsec).ne')).mp h

/-- Away from its actual pole the metric is a genuine positive Hermitian
form, constructed by its actual faithful rescaled linear evaluation. -/
@[instance_reducible] def projectiveLogHermitianCore
    (p : Projectivization ℂ (Fin 2 → ℂ)) (hsec : projectiveCoordinateSection p 0 ≠ 0) :
    InnerProductSpace.Core ℂ (projectiveDualFiber p) where
  inner ell eta := inner ℂ (projectiveLogDualEvaluation p ell) (projectiveLogDualEvaluation p eta)
  conj_inner_symm := fun ell eta ↦ inner_conj_symm _ _
  re_inner_nonneg := fun ell ↦ by
    rw [← norm_sq_eq_re_inner]
    exact sq_nonneg _
  definite := fun ell h ↦ by
    apply projectiveLogDualEvaluation_injective hsec
    simpa only [map_zero] using (inner_self_eq_zero.mp h)
  add_left := by intro ell eta nu; rw [map_add, inner_add_left]
  smul_left := by intro ell eta a; rw [map_smul, inner_smul_left]

/-- The actual rescaled Hermitian evaluation has precisely the printed norm. -/
theorem norm_projectiveLogDualEvaluation (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) :
    ‖projectiveLogDualEvaluation p ell‖ = projectiveFiberMetric p ell /
      projectiveFiberMetric p (projectiveCoordinateSection p 0) := by
  simp only [projectiveLogDualEvaluation, LinearMap.coe_mk, AddHom.coe_mk, norm_div,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (projectiveFiberMetric_nonneg _ _), norm_projectiveDualEvaluation]

/-- The independently defined extended squared metric is the quadratic
form of this genuine Hermitian core at every nonsingular original fiber. -/
theorem projectiveLogMetricSquared_eq_core
    (p : Projectivization ℂ (Fin 2 → ℂ)) (hsec : projectiveCoordinateSection p 0 ≠ 0)
    (ell : projectiveDualFiber p) :
    projectiveLogMetricSquared p ell =
      ENNReal.ofReal (((projectiveLogHermitianCore p hsec).inner ell ell).re) := by
  rw [projectiveLogMetricSquared, projectiveLogMetricNorm,
    ← ENNReal.ofReal_div_of_pos (projectiveCoordinateMetric_pos hsec),
    ← ENNReal.ofReal_pow (div_nonneg (projectiveFiberMetric_nonneg _ _)
      (projectiveFiberMetric_nonneg _ _)), ← norm_projectiveLogDualEvaluation]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

/-- At every original zero of X₀ the actual fiber is the singular Hermitian
form: zero at the zero vector and infinity at every nonzero vector. -/
theorem projectiveLogMetricSquared_singular
    (p : Projectivization ℂ (Fin 2 → ℂ)) (hsec : projectiveCoordinateSection p 0 = 0)
    (ell : projectiveDualFiber p) :
    projectiveLogMetricSquared p ell = if ell = 0 then (0 : ℝ≥0∞) else ⊤ := by
  classical
  by_cases hell : ell = 0
  · simp [hell, projectiveLogMetricSquared, projectiveLogMetricNorm_zero]
  · have hs : projectiveFiberMetric p (projectiveCoordinateSection p 0) = 0 :=
      (projectiveFiberMetric_eq_zero_iff _ _).mpr hsec
    have he : ENNReal.ofReal (projectiveFiberMetric p ell) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero]
      exact not_le.mpr (lt_of_le_of_ne (projectiveFiberMetric_nonneg _ _) (by
        intro h
        exact hell ((projectiveFiberMetric_eq_zero_iff _ _).mp h.symm)))
    simp [projectiveLogMetricSquared, projectiveLogMetricNorm, hs,
      ENNReal.div_zero he, hell]

/-- The two pointwise fiber alternatives in the original singular-metric
definition are produced from the actual computed metric. -/
theorem projectiveLogMetricSquared_fiber_classification
    (p : Projectivization ℂ (Fin 2 → ℂ)) :
    (∃ C : InnerProductSpace.Core ℂ (projectiveDualFiber p),
      ∀ ell, projectiveLogMetricSquared p ell = ENNReal.ofReal ((C.inner ell ell).re)) ∨
    (∀ ell, projectiveLogMetricSquared p ell = if ell = 0 then (0 : ℝ≥0∞) else ⊤) := by
  classical
  by_cases hsec : projectiveCoordinateSection p 0 = 0
  · exact Or.inr (projectiveLogMetricSquared_singular p hsec)
  · exact Or.inl ⟨projectiveLogHermitianCore p hsec,
      projectiveLogMetricSquared_eq_core p hsec⟩

/-- The literal original PSH-metric criterion, specialized to the actual
smooth Fubini–Study reference on the independently constructed O(1) fibers. -/
def IsProjectiveFSPSHMetric
    (q : (p : Projectivization ℂ (Fin 2 → ℂ)) → projectiveDualFiber p → ℝ≥0∞) : Prop :=
  (∀ p, (∃ C : InnerProductSpace.Core ℂ (projectiveDualFiber p),
      ∀ ell, q p ell = ENNReal.ofReal ((C.inner ell ell).re)) ∨
    (∀ ell, q p ell = if ell = 0 then (0 : ℝ≥0∞) else ⊤)) ∧
  ∃ u : Projectivization ℂ (Fin 2 → ℂ) → EReal,
    projectiveLineAtlas.IsThetaPSH projectiveFSForm u ∧
    ∀ p ell, q p ell = if ell = 0 then 0 else
      ENNReal.ofReal (projectiveFiberMetric p ell ^ 2) * EReal.exp (-u p)

/-- The original logarithmic example is genuinely a plurisubharmonic metric,
with its exact pointwise fiber forms and original exponential twist. -/
theorem isProjectiveFSPSHMetric_projectiveLogMetric :
    IsProjectiveFSPSHMetric projectiveLogMetricSquared := by
  classical
  refine ⟨projectiveLogMetricSquared_fiber_classification,
    projectiveLogSingularity, isThetaPSH_projectiveLogSingularity, ?_⟩
  intro p ell
  by_cases hell : ell = 0
  · simp [hell, projectiveLogMetricSquared, projectiveLogMetricNorm_zero]
  · rw [if_neg hell]
    exact projectiveLogMetricSquared_eq_twist p ell


/-- The literal source equation uses the extended logarithm of the actual
positive ratio, with log zero equal to bottom. -/
theorem projectiveLogSingularity_finite (z : ComplexModel 1) :
    projectiveLogSingularity ((projectiveModelChart false).symm z) =
      ENNReal.log (ENNReal.ofReal (Complex.normSq (z 0) / (1 + Complex.normSq (z 0)))) := by
  rw [projectiveLogSingularity, projectiveCoordinateMetricLog,
    projectiveCoordinateSection_zero_finite_metric_sq]

/-- The actual original fiber at zero is precisely the singular Hermitian
quadratic form, including its zero vector. -/
theorem projectiveLogMetricSquared_origin (ell : projectiveDualFiber projectiveOrigin) :
    projectiveLogMetricSquared projectiveOrigin ell = if ell = 0 then (0 : ℝ≥0∞) else ⊤ := by
  by_cases hell : ell = 0
  · simp [hell, projectiveLogMetricSquared, projectiveLogMetricNorm_zero]
  · simp [projectiveLogMetricSquared, projectiveLogMetricNorm_origin ell hell, hell]

/-- The actual quadratic metric at infinity agrees with the genuine smooth
reference Hermitian metric, exactly as in the original example. -/
theorem projectiveLogMetricSquared_infinity (ell : projectiveDualFiber projectiveInfinity) :
    projectiveLogMetricSquared projectiveInfinity ell =
      ENNReal.ofReal (projectiveFiberMetric projectiveInfinity ell ^ 2) := by
  rw [projectiveLogMetricSquared, projectiveLogMetricNorm_infinity,
    ← ENNReal.ofReal_pow (projectiveFiberMetric_nonneg _ _)]

end SGPT.Toric
