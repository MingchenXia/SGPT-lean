import SGPT.Toric.ProjectiveLineCharts
import SGPT.Toric.ProjectiveLineEntropy
import SGPT.PSH.GlobalQPSH
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.Pending.FubiniStudyLineLevi
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

/-- The actual orthonormal model equivalence has the original scalar coordinate. -/
theorem projectiveModelEquiv_apply_zero (z : ℂ) : projectiveModelEquiv z 0 = z := by
  simp [projectiveModelEquiv]

theorem projectiveModelEquiv_symm_apply (z : ComplexModel 1) :
    projectiveModelEquiv.symm z = z 0 := by
  have h := projectiveModelEquiv_apply_zero (projectiveModelEquiv.symm z)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

/-- The literal original affine Fubini--Study potential in the genuine model coordinate. -/
def projectiveFSPotential (z : ComplexModel 1) : ℝ :=
  Real.log (1 + Complex.normSq (projectiveModelEquiv.symm z))

theorem projectiveFSPotential_eq (z : ComplexModel 1) :
    projectiveFSPotential z = Real.log (1 + Complex.normSq (z 0)) := by
  rw [projectiveFSPotential, projectiveModelEquiv_symm_apply]

/-- The original linear coordinate has genuinely smooth squared norm. -/
theorem contDiff_projectiveModel_normSq : ContDiff ℝ ∞
    (fun z : ComplexModel 1 ↦ Complex.normSq (projectiveModelEquiv.symm z)) := by
  simp only [← Complex.sq_norm]
  exact (contDiff_norm_sq ℝ).comp
    (projectiveModelEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff

/-- Actual squared-norm smoothness and the positive logarithm argument produce full smoothness. -/
theorem contDiff_projectiveFSPotential : ContDiff ℝ ∞ projectiveFSPotential := by
  exact (contDiff_const.add contDiff_projectiveModel_normSq).log (fun z ↦ by
    have h := Complex.normSq_nonneg (projectiveModelEquiv.symm z)
    positivity)

/-- Actual nonzero field reciprocals yield precisely the original logarithmic transition identity. -/
theorem projectiveFS_scalar_inverse {z : ℂ} (hz : z ≠ 0) :
    Real.log (1 + Complex.normSq z⁻¹) =
      Real.log (1 + Complex.normSq z) - Real.log (Complex.normSq z) := by
  have hp : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hinv : Complex.normSq z⁻¹ = (Complex.normSq z)⁻¹ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, norm_inv, inv_pow]
  have harg : 1 + Complex.normSq z⁻¹ = (1 + Complex.normSq z) / Complex.normSq z := by
    rw [hinv]
    field_simp
    ring
  rw [harg, Real.log_div (by positivity) hp.ne']

/-- Actual reciprocal in the original linear model, used only on genuine overlap loci. -/
def projectiveModelInverse (z : ComplexModel 1) : ComplexModel 1 :=
  projectiveModelEquiv ((projectiveModelEquiv.symm z)⁻¹)

theorem projectiveFSPotential_modelInverse {z : ComplexModel 1}
    (hz : projectiveModelEquiv.symm z ≠ 0) :
    projectiveFSPotential (projectiveModelInverse z) = projectiveFSPotential z -
      Real.log (Complex.normSq (projectiveModelEquiv.symm z)) := by
  simp only [projectiveFSPotential, projectiveModelInverse,
    ContinuousLinearEquiv.symm_apply_apply]
  exact projectiveFS_scalar_inverse hz

/-- The genuine nonzero model-coordinate overlap. -/
def projectiveModelPunctured : Set (ComplexModel 1) :=
  {z | projectiveModelEquiv.symm z ≠ 0}

theorem isOpen_projectiveModelPunctured : IsOpen projectiveModelPunctured :=
  isOpen_ne.preimage projectiveModelEquiv.symm.continuous

theorem contDiffOn_projectiveModel_logNormSq : ContDiffOn ℝ ∞
    (fun z : ComplexModel 1 ↦ Real.log (Complex.normSq (projectiveModelEquiv.symm z)))
    projectiveModelPunctured :=
  contDiff_projectiveModel_normSq.contDiffOn.log
    (fun _ hz ↦ (Complex.normSq_pos.mpr hz).ne')

/-- The complete actual normalized form is unchanged by the original reciprocal transition. -/
theorem smoothDDC_projectiveFSPotential_modelInverse {z : ComplexModel 1}
    (hz : z ∈ projectiveModelPunctured) :
    smoothDDC (fun w ↦ projectiveFSPotential (projectiveModelInverse w)) z =
      smoothDDC projectiveFSPotential z := by
  have heq : (fun w ↦ projectiveFSPotential (projectiveModelInverse w)) =ᶠ[𝓝 z]
      (fun w ↦ projectiveFSPotential w -
        Real.log (Complex.normSq (projectiveModelEquiv.symm w))) := by
    filter_upwards [isOpen_projectiveModelPunctured.mem_nhds hz] with w hw
    exact projectiveFSPotential_modelInverse hw
  have hzero : smoothDDC (fun w ↦ Real.log (Complex.normSq (projectiveModelEquiv.symm w))) z = 0 :=
    Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
      (Eventually.of_forall fun _ ↦ projectiveModelEquiv.symm.toContinuousLinearMap.differentiableAt)
      hz
  rw [smoothDDC_congr heq, PositiveClasses.smoothDDC_sub isOpen_projectiveModelPunctured
    contDiff_projectiveFSPotential.contDiffOn contDiffOn_projectiveModel_logNormSq hz,
    hzero, sub_zero]

/-- Genuine homeomorphism cancellation exposes the actual scalar transition in model coordinates. -/
theorem projectiveModelChart_transition_apply (i j : Bool) (z : ComplexModel 1) :
    ((projectiveModelChart i).symm.trans (projectiveModelChart j)) z =
      projectiveModelEquiv ((projectiveScalarChart j)
        ((projectiveScalarChart i).symm (projectiveModelEquiv.symm z))) := by
  change projectiveModelEquiv ((projectiveScalarChart j) (projectiveLineHomeomorph.symm
    (projectiveLineHomeomorph ((projectiveScalarChart i).symm
      (projectiveModelEquiv.symm z))))) = _
  rw [Homeomorph.symm_apply_apply]

/-- Original source membership produces the true identity/reciprocal coordinate descriptions. -/
theorem projectiveModelChart_transition_description (i j : Bool) {z : ComplexModel 1}
    (hz : z ∈ ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source) :
    ((projectiveModelChart i).symm.trans (projectiveModelChart j)) z =
      (if i = j then z else projectiveModelInverse z) ∧
      (i ≠ j → z ∈ projectiveModelPunctured) := by
  have hzq := projectiveModelChart_transition_source i j hz
  have hzscalar : projectiveModelEquiv.symm z ∈
      ((projectiveScalarChart i).symm.trans (projectiveScalarChart j)).source := by
    refine ⟨hzq.1, ?_⟩
    have h : projectiveLineHomeomorph.symm (projectiveLineHomeomorph
        ((projectiveScalarChart i).symm (projectiveModelEquiv.symm z))) ∈
          (projectiveScalarChart j).source := hzq.2
    change (projectiveScalarChart i).symm (projectiveModelEquiv.symm z) ∈
      (projectiveScalarChart j).source
    simpa only [Homeomorph.symm_apply_apply] using h
  cases i <;> cases j
  · constructor
    · rw [projectiveModelChart_transition_apply]
      change projectiveModelEquiv (projectiveFiniteChart
        (projectiveFiniteChart.symm (projectiveModelEquiv.symm z))) = z
      rw [projectiveFiniteChart_symm, projectiveFiniteChart_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    · simp
  · have hne : projectiveModelEquiv.symm z ≠ 0 := by
      have h : projectiveFiniteChart.symm (projectiveModelEquiv.symm z) ∈
          projectiveInfinityChart.source := hzscalar.2
      rw [projectiveFiniteChart_symm, projectiveInfinityChart_source] at h
      intro hzero
      exact h (congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) hzero)
    constructor
    · rw [projectiveModelChart_transition_apply]
      change projectiveModelEquiv (projectiveInfinityChart
        (projectiveFiniteChart.symm (projectiveModelEquiv.symm z))) = projectiveModelInverse z
      rw [projectiveFiniteChart_symm, projectiveInfinityChart_coe hne]
      rfl
    · exact fun _ ↦ hne
  · have hne : projectiveModelEquiv.symm z ≠ 0 := by
      intro hzero
      have h : projectiveInfinityChart.symm (projectiveModelEquiv.symm z) ∈
          projectiveFiniteChart.source := hzscalar.2
      rw [hzero, projectiveInfinityChart_symm, projectiveReciprocal_zero,
        projectiveFiniteChart_source] at h
      simp at h
    constructor
    · rw [projectiveModelChart_transition_apply]
      change projectiveModelEquiv (projectiveFiniteChart
        (projectiveInfinityChart.symm (projectiveModelEquiv.symm z))) = projectiveModelInverse z
      rw [projectiveInfinityChart_symm, projectiveReciprocal_coe hne,
        projectiveFiniteChart_coe]
      rfl
    · exact fun _ ↦ hne
  · constructor
    · rw [projectiveModelChart_transition_apply]
      change projectiveModelEquiv (projectiveInfinityChart
        (projectiveInfinityChart.symm (projectiveModelEquiv.symm z))) = z
      rw [projectiveInfinityChart.right_inv hzscalar.1,
        ContinuousLinearEquiv.apply_symm_apply]
    · simp

/-- The original coordinate potentials have the same complete normalized derivative after every actual transition. -/
theorem smoothDDC_projectiveFSPotential_transition (i j : Bool) {z : ComplexModel 1}
    (hz : z ∈ ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source) :
    smoothDDC (fun w ↦ projectiveFSPotential
      (((projectiveModelChart i).symm.trans (projectiveModelChart j)) w)) z =
        smoothDDC projectiveFSPotential z := by
  by_cases hij : i = j
  · have heq : (fun w ↦ projectiveFSPotential
        (((projectiveModelChart i).symm.trans (projectiveModelChart j)) w)) =ᶠ[𝓝 z]
        projectiveFSPotential := by
      filter_upwards [((projectiveModelChart i).symm.trans (projectiveModelChart j)).open_source.mem_nhds hz]
        with w hw
      rw [(projectiveModelChart_transition_description i j hw).1, if_pos hij]
    exact smoothDDC_congr heq
  · have heq : (fun w ↦ projectiveFSPotential
        (((projectiveModelChart i).symm.trans (projectiveModelChart j)) w)) =ᶠ[𝓝 z]
        (fun w ↦ projectiveFSPotential (projectiveModelInverse w)) := by
      filter_upwards [((projectiveModelChart i).symm.trans (projectiveModelChart j)).open_source.mem_nhds hz]
        with w hw
      rw [(projectiveModelChart_transition_description i j hw).1, if_neg hij]
    rw [smoothDDC_congr heq]
    exact smoothDDC_projectiveFSPotential_modelInverse
      ((projectiveModelChart_transition_description i j hz).2 hij)

/-- The actual original projective-line curvature: its smooth, closed and type-(1,1)
coefficient family satisfies the genuine derivative tensor gluing law. -/
def projectiveFSForm :
    SGPT.PSH.VariableComplexAtlas.AtlasClosedRealOneOneForm projectiveLineAtlas where
  coeff := fun _ ↦ smoothDDC projectiveFSPotential
  smooth := fun _ ↦ (Pending.LogWeightFactorization.smoothDDC_contDiffOn
    isOpen_univ contDiff_projectiveFSPotential.contDiffOn).mono (subset_univ _)
  compatible := by
    intro i j z hz w
    let T := (projectiveModelChart i).symm.trans (projectiveModelChart j)
    have hT : ContDiffOn ℂ ∞ T T.source :=
      contDiffOn_of_differentiableOn_complex
        (differentiableOn_projectiveModelChart_transition i j) T.open_source
    have h := HolomorphicDDC.smoothDDC_comp T.open_source isOpen_univ hT
      contDiff_projectiveFSPotential.contDiffOn (mapsTo_univ _ _) hz
    rw [smoothDDC_projectiveFSPotential_transition i j hz] at h
    exact congrArg (fun A ↦ A w) h
  closed := by
    intro i z _
    change extDeriv (extDeriv (smoothDc projectiveFSPotential)) z = 0
    exact extDeriv_extDeriv_apply
      ((smoothDc_contDiffOn isOpen_univ contDiff_projectiveFSPotential.contDiffOn).contDiffAt
        (isOpen_univ.mem_nhds (mem_univ z)))
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  typeOneOne := by
    intro i z _ v w
    exact MongeAmpere.smoothDDC_isOneOne
      (contDiff_projectiveFSPotential.contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w

/-- Literal original chart curvature coefficients, with the full source normalization. -/
theorem projectiveFSForm_coeff (i : Bool) (z : ComplexModel 1) :
    projectiveFSForm.coeff i z = smoothDDC (fun w ↦ Real.log (1 + Complex.normSq (w 0))) z := by
  change smoothDDC projectiveFSPotential z = _
  exact congrArg (fun f : ComplexModel 1 → ℝ ↦ smoothDDC f z)
    (funext projectiveFSPotential_eq)

/-- The actual standard homogeneous lift, in the genuine Euclidean two-coordinate space. -/
def projectiveHomogeneousLift (z : ComplexModel 1) : ComplexModel 2 :=
  WithLp.toLp 2 ![projectiveModelEquiv.symm z, 1]

/-- The actual homogeneous tangent lift, whose second coordinate is zero. -/
def projectiveHomogeneousTangent (v : ComplexModel 1) : ComplexModel 2 :=
  WithLp.toLp 2 ![projectiveModelEquiv.symm v, 0]

theorem projectiveHomogeneousLift_norm_sq (z : ComplexModel 1) :
    ‖projectiveHomogeneousLift z‖ ^ 2 =
      1 + Complex.normSq (projectiveModelEquiv.symm z) := by
  simp [EuclideanSpace.norm_sq_eq, projectiveHomogeneousLift, Fin.sum_univ_two,
    ← Complex.sq_norm, add_comm]

theorem projectiveHomogeneousLift_line (z v : ComplexModel 1) (t : ℂ) :
    projectiveHomogeneousLift (z + t • v) =
      projectiveHomogeneousLift z + t • projectiveHomogeneousTangent v := by
  ext i
  fin_cases i <;> simp [projectiveHomogeneousLift, projectiveHomogeneousTangent,
    map_add, map_smul]

theorem projectiveHomogeneousLift_ne_zero (z : ComplexModel 1) :
    projectiveHomogeneousLift z ≠ 0 := by
  intro h
  have h1 := congrArg (fun w : ComplexModel 2 ↦ w 1) h
  simp [projectiveHomogeneousLift] at h1

/-- Genuine second-coordinate independence excludes every scalar multiple for a nonzero tangent. -/
theorem projectiveHomogeneousTangent_not_span (z : ComplexModel 1)
    {v : ComplexModel 1} (hv : v ≠ 0) :
    ∀ r : ℂ, projectiveHomogeneousTangent v ≠ r • projectiveHomogeneousLift z := by
  intro r h
  have h1 := congrArg (fun w : ComplexModel 2 ↦ w 1) h
  have hr : r = 0 := by
    simpa [projectiveHomogeneousLift, projectiveHomogeneousTangent] using h1.symm
  have h0 := congrArg (fun w : ComplexModel 2 ↦ w 0) h
  have hc : projectiveModelEquiv.symm v = 0 := by
    simpa [projectiveHomogeneousLift, projectiveHomogeneousTangent, hr] using h0
  apply hv
  apply projectiveModelEquiv.symm.injective
  simpa using hc

/-- The original affine potential along its true line is the standard homogeneous squared-norm potential. -/
theorem projectiveFSPotential_line (z v : ComplexModel 1) (t : ℂ) :
    projectiveFSPotential (z + t • v) =
      Real.log (‖projectiveHomogeneousLift z + t • projectiveHomogeneousTangent v‖ ^ 2) := by
  unfold projectiveFSPotential
  rw [← projectiveHomogeneousLift_norm_sq, projectiveHomogeneousLift_line]

/-- Every genuine nonzero original chart tangent has strictly positive source-normalized curvature. -/
theorem projectiveFSForm_strictlyPositive (i : Bool) (z : ComplexModel 1)
    {v : ComplexModel 1} (hv : v ≠ 0) :
    0 < projectiveFSForm.coeff i z ![v, Complex.I • v] := by
  have hρ : ContDiffAt ℝ 2 projectiveFSPotential z :=
    contDiff_projectiveFSPotential.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change 0 < smoothDDC projectiveFSPotential z ![v, Complex.I • v]
  rw [Pending.FubiniStudyLineLevi.quad_smoothDDC_eq_leviForm hρ v,
    Pending.FubiniStudyLineLevi.leviForm_eq_line hρ v]
  have heq : (fun t : ℂ ↦ projectiveFSPotential (z + t • v)) =
      (fun t : ℂ ↦ Real.log
        (‖projectiveHomogeneousLift z + t • projectiveHomogeneousTangent v‖ ^ 2)) :=
    funext (projectiveFSPotential_line z v)
  rw [heq]
  exact div_pos
    (Pending.FubiniStudyLineLevi.leviForm_log_normSq_line_pos
      (projectiveHomogeneousTangent_not_span z hv) (projectiveHomogeneousLift_ne_zero z))
    Real.pi_pos

/-- The literal original fiber of `O(1)`, dual to the actual homogeneous line. -/
abbrev projectiveDualFiber (p : Projectivization ℂ (Fin 2 → ℂ)) :=
  Module.Dual ℂ p.submodule

/-- The actual chosen nonzero homogeneous representative inside its original line. -/
def projectiveLineRep (p : Projectivization ℂ (Fin 2 → ℂ)) : p.submodule :=
  ⟨p.rep, by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _⟩

theorem projectiveLineRep_ne_zero (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveLineRep p ≠ 0 := by
  intro h
  exact p.rep_nonzero (congrArg Subtype.val h)

theorem projectiveEuclideanRep_ne_zero (p : Projectivization ℂ (Fin 2 → ℂ)) :
    (WithLp.toLp 2 p.rep : ComplexModel 2) ≠ 0 := by
  intro h
  exact p.rep_nonzero (congrArg WithLp.ofLp h)

/-- The source metric uses the genuine Euclidean Hermitian norm, not the function-space norm. -/
def projectiveFiberMetric (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : ℝ :=
  ‖ell (projectiveLineRep p)‖ / ‖(WithLp.toLp 2 p.rep : ComplexModel 2)‖

/-- Every actual nonzero line vector gives the same original homogeneous metric ratio. -/
theorem projectiveFiberMetric_eq_ratio (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) (v : p.submodule) (hv : v ≠ 0) :
    projectiveFiberMetric p ell = ‖ell v‖ / ‖(WithLp.toLp 2 v.val : ComplexModel 2)‖ := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (show v.val ∈ ℂ ∙ p.rep from Projectivization.submodule_eq p ▸ v.property)
  have hsub : a • projectiveLineRep p = v := Subtype.ext ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hv
    rw [← hsub, h, zero_smul]
  have hnorm : ‖(WithLp.toLp 2 v.val : ComplexModel 2)‖ =
      ‖a‖ * ‖(WithLp.toLp 2 p.rep : ComplexModel 2)‖ := by
    rw [← ha, WithLp.toLp_smul, norm_smul]
  rw [← hsub, map_smul, norm_smul, hsub, hnorm]
  unfold projectiveFiberMetric
  exact (mul_div_mul_left _ _ (norm_ne_zero_iff.mpr ha0)).symm

/-- Actual one-dimensional span membership makes evaluation at the nonzero lift faithful. -/
theorem projectiveDual_eval_eq_zero_iff (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : ell (projectiveLineRep p) = 0 ↔ ell = 0 := by
  constructor
  · intro h
    ext v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (show v.val ∈ ℂ ∙ p.rep from Projectivization.submodule_eq p ▸ v.property)
    have hsub : a • projectiveLineRep p = v := Subtype.ext ha
    rw [← hsub, map_smul, h, smul_zero]
    rfl
  · rintro rfl
    rfl

theorem projectiveFiberMetric_nonneg (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : 0 ≤ projectiveFiberMetric p ell :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem projectiveFiberMetric_eq_zero_iff (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) : projectiveFiberMetric p ell = 0 ↔ ell = 0 := by
  rw [projectiveFiberMetric, div_eq_zero_iff]
  simp only [norm_eq_zero, projectiveDual_eval_eq_zero_iff,
    projectiveEuclideanRep_ne_zero, or_false]

theorem projectiveFiberMetric_smul (p : Projectivization ℂ (Fin 2 → ℂ))
    (a : ℂ) (ell : projectiveDualFiber p) :
    projectiveFiberMetric p (a • ell) = ‖a‖ * projectiveFiberMetric p ell := by
  simp only [projectiveFiberMetric, LinearMap.smul_apply, norm_smul, mul_div_assoc]

theorem projectiveFiberMetric_add_le (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell eta : projectiveDualFiber p) :
    projectiveFiberMetric p (ell + eta) ≤ projectiveFiberMetric p ell + projectiveFiberMetric p eta := by
  unfold projectiveFiberMetric
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)

/-- Actual normalized evaluation, linear in the original dual-line fiber. -/
def projectiveDualEvaluation (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveDualFiber p →ₗ[ℂ] ℂ where
  toFun := fun ell ↦ ell (projectiveLineRep p) /
    (‖(WithLp.toLp 2 p.rep : ComplexModel 2)‖ : ℂ)
  map_add' := by intro ell eta; simp [add_div]
  map_smul' := by intro a ell; simp [mul_div_assoc]

theorem projectiveDualEvaluation_injective (p : Projectivization ℂ (Fin 2 → ℂ)) :
    Function.Injective (projectiveDualEvaluation p) := by
  intro ell eta h
  have hd : (‖(WithLp.toLp 2 p.rep : ComplexModel 2)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (projectiveEuclideanRep_ne_zero p))
  apply sub_eq_zero.mp
  apply (projectiveDual_eval_eq_zero_iff p (ell - eta)).mp
  change ell (projectiveLineRep p) - eta (projectiveLineRep p) = 0
  apply sub_eq_zero.mpr
  exact (div_left_inj' hd).mp h

theorem norm_projectiveDualEvaluation (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) :
    ‖projectiveDualEvaluation p ell‖ = projectiveFiberMetric p ell := by
  simp only [projectiveDualEvaluation, LinearMap.coe_mk, AddHom.coe_mk, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), projectiveFiberMetric]

/-- A genuine positive Hermitian form on every original `O(1)` fiber,
constructed by actual faithful normalized evaluation. -/
@[instance_reducible] def projectiveFiberHermitianCore (p : Projectivization ℂ (Fin 2 → ℂ)) :
    InnerProductSpace.Core ℂ (projectiveDualFiber p) where
  inner ell eta := inner ℂ (projectiveDualEvaluation p ell) (projectiveDualEvaluation p eta)
  conj_inner_symm := fun ell eta ↦ inner_conj_symm _ _
  re_inner_nonneg := fun ell ↦ by
    rw [← norm_sq_eq_re_inner]
    exact sq_nonneg _
  definite := fun ell h ↦ by
    apply projectiveDualEvaluation_injective p
    simpa only [map_zero] using (inner_self_eq_zero.mp h)
  add_left := by intro ell eta nu; rw [map_add, inner_add_left]
  smul_left := by intro ell eta a; rw [map_smul, inner_smul_left]

/-- The actual Hermitian norm is precisely the original lift-independent metric ratio. -/
theorem projectiveFiberHermitianCore_norm (p : Projectivization ℂ (Fin 2 → ℂ))
    (ell : projectiveDualFiber p) :
    Real.sqrt ((projectiveFiberHermitianCore p).inner ell ell).re =
      projectiveFiberMetric p ell := by
  change Real.sqrt (RCLike.re (inner ℂ (projectiveDualEvaluation p ell)
    (projectiveDualEvaluation p ell))) = _
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), Real.sqrt_sq (norm_nonneg _), norm_projectiveDualEvaluation]

/-- The literal original homogeneous coordinate sections of the actual dual-line fibers. -/
def projectiveCoordinateSection (p : Projectivization ℂ (Fin 2 → ℂ)) (j : Fin 2) :
    projectiveDualFiber p := (LinearMap.proj j).comp p.submodule.subtype

theorem projectiveCoordinateSection_apply (p : Projectivization ℂ (Fin 2 → ℂ))
    (j : Fin 2) (v : p.submodule) : projectiveCoordinateSection p j v = v.val j := rfl

/-- The actual nonzero homogeneous lift in either original affine chart. -/
def projectiveAffineLift (b : Bool) (z : ComplexModel 1) : Fin 2 → ℂ :=
  if b then ![1, projectiveModelEquiv.symm z] else ![projectiveModelEquiv.symm z, 1]

theorem projectiveAffineLift_ne_zero (b : Bool) (z : ComplexModel 1) :
    projectiveAffineLift b z ≠ 0 := by
  cases b <;> simp [projectiveAffineLift]

/-- Each genuine original quotient-chart inverse is represented by its actual homogeneous lift. -/
theorem projectiveModelChart_symm_eq_mk (b : Bool) (z : ComplexModel 1) :
    (projectiveModelChart b).symm z =
      Projectivization.mk ℂ (projectiveAffineLift b z) (projectiveAffineLift_ne_zero b z) := by
  cases b
  · change projectiveLineHomeomorph
      (projectiveFiniteChart.symm (projectiveModelEquiv.symm z)) = _
    rw [projectiveFiniteChart_symm]
    rfl
  · apply projectiveLineHomeomorph.symm.injective
    change projectiveLineHomeomorph.symm (projectiveLineHomeomorph
      (projectiveInfinityChart.symm (projectiveModelEquiv.symm z))) = _
    rw [Homeomorph.symm_apply_apply, projectiveInfinityChart_symm]
    change projectiveReciprocal ((projectiveModelEquiv.symm z : ℂ) : OnePoint ℂ) =
      (OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ (projectiveAffineLift true z) _)
    have hreader : (OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ (projectiveAffineLift true z) (projectiveAffineLift_ne_zero true z)) =
        if projectiveModelEquiv.symm z = 0 then OnePoint.infty else
          (((projectiveModelEquiv.symm z)⁻¹ : ℂ) : OnePoint ℂ) := by
      simp [projectiveAffineLift, OnePoint.equivProjectivization_symm_apply_mk]
    rw [hreader]
    by_cases hz : projectiveModelEquiv.symm z = 0
    · simp [hz, projectiveReciprocal_zero]
    · simp [hz, projectiveReciprocal_coe hz]

theorem projectiveAffineLift_mem (b : Bool) (z : ComplexModel 1) :
    projectiveAffineLift b z ∈ ((projectiveModelChart b).symm z).submodule := by
  rw [projectiveModelChart_symm_eq_mk, Projectivization.submodule_mk]
  exact Submodule.mem_span_singleton_self _

/-- The actual affine lift as an element of its original homogeneous line. -/
def projectiveAffineFiberLift (b : Bool) (z : ComplexModel 1) :
    ((projectiveModelChart b).symm z).submodule :=
  ⟨projectiveAffineLift b z, projectiveAffineLift_mem b z⟩

theorem projectiveAffineFiberLift_ne_zero (b : Bool) (z : ComplexModel 1) :
    projectiveAffineFiberLift b z ≠ 0 := by
  intro h
  exact projectiveAffineLift_ne_zero b z (congrArg Subtype.val h)

theorem projectiveAffineLift_norm_sq (b : Bool) (z : ComplexModel 1) :
    ‖(WithLp.toLp 2 (projectiveAffineLift b z) : ComplexModel 2)‖ ^ 2 =
      1 + Complex.normSq (projectiveModelEquiv.symm z) := by
  cases b <;> simp [EuclideanSpace.norm_sq_eq, projectiveAffineLift,
    Fin.sum_univ_two, ← Complex.sq_norm, add_comm]

/-- The source nowhere-vanishing affine frame, `X₁` or `X₀` in the actual dual fiber. -/
def projectiveAffineFrame (b : Bool) (z : ComplexModel 1) :
    projectiveDualFiber ((projectiveModelChart b).symm z) :=
  projectiveCoordinateSection ((projectiveModelChart b).symm z) (if b then 0 else 1)

theorem projectiveAffineFrame_apply_lift (b : Bool) (z : ComplexModel 1) :
    projectiveAffineFrame b z (projectiveAffineFiberLift b z) = 1 := by
  cases b <;> simp [projectiveAffineFrame, projectiveCoordinateSection,
    projectiveAffineFiberLift, projectiveAffineLift]

theorem projectiveAffineFrame_ne_zero (b : Bool) (z : ComplexModel 1) :
    projectiveAffineFrame b z ≠ 0 := by
  intro h
  have hval := projectiveAffineFrame_apply_lift b z
  rw [h] at hval
  simp at hval

/-- The literal original local metric computation follows from the independent homogeneous ratio. -/
theorem projectiveAffineFrame_metric_sq (b : Bool) (z : ComplexModel 1) :
    projectiveFiberMetric ((projectiveModelChart b).symm z) (projectiveAffineFrame b z) ^ 2 =
      1 / (1 + Complex.normSq (projectiveModelEquiv.symm z)) := by
  rw [projectiveFiberMetric_eq_ratio _ _ (projectiveAffineFiberLift b z)
    (projectiveAffineFiberLift_ne_zero b z), projectiveAffineFrame_apply_lift, norm_one]
  rw [div_pow, one_pow]
  exact congrArg (fun t : ℝ ↦ 1 / t) (projectiveAffineLift_norm_sq b z)

/-- Negative logarithmic metric weight is exactly the original smooth chart potential. -/
theorem neg_log_projectiveAffineFrame_metric_sq (b : Bool) (z : ComplexModel 1) :
    -Real.log (projectiveFiberMetric ((projectiveModelChart b).symm z)
      (projectiveAffineFrame b z) ^ 2) = projectiveFSPotential z := by
  rw [projectiveAffineFrame_metric_sq, one_div, Real.log_inv, neg_neg]
  rfl

/-- The genuine homogeneous dual-fiber metric has precisely the constructed global curvature. -/
theorem projectiveFSForm_eq_metric_curvature (b : Bool) (z : ComplexModel 1) :
    projectiveFSForm.coeff b z = smoothDDC (fun w : ComplexModel 1 ↦
      -Real.log (projectiveFiberMetric ((projectiveModelChart b).symm w)
        (projectiveAffineFrame b w) ^ 2)) z := by
  change smoothDDC projectiveFSPotential z = _
  exact congrArg (fun f : ComplexModel 1 → ℝ ↦ smoothDDC f z)
    (funext (fun w ↦ (neg_log_projectiveAffineFrame_metric_sq b w).symm))

/-- Genuine local smoothness of the original Hermitian metric in both actual nonzero frames. -/
theorem contDiff_projectiveAffineFrame_metric_sq (b : Bool) :
    ContDiff ℝ ∞ (fun z : ComplexModel 1 ↦
      projectiveFiberMetric ((projectiveModelChart b).symm z) (projectiveAffineFrame b z) ^ 2) := by
  have h : ContDiff ℝ ∞ (fun z : ComplexModel 1 ↦
      1 / (1 + Complex.normSq (projectiveModelEquiv.symm z))) :=
    contDiff_const.div (contDiff_const.add contDiff_projectiveModel_normSq)
      (fun z ↦ by have h := Complex.normSq_nonneg (projectiveModelEquiv.symm z); positivity)
  simpa only [projectiveAffineFrame_metric_sq] using h

/-- The actual global source Fubini--Study metric restricts to the literal
original toric conjugate potential, retaining `Trop = log |z|²`. -/
theorem projectiveFSForm_tropicalization {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    projectiveFSForm.coeff false z =
      smoothDDC (fun w : ComplexModel 1 ↦
        projectiveLineLogPartition (tropicalization w 0)) z :=
  (projectiveFSForm_coeff false z).trans (smoothDDC_projectiveLine_tropicalization hz).symm

/-- Literal toric curvature equals the negative-log curvature of the genuine original `O(1)` metric. -/
theorem projectiveLine_toric_eq_metric_curvature {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    smoothDDC (fun w : ComplexModel 1 ↦ projectiveLineLogPartition (tropicalization w 0)) z =
      smoothDDC (fun w : ComplexModel 1 ↦
        -Real.log (projectiveFiberMetric ((projectiveModelChart false).symm w)
          (projectiveAffineFrame false w) ^ 2)) z :=
  (projectiveFSForm_tropicalization hz).symm.trans (projectiveFSForm_eq_metric_curvature false z)

end SGPT.Toric
