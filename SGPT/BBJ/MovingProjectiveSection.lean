import SGPT.Toric.ProjectiveLineLogSingularity
import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Foundations.Analysis.Pending.BergmanSupWeight
import SGPT.Foundations.Analysis.PshAddition

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open SGPT.Toric SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff NNReal ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
/-- The existing actual homogeneous linear section with moving zero `[c:1]`. -/
def movingProjectiveSection (c : ℝ) (p : P1) : projectiveDualFiber p :=
  projectiveLinearSection ![1,-(c : ℂ)] p

/-- The literal normalized logarithm of the existing Fubini--Study fiber norm. -/
def movingProjectiveSectionPotential (c : ℝ) (p : P1) : EReal :=
  ENNReal.log (ENNReal.ofReal (projectiveFiberMetric p (movingProjectiveSection c p)^2)) -
    ((Real.log (1+c^2) : ℝ) : EReal)

/-- The actual coefficients in both original nonvanishing coordinate frames. -/
theorem movingProjectiveSection_coefficient (c : ℝ) (b : Bool) (z : ComplexModel 1) :
    movingProjectiveSection c ((projectiveModelChart b).symm z)
      (projectiveAffineFiberLift b z) =
      if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ) := by
  rw [movingProjectiveSection,projectiveLinearSection_chart_coefficient]
  cases b <;> simp [projectiveModelEquiv_symm_apply,sub_eq_add_neg]

/-- The metric is computed on a genuine nonzero homogeneous lift and its true
Euclidean norm; the original quotient metric is unchanged. -/
theorem movingProjectiveSection_metric_sq (c : ℝ) (b : Bool) (z : ComplexModel 1) :
    projectiveFiberMetric ((projectiveModelChart b).symm z)
      (movingProjectiveSection c ((projectiveModelChart b).symm z)) ^ 2 =
      Complex.normSq (if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) /
        (1+Complex.normSq (z 0)) := by
  rw [projectiveFiberMetric_eq_ratio _ _ (projectiveAffineFiberLift b z)
    (projectiveAffineFiberLift_ne_zero b z)]
  change (‖movingProjectiveSection c ((projectiveModelChart b).symm z)
    (projectiveAffineFiberLift b z)‖ /
    ‖(WithLp.toLp 2 (projectiveAffineLift b z) : ComplexModel 2)‖)^2 = _
  rw [div_pow,projectiveAffineLift_norm_sq,movingProjectiveSection_coefficient,
    Complex.sq_norm,projectiveModelEquiv_symm_apply]

/-- Exact extended-real chart formula, including the zero numerator branch. -/
theorem movingProjectiveSectionPotential_chart (c : ℝ) (b : Bool) (z : ComplexModel 1) :
    movingProjectiveSectionPotential c ((projectiveModelChart b).symm z) =
      logNormSq (if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) -
        (projectiveFSPotential z : EReal) - ((Real.log (1+c^2) : ℝ) : EReal) := by
  rw [movingProjectiveSectionPotential,movingProjectiveSection_metric_sq,projectiveFSPotential_eq]
  by_cases hz : (if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) = 0
  · simp [hz]
  · have hp := Complex.normSq_pos.mpr hz
    have hd : 0 < 1+Complex.normSq (z 0) := by
      have := Complex.normSq_nonneg (z 0)
      linarith
    rw [ENNReal.log_ofReal_of_pos (div_pos hp hd),Real.log_div hp.ne' hd.ne',
      logNormSq_of_ne_zero hz,Complex.sq_norm]
    simp only [EReal.coe_sub]

private theorem finite_sub_sub_add (a : EReal) (r s : ℝ) :
    (a-(r : EReal)-(s : EReal))+(r : EReal) = a-(s : EReal) := by
  cases a with
  | bot => simp
  | top => simp
  | coe a =>
    exact (by simpa only [EReal.coe_sub,EReal.coe_add] using
      congrArg (fun q : ℝ => (q : EReal)) (show a-r-s+r=a-s by ring))

/-- Correction by the actual smooth FS potential gives precisely a logarithm
of the genuine holomorphic affine coefficient and one finite constant. -/
theorem movingProjectiveSectionPotential_corrected_chart (c : ℝ) (b : Bool)
    (z : ComplexModel 1) :
    movingProjectiveSectionPotential c ((projectiveModelChart b).symm z)+
      (projectiveFSPotential z : EReal) =
      logNormSq (if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) -
        ((Real.log (1+c^2) : ℝ) : EReal) := by
  rw [movingProjectiveSectionPotential_chart]
  exact finite_sub_sub_add _ _ _

private theorem coefficient_normSq_le (c : ℝ) (b : Bool) (z : ℂ) :
    Complex.normSq (if b then 1-(c : ℂ)*z else z-(c : ℂ)) ≤
      (1+c^2)*(1+Complex.normSq z) := by
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,add_zero,sub_zero,zero_mul]
  · nlinarith [sq_nonneg (1+c*z.re),sq_nonneg (c*z.im)]
  · nlinarith [sq_nonneg (z.re+c),sq_nonneg z.im]

/-- The original normalization is nonpositive for every real moving center. -/
theorem movingProjectiveSectionPotential_nonpos (c : ℝ) (p : P1) :
    movingProjectiveSectionPotential c p ≤ 0 := by
  have hlocal (b : Bool) (z : ComplexModel 1) :
      movingProjectiveSectionPotential c ((projectiveModelChart b).symm z) ≤ 0 := by
    rw [movingProjectiveSectionPotential,movingProjectiveSection_metric_sq]
    apply EReal.sub_nonpos.mpr
    have hden : 0 < 1+Complex.normSq (z 0) := by
      have := Complex.normSq_nonneg (z 0)
      linarith
    have hle := (div_le_iff₀ hden).mpr (coefficient_normSq_le c b (z 0))
    have hlog := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal hle)
    rwa [ENNReal.log_ofReal_of_pos (by positivity : 0 < 1+c^2)] at hlog
  obtain ⟨b,hb⟩ := projectiveLineAtlas.cover p
  have hp : (projectiveModelChart b).symm ((projectiveModelChart b) p) = p :=
    (projectiveModelChart b).left_inv hb
  simpa only [hp] using hlocal b ((projectiveModelChart b) p)

/-- The extended potential never has a positive-infinite value. -/
theorem movingProjectiveSectionPotential_ne_top (c : ℝ) (p : P1) :
    movingProjectiveSectionPotential c p ≠ ⊤ :=
  ne_of_lt ((movingProjectiveSectionPotential_nonpos c p).trans_lt (by simp))

private theorem coefficient_frequently_ne_zero (c : ℝ) (b : Bool) (z : ComplexModel 1) :
    ∃ᶠ w in 𝓝 z, (if b then 1-(c : ℂ)*w 0 else w 0-(c : ℂ)) ≠ 0 := by
  have hroot (q : ℂ) : ∃ᶠ w in 𝓝 z, w 0 ≠ q := by
    have hz : z ∈ closure ({projectiveModelEquiv q}ᶜ : Set (ComplexModel 1)) := by
      rw [(dense_compl_singleton (projectiveModelEquiv q)).closure_eq]
      trivial
    apply (mem_closure_iff_frequently.mp hz).mono
    intro w hw he
    apply hw
    apply projectiveModelEquiv.symm.injective
    rw [projectiveModelEquiv.symm_apply_apply]
    exact he
  cases b
  · exact (hroot (c : ℂ)).mono fun w hw => by simpa only [Bool.false_eq_true,if_false,sub_ne_zero] using hw
  · by_cases hc : c = 0
    · subst c
      exact Filter.Frequently.of_forall fun w => by simp
    · have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
      apply (hroot ((c : ℂ)⁻¹)).mono
      intro w hw hz
      apply hw
      apply mul_left_cancel₀ hcC
      rw [mul_inv_cancel₀ hcC]
      exact (sub_eq_zero.mp hz).symm

/-- Actual finite points occur in every nonempty original neighborhood. -/
theorem movingProjectiveSectionPotential_locallyNondegenerate (c : ℝ) :
    SGPT.PSH.LocallyNondegenerateOn (movingProjectiveSectionPotential c) univ := by
  intro p _ O hO hpO
  obtain ⟨b,hb⟩ := projectiveLineAtlas.cover p
  change Bool at b
  let z := projectiveModelChart b p
  let D := (projectiveModelChart b).target ∩ (projectiveModelChart b).symm ⁻¹' O
  have hz : z ∈ D := ⟨(projectiveModelChart b).map_source hb,by
    change (projectiveModelChart b).symm ((projectiveModelChart b) p) ∈ O
    rwa [(projectiveModelChart b).left_inv hb]⟩
  have hD : IsOpen D := (projectiveModelChart b).isOpen_inter_preimage_symm hO
  obtain ⟨w,hw,hwD⟩ := (coefficient_frequently_ne_zero c b z).and_eventually
    (hD.mem_nhds hz) |>.exists
  refine ⟨(projectiveModelChart b).symm w,⟨mem_univ _,hwD.2⟩,?_⟩
  rw [movingProjectiveSectionPotential_chart,logNormSq_of_ne_zero hw,← EReal.coe_sub,
    ← EReal.coe_sub]
  exact EReal.coe_ne_bot _

/-- Both genuine holomorphic coefficients produce the corrected PSH functions. -/
theorem movingProjectiveSectionPotential_corrected_psh (c : ℝ) (b : Bool) :
    PlurisubharmonicOn (fun z : ComplexModel 1 =>
      movingProjectiveSectionPotential c ((projectiveModelChart b).symm z)+
        (projectiveFSPotential z : EReal)) univ := by
  have hdiff : Differentiable ℂ (fun z : ComplexModel 1 =>
      if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) := by
    have h := differentiable_projectiveLinearSection_chart_coefficient ![1,-(c : ℂ)] b
    convert h using 1
    funext z
    exact (movingProjectiveSection_coefficient c b z).symm
  have hlog := SGPT.Foundations.Analysis.Pending.BergmanSupWeight.plurisubharmonicOn_logNormSq_comp
    isOpen_univ hdiff.differentiableOn
  intro z hz
  have h := (hlog z hz).add (plurisubharmonicAt_const
    ((-Real.log (1+c^2) : ℝ) : EReal) (EReal.coe_ne_top _) z)
  apply h.congr
  exact Filter.Eventually.of_forall fun w => by
    simpa only [sub_eq_add_neg,EReal.coe_neg] using
      (movingProjectiveSectionPotential_corrected_chart c b w).symm

/-- The entire original source FS-PSH condition is manufactured from actual charts. -/
theorem isThetaPSH_movingProjectiveSectionPotential (c : ℝ) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (movingProjectiveSectionPotential c) := by
  apply isThetaPSH_of_chart_corrected (fun _ => projectiveFSPotential)
    (fun _ => contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ => rfl) ?_
    (movingProjectiveSectionPotential_ne_top c) (movingProjectiveSectionPotential_locallyNondegenerate c)
  intro b z _
  exact movingProjectiveSectionPotential_corrected_psh c b z (mem_univ _)

/-- Genuine native FS-PSH follows through the published one-way dictionary. -/
theorem isThetaPshPotential_movingProjectiveSectionPotential (c : ℝ) :
    IsThetaPshPotential projectiveNativeFSBackground.form.val (movingProjectiveSectionPotential c) :=
  isThetaPshPotential_projectiveNativeFS_of_source (isThetaPSH_movingProjectiveSectionPotential c)

/-- The actual original finite projective point carrying the unique pole. -/
def movingProjectiveSectionPole (c : ℝ) : P1 :=
  projectiveLineHomeomorph ((c : ℂ) : OnePoint ℂ)

private theorem finite_chart_inverse (z : ℂ) :
    (projectiveModelChart false).symm (projectiveModelEquiv z) =
      projectiveLineHomeomorph (z : OnePoint ℂ) := by
  change projectiveLineHomeomorph
    (projectiveFiniteChart.symm (projectiveModelEquiv.symm (projectiveModelEquiv z))) = _
  rw [projectiveModelEquiv.symm_apply_apply,projectiveFiniteChart_symm]

private theorem infinity_chart_inverse :
    (projectiveModelChart true).symm 0 = projectiveLineHomeomorph (OnePoint.infty : OnePoint ℂ) := by
  change projectiveLineHomeomorph (projectiveInfinityChart.symm (projectiveModelEquiv.symm 0)) = _
  rw [map_zero,projectiveInfinityChart_symm,projectiveReciprocal_zero]

/-- Literal normalized homogeneous logarithm in the actual finite chart. -/
theorem movingProjectiveSectionPotential_finite (c : ℝ) (z : ℂ) :
    movingProjectiveSectionPotential c (projectiveLineHomeomorph (z : OnePoint ℂ)) =
      logNormSq (z-(c : ℂ)) - ((Real.log (1+Complex.normSq z) : ℝ) : EReal) -
        ((Real.log (1+c^2) : ℝ) : EReal) := by
  have h := movingProjectiveSectionPotential_chart c false (projectiveModelEquiv z)
  simpa only [finite_chart_inverse,Bool.false_eq_true,if_false,projectiveModelEquiv_apply_zero,
    projectiveFSPotential_eq] using h

/-- The actual infinity value is finite and has the exact printed normalization. -/
theorem movingProjectiveSectionPotential_infinity (c : ℝ) :
    movingProjectiveSectionPotential c (projectiveLineHomeomorph (OnePoint.infty : OnePoint ℂ)) =
      ((-Real.log (1+c^2) : ℝ) : EReal) := by
  have h := movingProjectiveSectionPotential_chart c true 0
  rw [infinity_chart_inverse] at h
  simpa [projectiveFSPotential_eq,logNormSq] using h

/-- The exact unique pole is the actual original quotient point `[c:1]`. -/
theorem movingProjectiveSectionPotential_eq_bot_iff (c : ℝ) (p : P1) :
    movingProjectiveSectionPotential c p = ⊥ ↔ p = movingProjectiveSectionPole c := by
  obtain ⟨q,rfl⟩ := projectiveLineHomeomorph.surjective p
  induction q using OnePoint.rec with
  | infty =>
    rw [movingProjectiveSectionPotential_infinity]
    simp [movingProjectiveSectionPole]
  | coe z =>
    rw [movingProjectiveSectionPotential_finite]
    simp [movingProjectiveSectionPole,sub_eq_add_neg,EReal.add_eq_bot_iff,
      ← EReal.coe_neg]
    change z-(c : ℂ)=0 ↔ z=(c : ℂ)
    exact sub_eq_zero

/-- The uniform infinity lower bound needed for the bounded Cantor centers. -/
theorem movingProjectiveSectionPotential_infinity_lower (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ 1/2) :
    ((-Real.log 2 : ℝ) : EReal) ≤
      movingProjectiveSectionPotential c (projectiveLineHomeomorph (OnePoint.infty : OnePoint ℂ)) := by
  rw [movingProjectiveSectionPotential_infinity,EReal.coe_le_coe_iff]
  have hsq : c^2 ≤ 1 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1+c^2) (by linarith : 1+c^2 ≤ 2)
  linarith

end SGPT.BBJ
