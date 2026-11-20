import SGPT.BBJ.MovingProjectiveSection
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Laplacian Distributions ComplexConjugate

/-- The genuine affine coefficient of the same moving section in either chart. -/
def movingSectionCoefficient (c : ℝ) (b : Bool) (z : ComplexModel 1) : ℂ :=
  if b then 1-(c : ℂ)*projectiveModelEquiv.symm z
    else projectiveModelEquiv.symm z-(c : ℂ)

/-- The actual extended kernel's real chart representative. -/
def movingSectionDensity (c : ℝ) (b : Bool) (z : ComplexModel 1) : ℝ :=
  (movingProjectiveSectionPotential c ((projectiveModelChart b).symm z)).toReal

theorem movingSectionCoefficient_differentiable (c : ℝ) (b : Bool) :
    Differentiable ℂ (movingSectionCoefficient c b) := by
  cases b
  · exact projectiveModelEquiv.symm.differentiable.sub_const _
  · exact differentiable_const _ |>.sub
      ((differentiable_const _).mul projectiveModelEquiv.symm.differentiable)

/-- Affine coefficients are never identically zero in a neighborhood. -/
theorem movingSectionCoefficient_frequently_ne_zero (c : ℝ) (b : Bool)
    (z : ComplexModel 1) : ∃ᶠ w in 𝓝 z, movingSectionCoefficient c b w ≠ 0 := by
  have hroot (a : ℂ) : ∃ᶠ w in 𝓝 z, projectiveModelEquiv.symm w ≠ a := by
    have hz : z ∈ closure ({projectiveModelEquiv a}ᶜ : Set (ComplexModel 1)) := by
      rw [(dense_compl_singleton _).closure_eq]; trivial
    apply (mem_closure_iff_frequently.mp hz).mono
    intro w hw heq
    apply hw
    simp only [mem_singleton_iff, ← heq, projectiveModelEquiv.apply_symm_apply]
  cases b
  · exact (hroot c).mono fun w hw => sub_ne_zero.mpr hw
  · by_cases hc : c = 0
    · subst c
      exact Filter.Frequently.of_forall fun w => by simp [movingSectionCoefficient]
    · have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
      apply (hroot ((c : ℂ)⁻¹)).mono
      intro w hw hz
      apply hw
      apply mul_left_cancel₀ hcC
      rw [mul_inv_cancel₀ hcC]
      exact (sub_eq_zero.mp hz).symm

/-- Actual logarithmic affine coefficients have genuine local L1 densities. -/
theorem locallyIntegrable_movingSectionLog (c : ℝ) (b : Bool) :
    LocallyIntegrableOn (fun z => Real.log (‖movingSectionCoefficient c b z‖^2))
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume :=
  Pending.DivisorIntegrationCurrent.locallyIntegrableOn_log_normSq isOpen_univ
    (movingSectionCoefficient_differentiable c b).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero c b z)

/-- Finite readback is used only on the actual conull nonzero set. -/
theorem movingSectionDensity_ae (c : ℝ) (b : Bool) :
    movingSectionDensity c b =ᵐ[volume.restrict (⊤ : TopologicalSpace.Opens (ComplexModel 1))]
      (fun z => Real.log (‖movingSectionCoefficient c b z‖^2) -
        projectiveFSPotential z - Real.log (1+c^2)) := by
  have hne := Pending.LelongPoincareDivisor.ae_ne_zero isOpen_univ
    (movingSectionCoefficient_differentiable c b).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero c b z)
  filter_upwards [hne] with z hz
  change (movingProjectiveSectionPotential c ((projectiveModelChart b).symm z)).toReal = _
  rw [movingProjectiveSectionPotential_chart]
  have hcoeff : (if b then 1-(c : ℂ)*z 0 else z 0-(c : ℂ)) =
      movingSectionCoefficient c b z := by simp only [movingSectionCoefficient,projectiveModelEquiv_symm_apply]
  rw [hcoeff, logNormSq_of_ne_zero hz, ← EReal.coe_sub, ← EReal.coe_sub,EReal.toReal_coe]

/-- Actual QPSH, not pointwise totalized logarithm algebra, supplies local L1. -/
theorem locallyIntegrable_movingSectionDensity (c : ℝ) (b : Bool) :
    LocallyIntegrableOn (movingSectionDensity c b)
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume := by
  have ht : (projectiveModelChart b).target = univ := by
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  have h := ((isThetaPshPotential_movingProjectiveSectionPotential c).quasiPshPotential).locallyIntegrableOn_chart_toReal (projectiveNativeChart b)
  change LocallyIntegrableOn (movingSectionDensity c b) (projectiveModelChart b).target volume at h
  rw [ht] at h
  exact h

/-- Finite constants require local, not global, integrability. -/
theorem locallyIntegrable_movingSectionConstant (c : ℝ) :
    LocallyIntegrableOn (fun _ : ComplexModel 1 => Real.log (1+c^2))
      (⊤ : TopologicalSpace.Opens (ComplexModel 1)) volume :=
  continuous_const.locallyIntegrable.locallyIntegrableOn _

/-- The genuine distribution identity is obtained by AE congruence at the pole. -/
theorem movingSectionDensity_regularDistribution (c : ℝ) (b : Bool) :
    regularDistribution volume (movingSectionDensity c b)
      (locallyIntegrable_movingSectionDensity c b) =
    regularDistribution volume (fun z => Real.log (‖movingSectionCoefficient c b z‖^2))
      (locallyIntegrable_movingSectionLog c b) -
    regularDistribution volume projectiveFSPotential locallyIntegrable_projectiveFSPotential -
    regularDistribution volume (fun _ => Real.log (1+c^2))
      (locallyIntegrable_movingSectionConstant c) := by
  have hl := (locallyIntegrable_movingSectionLog c b).sub
    locallyIntegrable_projectiveFSPotential
  have hsub := Pending.ThetaPshChartLimitGluing.regularDistribution_sub
    hl (locallyIntegrable_movingSectionConstant c)
  have hsub' := Pending.ThetaPshChartLimitGluing.regularDistribution_sub
    (locallyIntegrable_movingSectionLog c b) locallyIntegrable_projectiveFSPotential
  rw [← hsub']
  change _ = regularDistribution volume
    ((fun z => Real.log (‖movingSectionCoefficient c b z‖^2))-projectiveFSPotential) hl - _
  rw [← hsub]
  exact regularDistribution_congr_ae_on (locallyIntegrable_movingSectionDensity c b)
    (hl.sub (locallyIntegrable_movingSectionConstant c)) (movingSectionDensity_ae c b)

/-- The literal affine function, with its nonzero scalar as a genuine unit. -/
def affineSectionFunction (a A : ℂ) (z : ComplexModel 1) : ℂ :=
  A*(projectiveModelEquiv.symm z-a)

/-- Actual multiplicity-one translated divisor presentation. -/
def affineSectionPresentation (a A : ℂ) (hA : A ≠ 0) :
    Pending.DivisorRegularLocus.RegularPresentation (affineSectionFunction a A)
      (projectiveModelEquiv a) where
  U := univ
  isOpen := isOpen_univ
  mem := mem_univ _
  m := 1
  m_pos := one_pos
  h := fun z => projectiveModelEquiv.symm z-a
  v := fun _ => A
  h_diff := projectiveModelEquiv.symm.differentiable.sub_const a |>.differentiableOn
  v_diff := differentiableOn_const _
  h_zero := by simp
  dh_ne := by
    intro y _ hzero
    rw [fderiv_sub_const] at hzero
    change fderiv ℂ projectiveModelEquiv.symm.toContinuousLinearMap y = 0 at hzero
    rw [projectiveModelEquiv.symm.toContinuousLinearMap.fderiv] at hzero
    have hval := congrArg (fun L : ComplexModel 1 →L[ℂ] ℂ => L (projectiveModelEquiv 1)) hzero
    simp at hval
  v_ne := fun _ _ => hA
  eq := fun _ _ => by simp [affineSectionFunction,mul_comm]

theorem affineSection_regularLocus (a A : ℂ) (hA : A ≠ 0) :
    Pending.DivisorRegularLocus.regularLocus (affineSectionFunction a A) =
      {projectiveModelEquiv a} := by
  ext z
  constructor
  · rintro ⟨P⟩
    have hz := P.g_x
    have heq : projectiveModelEquiv.symm z = a :=
      sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hA)
    simp only [mem_singleton_iff, ← heq, projectiveModelEquiv.apply_symm_apply]
  · rintro rfl
    exact (affineSectionPresentation a A hA).mem_regularLocus

theorem affineSection_transverseForm (a A : ℂ) (hA : A ≠ 0) (v w : ComplexModel 1) :
    Pending.DivisorRegularLocus.transverseForm (affineSectionFunction a A)
      (projectiveModelEquiv a) v w = (conj (v 0)*w 0).im := by
  have h := (affineSectionPresentation a A hA).transverseForm_eq v w
  change _ = Pending.DivisorRegularLocus.lineForm
    (fderiv ℂ (fun z => projectiveModelEquiv.symm z-a) (projectiveModelEquiv a)) v w at h
  rw [fderiv_sub_const] at h
  change _ = Pending.DivisorRegularLocus.lineForm
    (fderiv ℂ projectiveModelEquiv.symm.toContinuousLinearMap (projectiveModelEquiv a)) v w at h
  rw [projectiveModelEquiv.symm.toContinuousLinearMap.fderiv] at h
  rw [h,Pending.DivisorRegularLocus.lineForm,projectiveModelEquiv_symm_opNorm]
  simp [projectiveModelEquiv_symm_apply]

theorem affineSection_differentiable (a A : ℂ) :
    Differentiable ℂ (affineSectionFunction a A) :=
  (differentiable_const A).mul (projectiveModelEquiv.symm.differentiable.sub_const a)

theorem affineSection_frequently_ne_zero (a A : ℂ) (hA : A ≠ 0)
    (z : ComplexModel 1) : ∃ᶠ w in 𝓝 z, affineSectionFunction a A w ≠ 0 := by
  have hz : z ∈ closure ({projectiveModelEquiv a}ᶜ : Set (ComplexModel 1)) := by
    rw [(dense_compl_singleton _).closure_eq]; trivial
  apply (mem_closure_iff_frequently.mp hz).mono
  intro w hw heq
  have heq' : projectiveModelEquiv.symm w = a :=
    sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hA)
  apply hw
  simp only [mem_singleton_iff, ← heq', projectiveModelEquiv.apply_symm_apply]

/-- The actual current, not a Dirac-current certificate. -/
def affineSectionDivisorCurrent (a A : ℂ) (hA : A ≠ 0) :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  Pending.DivisorIntegrationCurrent.divisorCurrent
    (affineSection_differentiable a A).differentiableOn
    (fun z _ => affineSection_frequently_ne_zero a A hA z)

/-- All directions and all tests give the normalized simple point current. -/
theorem affineSectionDivisorCurrent_apply (a A : ℂ) (hA : A ≠ 0)
    (v w : ComplexModel 1) (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    affineSectionDivisorCurrent a A hA ![v,w] φ =
      φ (projectiveModelEquiv a)*(conj (v 0)*w 0).im := by
  rw [affineSectionDivisorCurrent,Pending.DivisorIntegrationCurrent.divisorCurrent_apply]
  simp only [Pending.DivisorIntegrationCurrent.divisorDensity,affineSection_regularLocus a A hA]
  have heq : (fun x : ComplexModel 1 => φ x * ({projectiveModelEquiv a} : Set (ComplexModel 1)).indicator
      (fun x => (Pending.DivisorRegularLocus.divisorMult (affineSectionFunction a A) x : ℝ) *
        Pending.DivisorRegularLocus.transverseForm (affineSectionFunction a A) x v w) x) =
      ({projectiveModelEquiv a} : Set (ComplexModel 1)).indicator (fun x => φ x *
        ((Pending.DivisorRegularLocus.divisorMult (affineSectionFunction a A) x : ℝ) *
          Pending.DivisorRegularLocus.transverseForm (affineSectionFunction a A) x v w)) := by
    funext x
    by_cases hx : x ∈ ({projectiveModelEquiv a} : Set (ComplexModel 1)) <;> simp [hx]
  rw [heq,integral_indicator (measurableSet_singleton _),integral_singleton]
  simp [measureReal_def,Measure.euclideanHausdorffMeasure_zero,
    (affineSectionPresentation a A hA).divisorMult_eq,affineSection_transverseForm a A hA,
    affineSectionPresentation]

/-- The actual chart divisor current of the holomorphic moving coefficient. -/
def movingSectionDivisorCurrent (c : ℝ) (b : Bool) :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  Pending.DivisorIntegrationCurrent.divisorCurrent
    (movingSectionCoefficient_differentiable c b).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero c b z)

/-- The curvature of the true real chart density, with its actual L1 witness. -/
def movingSectionMetricCurrent (c : ℝ) (b : Bool) :
    LocalCurrents.DistributionForm (⊤ : TopologicalSpace.Opens (ComplexModel 1)) 2 :=
  LocalCurrents.ddC (regularDistribution volume (movingSectionDensity c b)
    (locallyIntegrable_movingSectionDensity c b))

private theorem ddC_finiteConstant (c : ℝ) :
    LocalCurrents.ddC (regularDistribution volume (fun _ : ComplexModel 1 => Real.log (1+c^2))
      (locallyIntegrable_movingSectionConstant c)) = 0 := by
  ext v φ
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  rw [Pending.LelongPoincareDivisor.ddC_regularDistribution_apply_of_contDiffOn
    contDiffOn_const]
  simp [GlobalPotentialTransforms.smoothDDC_const]

/-- Full normalized current equality on either original chart, including c=0. -/
theorem movingSection_lelongPoincare (c : ℝ) (b : Bool) :
    projectiveFSCurvatureCurrent + movingSectionMetricCurrent c b =
      movingSectionDivisorCurrent c b := by
  change Pending.LelongPoincareDivisor.ddCLM _ +
    Pending.LelongPoincareDivisor.ddCLM _ = _
  rw [movingSectionDensity_regularDistribution,map_sub,map_sub]
  have hconst := ddC_finiteConstant c
  change Pending.LelongPoincareDivisor.ddCLM _ = 0 at hconst
  rw [hconst,sub_zero]
  have hlog := Pending.DivisorIntegrationCurrent.ddC_log_normSq_eq_divisorCurrent
    (Ω := (⊤ : TopologicalSpace.Opens (ComplexModel 1)))
    (movingSectionCoefficient_differentiable c b).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero c b z)
  change Pending.LelongPoincareDivisor.ddCLM _ = movingSectionDivisorCurrent c b at hlog
  rw [← hlog]
  abel

/-- The finite chart gives the actual pole, without any rescaling factor. -/
theorem movingSectionDivisorCurrent_finite (c : ℝ) :
    movingSectionDivisorCurrent c false = affineSectionDivisorCurrent (c : ℂ) 1 one_ne_zero := by
  have hf : movingSectionCoefficient c false = affineSectionFunction (c : ℂ) 1 := by
    funext z; simp [movingSectionCoefficient,affineSectionFunction]
  unfold movingSectionDivisorCurrent affineSectionDivisorCurrent
  simp only [hf]

/-- The nonzero infinity-chart coefficient has the reciprocal root and a unit. -/
theorem movingSectionDivisorCurrent_infinity (c : ℝ) (hc : c ≠ 0) :
    movingSectionDivisorCurrent c true =
      affineSectionDivisorCurrent ((c : ℂ)⁻¹) (-(c : ℂ))
        (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc)) := by
  have hf : movingSectionCoefficient c true = affineSectionFunction ((c : ℂ)⁻¹) (-(c : ℂ)) := by
    funext z
    dsimp [movingSectionCoefficient,affineSectionFunction]
    rw [mul_sub,neg_mul,neg_mul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc)]
    ring
  unfold movingSectionDivisorCurrent affineSectionDivisorCurrent
  simp only [hf]

/-- At center zero the infinity chart has no divisor. -/
theorem movingSectionDivisorCurrent_infinity_zero : movingSectionDivisorCurrent 0 true = 0 := by
  have hreg : Pending.DivisorRegularLocus.regularLocus (movingSectionCoefficient 0 true) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨P⟩
    have h := P.g_x
    simp [movingSectionCoefficient] at h
  ext v φ
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  rw [movingSectionDivisorCurrent,Pending.DivisorIntegrationCurrent.divisorCurrent_apply]
  simp [Pending.DivisorIntegrationCurrent.divisorDensity,hreg]

/-- The full finite-chart current evaluated on any genuine test and direction pair. -/
theorem movingSection_lelongPoincare_finite_apply (c : ℝ) (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent + movingSectionMetricCurrent c false) ![v,w] φ =
      φ (projectiveModelEquiv (c : ℂ))*(conj (v 0)*w 0).im := by
  rw [movingSection_lelongPoincare,movingSectionDivisorCurrent_finite]
  exact affineSectionDivisorCurrent_apply _ _ _ v w φ

/-- The original unit oriented frame yields precisely evaluation at the moving pole. -/
theorem movingSection_lelongPoincare_finite_standard (c : ℝ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent + movingSectionMetricCurrent c false)
      ![projectiveModelEquiv 1,projectiveModelEquiv Complex.I] φ =
      φ (projectiveModelEquiv (c : ℂ)) := by
  simpa [projectiveModelEquiv_apply_zero] using
    movingSection_lelongPoincare_finite_apply c (projectiveModelEquiv 1)
      (projectiveModelEquiv Complex.I) φ

/-- Both actual infinity-chart branches, all real centers, all directions and tests. -/
theorem movingSection_lelongPoincare_infinity_apply (c : ℝ) (v w : ComplexModel 1)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (ComplexModel 1)), ℝ)) :
    (projectiveFSCurvatureCurrent + movingSectionMetricCurrent c true) ![v,w] φ =
      if c = 0 then 0 else φ (projectiveModelEquiv ((c : ℂ)⁻¹))*(conj (v 0)*w 0).im := by
  rw [movingSection_lelongPoincare]
  split_ifs with hc
  · subst c
    rw [movingSectionDivisorCurrent_infinity_zero]
    rfl
  · rw [movingSectionDivisorCurrent_infinity c hc]
    exact affineSectionDivisorCurrent_apply _ _ _ v w φ

/-- The finite-chart evaluation point is the original quotient pole `[c:1]`. -/
theorem movingSection_finite_root (c : ℝ) :
    (projectiveModelChart false).symm (projectiveModelEquiv (c : ℂ)) =
      movingProjectiveSectionPole c := by
  apply (movingProjectiveSectionPotential_eq_bot_iff c _).mp
  rw [movingProjectiveSectionPotential_chart]
  simp [projectiveModelEquiv_apply_zero]

/-- The reciprocal root in the opposite chart is the same original quotient pole. -/
theorem movingSection_infinity_root (c : ℝ) (hc : c ≠ 0) :
    (projectiveModelChart true).symm (projectiveModelEquiv ((c : ℂ)⁻¹)) =
      movingProjectiveSectionPole c := by
  apply (movingProjectiveSectionPotential_eq_bot_iff c _).mp
  rw [movingProjectiveSectionPotential_chart]
  simp [projectiveModelEquiv_apply_zero,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc)]

end SGPT.BBJ
