import SGPT.Toric.ProjectiveLineFubiniStudy
import SGPT.PSH.VariablePullback
import SGPT.Toric.RelativeThetaCriterion

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology OnePoint Classical

/-- The actual diagonal character action on original homogeneous vectors. -/
def projectiveTorusLinear (a : ℂˣ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v i := if i = 0 then (a : ℂ) * v i else v i
  map_add' v w := by
    funext i
    by_cases hi : i = 0 <;> simp [hi, mul_add]
  map_smul' c v := by
    funext i
    by_cases hi : i = 0 <;> simp [hi, mul_left_comm]

/-- Genuine inverse coordinates give injectivity before quotient descent. -/
theorem projectiveTorusLinear_injective (a : ℂˣ) :
    Function.Injective (projectiveTorusLinear a) := by
  intro v w h
  funext i
  have hi := congr_fun h i
  by_cases hzero : i = 0
  · have hi' : (a : ℂ) * v i = (a : ℂ) * w i := by
      simpa only [projectiveTorusLinear, LinearMap.coe_mk, AddHom.coe_mk,
        if_pos hzero] using hi
    exact mul_left_cancel₀ (Units.ne_zero a) hi'
  · simpa only [projectiveTorusLinear, LinearMap.coe_mk, AddHom.coe_mk,
      if_neg hzero] using hi

/-- The circle action is the restriction of this genuine quotient torus action. -/
def projectiveTorusAction (a : ℂˣ) :
    Projectivization ℂ (Fin 2 → ℂ) → Projectivization ℂ (Fin 2 → ℂ) :=
  Projectivization.map (projectiveTorusLinear a) (projectiveTorusLinear_injective a)

/-- Actual affine homogeneous coordinates produce scalar multiplication. -/
theorem projectiveTorusAction_finite (a : ℂˣ) (z : ℂ) :
    projectiveTorusAction a (OnePoint.equivProjectivization ℂ (z : OnePoint ℂ)) =
      OnePoint.equivProjectivization ℂ (((a : ℂ) * z : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.equivProjectivization_apply_coe, projectiveTorusAction,
    Projectivization.map_mk, OnePoint.equivProjectivization_apply_coe]
  congr 1
  ext i
  fin_cases i <;> simp [projectiveTorusLinear]

/-- The original point at infinity is fixed, by true homogeneous scaling. -/
theorem projectiveTorusAction_infinity (a : ℂˣ) :
    projectiveTorusAction a (OnePoint.equivProjectivization ℂ ∞) =
      OnePoint.equivProjectivization ℂ ∞ := by
  rw [OnePoint.equivProjectivization_apply_infinity, projectiveTorusAction,
    Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(a : ℂ), ?_⟩
  ext i
  fin_cases i <;> simp [projectiveTorusLinear]

/-- Genuine affine coordinate identities prove the torus group multiplication law. -/
theorem projectiveTorusAction_mul (a b : ℂˣ)
    (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveTorusAction (a * b) p =
      projectiveTorusAction a (projectiveTorusAction b p) := by
  obtain ⟨q, rfl⟩ := (OnePoint.equivProjectivization ℂ).surjective p
  cases q with
  | coe z => simp only [projectiveTorusAction_finite, Units.val_mul, mul_assoc]
  | infty => simp only [projectiveTorusAction_infinity]

/-- The genuine unit character fixes every original quotient point. -/
theorem projectiveTorusAction_one (p : Projectivization ℂ (Fin 2 → ℂ)) :
    projectiveTorusAction 1 p = p := by
  obtain ⟨q, rfl⟩ := (OnePoint.equivProjectivization ℂ).surjective p
  cases q with
  | coe z => simp only [projectiveTorusAction_finite, Units.val_one, one_mul]
  | infty => exact projectiveTorusAction_infinity 1

/-- The action is continuous for the original coinduced quotient topology. -/
theorem continuous_projectiveTorusAction (a : ℂˣ) :
    Continuous (projectiveTorusAction a) := by
  have hlin : Continuous (projectiveTorusLinear a) := by
    change Continuous (fun v : Fin 2 → ℂ ↦ fun i ↦
      if i = 0 then (a : ℂ) * v i else v i)
    apply continuous_pi
    intro i
    split_ifs <;> fun_prop
  have hsub : Continuous (fun v : {v : Fin 2 → ℂ // v ≠ 0} ↦
      (⟨projectiveTorusLinear a v.1, by
        simpa only [map_zero] using
          (projectiveTorusLinear_injective a).ne v.2⟩ :
        {v : Fin 2 → ℂ // v ≠ 0})) :=
    (hlin.comp continuous_subtype_val).subtype_mk _
  apply continuous_coinduced_dom.mpr
  exact continuous_quotient_mk'.comp hsub

/-- Original quotient torus elements act by genuine homeomorphisms. -/
def projectiveTorusHomeomorph (a : ℂˣ) :
    Projectivization ℂ (Fin 2 → ℂ) ≃ₜ Projectivization ℂ (Fin 2 → ℂ) where
  toFun := projectiveTorusAction a
  invFun := projectiveTorusAction a⁻¹
  left_inv p := by
    rw [← projectiveTorusAction_mul, inv_mul_cancel, projectiveTorusAction_one]
  right_inv p := by
    rw [← projectiveTorusAction_mul, mul_inv_cancel, projectiveTorusAction_one]
  continuous_toFun := continuous_projectiveTorusAction a
  continuous_invFun := continuous_projectiveTorusAction a⁻¹

/-- The actual diagonal action has original reciprocal chart weight at infinity. -/
def projectiveTorusChartFactor (a : ℂˣ) (b : Bool) : ℂ :=
  if b then ((a⁻¹ : ℂˣ) : ℂ) else (a : ℂ)

/-- Literal homogeneous scaling produces the full original chart formula. -/
theorem projectiveTorusAction_chart_symm (a : ℂˣ) (b : Bool) (z : ComplexModel 1) :
    projectiveTorusAction a ((projectiveModelChart b).symm z) =
      (projectiveModelChart b).symm (projectiveTorusChartFactor a b • z) := by
  rw [projectiveModelChart_symm_eq_mk, projectiveTorusAction, Projectivization.map_mk,
    projectiveModelChart_symm_eq_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  cases b
  · refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [projectiveAffineLift, projectiveTorusLinear,
      projectiveTorusChartFactor, map_smul, smul_eq_mul]
  · refine ⟨(a : ℂ), ?_⟩
    ext i
    fin_cases i <;> simp [projectiveAffineLift, projectiveTorusLinear,
      projectiveTorusChartFactor, map_smul, smul_eq_mul]

/-- The original affine sources are preserved by each genuine torus element. -/
theorem projectiveTorusAction_mem_chart (a : ℂˣ) (b : Bool)
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∈ (projectiveModelChart b).source) :
    projectiveTorusAction a p ∈ (projectiveModelChart b).source := by
  rw [← (projectiveModelChart b).left_inv hp, projectiveTorusAction_chart_symm]
  apply (projectiveModelChart b).map_target
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

/-- All actual coordinate representatives are holomorphic on their true domains. -/
theorem projectiveTorusAction_isHolomorphic (a : ℂˣ) :
    projectiveLineAtlas.IsHolomorphic projectiveLineAtlas (projectiveTorusAction a) := by
  refine ⟨continuous_projectiveTorusAction a, ?_⟩
  intro i j
  change Bool at i j
  let c := projectiveTorusChartFactor a i
  let U := (projectiveModelChart i).target ∩
    (projectiveModelChart i).symm ⁻¹'
      (projectiveTorusAction a ⁻¹' (projectiveModelChart j).source)
  have hsource : ∀ z ∈ U, c • z ∈
      ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simp [projectiveModelChart, projectiveQuotientScalarChart_target]
    · change (projectiveModelChart i).symm (projectiveTorusChartFactor a i • z) ∈
        (projectiveModelChart j).source
      rw [← projectiveTorusAction_chart_symm]
      exact hz.2
  have hs : DifferentiableOn ℂ (fun z : ComplexModel 1 ↦ c • z) U :=
    (differentiable_id.const_smul c).differentiableOn
  apply ((differentiableOn_projectiveModelChart_transition i j).comp hs hsource).congr
  intro z _
  change (projectiveModelChart j)
      (projectiveTorusAction a ((projectiveModelChart i).symm z)) =
    (projectiveModelChart j) ((projectiveModelChart i).symm (c • z))
  rw [projectiveTorusAction_chart_symm]

end SGPT.Toric

namespace SGPT.Toric
open Set Filter
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- Actual unit-modulus multiplication preserves the computed reference potential. -/
theorem projectiveFSPotential_smul {c : ℂ} (hc : ‖c‖ = 1) (z : ComplexModel 1) :
    projectiveFSPotential (c • z) = projectiveFSPotential z := by
  have hcSq : Complex.normSq c = 1 := by
    rw [← Complex.sq_norm, hc]
    norm_num
  simp only [projectiveFSPotential_eq, PiLp.smul_apply, smul_eq_mul,
    Complex.normSq_mul, hcSq, one_mul]

/-- The reciprocal character in the opposite chart is also genuinely unitary. -/
theorem norm_projectiveTorusChartFactor {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (b : Bool) :
    ‖projectiveTorusChartFactor a b‖ = 1 := by
  cases b <;> simp [projectiveTorusChartFactor, norm_inv, ha]

/-- Genuine circle pullback preserves the entire original universal theta-PSH class. -/
theorem isThetaPSH_comp_projectiveTorusAction
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm (u ∘ projectiveTorusAction a) := by
  have hnd : LocallyNondegenerateOn (u ∘ projectiveTorusAction a) univ := by
    intro x _ O hO hxO
    let e := projectiveTorusHomeomorph a
    obtain ⟨y, hy, hfin⟩ := hu.locallyNondegenerate (e x) (mem_univ _)
      (e '' O) (e.isOpenMap O hO) ⟨x, hxO, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy.2
    exact ⟨z, ⟨mem_univ _, hz⟩, hfin⟩
  apply isThetaPSH_global_from_relative (fun _ ↦ projectiveFSPotential)
    (fun _ ↦ contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ ↦ rfl)
    _ (fun p ↦ hu.1 _) hnd
  intro b
  change Bool at b
  have hc := norm_projectiveTorusChartFactor ha b
  have hp := hu.preferred_chart_corrected (i := b)
    contDiff_projectiveFSPotential.contDiffOn (fun _ _ ↦ rfl)
  change PlurisubharmonicOn
    (fun z ↦ u ((projectiveModelChart b).symm z) + (projectiveFSPotential z : EReal))
    (projectiveModelChart b).target at hp
  have hp' : PlurisubharmonicOn
      (fun z ↦ u ((projectiveModelChart b).symm z) + (projectiveFSPotential z : EReal))
      univ := by
    simpa [projectiveModelChart, projectiveQuotientScalarChart_target] using hp
  let c := projectiveTorusChartFactor a b
  have hs := hp'.comp_continuousLinearMap
    (c • (ContinuousLinearMap.id ℂ (ComplexModel 1)))
  change PlurisubharmonicOn
    (fun z ↦ (u ∘ projectiveTorusAction a) ((projectiveModelChart b).symm z) +
      (projectiveFSPotential z : EReal)) (projectiveModelChart b).target
  intro z _
  have hs' := hs z (mem_univ _)
  apply hs'.congr
  exact Eventually.of_forall fun y ↦ by
    change u ((projectiveModelChart b).symm (c • y)) +
        (projectiveFSPotential (c • y) : EReal) =
      u (projectiveTorusAction a ((projectiveModelChart b).symm y)) +
        (projectiveFSPotential y : EReal)
    rw [projectiveTorusAction_chart_symm, projectiveFSPotential_smul hc]

end SGPT.Toric
