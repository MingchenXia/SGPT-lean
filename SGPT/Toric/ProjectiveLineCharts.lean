import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import SGPT.PSH.VariableAtlas

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter Bornology
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology OnePoint

/-- Reciprocal on the actual compact point space swaps zero and infinity. -/
def projectiveReciprocal (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z ↦ if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ))

@[simp] theorem projectiveReciprocal_infty :
    projectiveReciprocal ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem projectiveReciprocal_zero :
    projectiveReciprocal ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [projectiveReciprocal]

theorem projectiveReciprocal_coe {z : ℂ} (hz : z ≠ 0) :
    projectiveReciprocal (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [projectiveReciprocal, hz]

/-- Actual field inverse identities supply the entire involution. -/
theorem projectiveReciprocal_involutive : Function.Involutive projectiveReciprocal := by
  intro p
  cases p with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp
    · rw [projectiveReciprocal_coe hz, projectiveReciprocal_coe (inv_ne_zero hz), inv_inv]

/-- Actual punctured-zero inverse convergence gives original compact continuity at zero. -/
theorem continuousAt_projectiveReciprocal_zero :
    ContinuousAt projectiveReciprocal ((0 : ℂ) : OnePoint ℂ) := by
  apply OnePoint.continuousAt_coe.mpr
  have hinv : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
    apply OnePoint.tendsto_coe_infty.comp
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  have hpunc : Tendsto (fun z : ℂ ↦ projectiveReciprocal (z : OnePoint ℂ))
      (𝓝[≠] 0) (𝓝 ∞) :=
    hinv.congr' (eventually_nhdsWithin_of_forall
      fun z (hz : z ≠ 0) ↦ (projectiveReciprocal_coe hz).symm)
  change Tendsto (fun z : ℂ ↦ projectiveReciprocal (z : OnePoint ℂ)) (𝓝 0)
    (𝓝 (projectiveReciprocal ((0 : ℂ) : OnePoint ℂ)))
  rw [projectiveReciprocal_zero]
  rw [← nhdsNE_sup_pure]
  exact hpunc.sup (by
    simpa only [projectiveReciprocal_zero] using
      tendsto_pure_nhds (fun z : ℂ ↦ projectiveReciprocal (z : OnePoint ℂ)) (0 : ℂ))

/-- Actual inverse convergence at infinity uses the original cocompact topology. -/
theorem continuousAt_projectiveReciprocal_infty : ContinuousAt projectiveReciprocal ∞ := by
  apply OnePoint.continuousAt_infty'.mpr
  have hinv : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ))
      (coclosedCompact ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
    apply OnePoint.continuous_coe.continuousAt.tendsto.comp
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded (α := ℂ))
  have hn : Tendsto (norm : ℂ → ℝ) (coclosedCompact ℂ) atTop := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (tendsto_norm_cobounded_atTop (E := ℂ))
  apply hinv.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop 0)] with z hz
  exact (projectiveReciprocal_coe (norm_pos_iff.mp hz)).symm

/-- The actual reciprocal map is globally continuous, without a continuity certificate. -/
theorem continuous_projectiveReciprocal : Continuous projectiveReciprocal := by
  rw [continuous_iff_continuousAt]
  intro p
  cases p with
  | infty => exact continuousAt_projectiveReciprocal_infty
  | coe z =>
    by_cases hz : z = 0
    · subst z
      exact continuousAt_projectiveReciprocal_zero
    · apply OnePoint.continuousAt_coe.mpr
      change Tendsto (fun w : ℂ ↦ projectiveReciprocal (w : OnePoint ℂ))
        (𝓝 z) (𝓝 (projectiveReciprocal (z : OnePoint ℂ)))
      rw [projectiveReciprocal_coe hz]
      apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).tendsto.congr'
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact (projectiveReciprocal_coe hw).symm

/-- Genuine compact reciprocal homeomorphism, produced from actual continuity and involution. -/
def projectiveReciprocalHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := projectiveReciprocal
  invFun := projectiveReciprocal
  left_inv := projectiveReciprocal_involutive
  right_inv := projectiveReciprocal_involutive
  continuous_toFun := continuous_projectiveReciprocal
  continuous_invFun := continuous_projectiveReciprocal

/-- The ordinary finite affine chart is the inverse of the actual open embedding. -/
def projectiveFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℂ → OnePoint ℂ)).symm

theorem projectiveFiniteChart_source :
    projectiveFiniteChart.source = range ((↑) : ℂ → OnePoint ℂ) := by
  simp only [projectiveFiniteChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

theorem projectiveFiniteChart_target : projectiveFiniteChart.target = univ := by
  simp only [projectiveFiniteChart, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]

@[simp] theorem projectiveFiniteChart_coe (z : ℂ) : projectiveFiniteChart (z : OnePoint ℂ) = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv ((↑) : ℂ → OnePoint ℂ)

@[simp] theorem projectiveFiniteChart_symm (z : ℂ) :
    projectiveFiniteChart.symm z = (z : OnePoint ℂ) := by
  simp only [projectiveFiniteChart, OpenPartialHomeomorph.symm_symm,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

/-- The infinity chart uses the produced reciprocal homeomorphism of the original compact space. -/
def projectiveInfinityChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  projectiveReciprocalHomeomorph.transOpenPartialHomeomorph projectiveFiniteChart

theorem projectiveInfinityChart_target : projectiveInfinityChart.target = univ :=
  projectiveFiniteChart_target

@[simp] theorem projectiveInfinityChart_infty : projectiveInfinityChart ∞ = 0 := by
  change projectiveFiniteChart (projectiveReciprocal ∞) = 0
  simp

theorem projectiveInfinityChart_coe {z : ℂ} (hz : z ≠ 0) :
    projectiveInfinityChart (z : OnePoint ℂ) = z⁻¹ := by
  change projectiveFiniteChart (projectiveReciprocal (z : OnePoint ℂ)) = z⁻¹
  rw [projectiveReciprocal_coe hz, projectiveFiniteChart_coe]

@[simp] theorem projectiveInfinityChart_symm (z : ℂ) :
    projectiveInfinityChart.symm z = projectiveReciprocal (z : OnePoint ℂ) := by
  change projectiveReciprocal (projectiveFiniteChart.symm z) = _
  rw [projectiveFiniteChart_symm]

/-- The true infinity chart domain excludes precisely the original zero point. -/
theorem projectiveInfinityChart_source :
    projectiveInfinityChart.source = {p : OnePoint ℂ | p ≠ (0 : ℂ)} := by
  ext p
  change projectiveReciprocal p ∈ projectiveFiniteChart.source ↔ p ≠ (0 : ℂ)
  rw [projectiveFiniteChart_source]
  cases p with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp
    · rw [projectiveReciprocal_coe hz]
      simp [hz]

/-- Both genuine original affine chart domains cover the entire compact point space. -/
theorem projectiveLine_chart_cover (p : OnePoint ℂ) :
    p ∈ projectiveFiniteChart.source ∨ p ∈ projectiveInfinityChart.source := by
  cases p with
  | infty =>
    right
    rw [projectiveInfinityChart_source]
    simp
  | coe z =>
    left
    rw [projectiveFiniteChart_source]
    exact ⟨z, rfl⟩

/-- The actual projectivization carries its original quotient topology from nonzero vectors. -/
instance projectiveLineTopology : TopologicalSpace (Projectivization ℂ (Fin 2 → ℂ)) := by
  unfold Projectivization
  infer_instance

/-- The actual nonzero vector section of the ordinary affine coordinate is continuous. -/
theorem continuous_projective_mk_left :
    Continuous (fun z : ℂ ↦ Projectivization.mk ℂ ![z, 1] (by simp)) := by
  have h : Continuous (fun z : ℂ ↦ (⟨![z, 1], by simp⟩ :
      {v : Fin 2 → ℂ // v ≠ 0})) := by
    apply Continuous.subtype_mk
    fun_prop
  exact continuous_quotient_mk'.comp h

/-- The second genuine nonzero vector section is continuous in the quotient topology. -/
theorem continuous_projective_mk_right :
    Continuous (fun z : ℂ ↦ Projectivization.mk ℂ ![1, z] (by simp)) := by
  have h : Continuous (fun z : ℂ ↦ (⟨![1, z], by simp⟩ :
      {v : Fin 2 → ℂ // v ≠ 0})) := by
    apply Continuous.subtype_mk
    fun_prop
  exact continuous_quotient_mk'.comp h

/-- Genuine scalar normalization identifies the two actual homogeneous coordinates. -/
theorem projective_mk_normalize {z : ℂ} (hz : z ≠ 0) :
    Projectivization.mk ℂ ![z, 1] (by simp) =
      Projectivization.mk ℂ ![1, z⁻¹] (by simp) := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [hz]

/-- The canonical algebraic equivalence is continuous for the original quotient topology. -/
theorem continuous_equivProjectivization :
    Continuous (OnePoint.equivProjectivization ℂ) := by
  rw [continuous_iff_continuousAt]
  intro p
  cases p with
  | coe z =>
    apply OnePoint.continuousAt_coe.mpr
    simpa only [Function.comp_def, OnePoint.equivProjectivization_apply_coe] using
      continuous_projective_mk_left.continuousAt (x := z)
  | infty =>
    apply OnePoint.continuousAt_infty'.mpr
    have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (coclosedCompact ℂ) (𝓝 0) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded (α := ℂ))
    have hlim := continuous_projective_mk_right.continuousAt.tendsto.comp hinv
    have hn : Tendsto (norm : ℂ → ℝ) (coclosedCompact ℂ) atTop := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (tendsto_norm_cobounded_atTop (E := ℂ))
    apply hlim.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with z hz
    exact (projective_mk_normalize (norm_pos_iff.mp hz)).symm

/-- The literal homogeneous-coordinate reader on actual nonzero vectors. -/
def projectiveHomogeneousReader (v : {v : Fin 2 → ℂ // v ≠ 0}) : OnePoint ℂ :=
  if v.1 1 = 0 then ∞ else (((v.1 1)⁻¹ * v.1 0 : ℂ) : OnePoint ℂ)

/-- Its continuity at infinity is produced by the opposite ratio and actual reciprocal. -/
theorem continuous_projectiveHomogeneousReader : Continuous projectiveHomogeneousReader := by
  rw [continuous_iff_continuousAt]
  intro v
  have h0 : ContinuousAt (fun w : {v : Fin 2 → ℂ // v ≠ 0} ↦ w.1 0) v :=
    ((continuous_apply 0).comp continuous_subtype_val).continuousAt
  have h1 : ContinuousAt (fun w : {v : Fin 2 → ℂ // v ≠ 0} ↦ w.1 1) v :=
    ((continuous_apply 1).comp continuous_subtype_val).continuousAt
  by_cases hv1 : v.1 1 = 0
  · have hv0 : v.1 0 ≠ 0 := by
      intro hv0
      apply v.2
      ext i
      fin_cases i <;> simp_all
    have hc : ContinuousAt (fun w : {v : Fin 2 → ℂ // v ≠ 0} ↦
        projectiveReciprocal (((w.1 0)⁻¹ * w.1 1 : ℂ) : OnePoint ℂ)) v :=
      continuous_projectiveReciprocal.continuousAt.comp
        (OnePoint.continuous_coe.continuousAt.comp ((h0.inv₀ hv0).mul h1))
    apply hc.congr
    filter_upwards [h0.preimage_mem_nhds (isOpen_ne.mem_nhds hv0)] with w hw0
    by_cases hw1 : w.1 1 = 0
    · simp [projectiveHomogeneousReader, hw1]
    · rw [projectiveReciprocal_coe (mul_ne_zero (inv_ne_zero hw0) hw1)]
      simp [projectiveHomogeneousReader, hw1, mul_comm]
  · have hc : ContinuousAt (fun w : {v : Fin 2 → ℂ // v ≠ 0} ↦
        (((w.1 1)⁻¹ * w.1 0 : ℂ) : OnePoint ℂ)) v :=
      OnePoint.continuous_coe.continuousAt.comp ((h1.inv₀ hv1).mul h0)
    apply hc.congr
    filter_upwards [h1.preimage_mem_nhds (isOpen_ne.mem_nhds hv1)] with w hw1
    change w.1 1 ≠ 0 at hw1
    simp [projectiveHomogeneousReader, hw1]

/-- Actual quotient continuity descends the genuine homogeneous reader. -/
theorem continuous_equivProjectivization_symm :
    Continuous (OnePoint.equivProjectivization ℂ).symm := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun v : {v : Fin 2 → ℂ // v ≠ 0} ↦
    (OnePoint.equivProjectivization ℂ).symm (Projectivization.mk ℂ v.1 v.2))
  apply continuous_projectiveHomogeneousReader.congr
  intro v
  exact (OnePoint.equivProjectivization_symm_apply_mk ℂ v.1 v.2).symm

/-- The canonical set equivalence is now a homeomorphism for the actual quotient topology. -/
def projectiveLineHomeomorph : OnePoint ℂ ≃ₜ Projectivization ℂ (Fin 2 → ℂ) where
  toEquiv := OnePoint.equivProjectivization ℂ
  continuous_toFun := continuous_equivProjectivization
  continuous_invFun := continuous_equivProjectivization_symm

/-- The two actual affine charts, indexed by their genuine coordinate choices. -/
def projectiveScalarChart (b : Bool) : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  if b then projectiveInfinityChart else projectiveFiniteChart

/-- All scalar coordinate targets are the original entire complex plane. -/
theorem projectiveScalarChart_target (b : Bool) : (projectiveScalarChart b).target = univ := by
  cases b <;> simp [projectiveScalarChart, projectiveFiniteChart_target,
    projectiveInfinityChart_target]

/-- Genuine reciprocal transitions on actual nonzero overlaps are holomorphic. -/
theorem differentiableOn_projectiveScalarChart_transition (i j : Bool) :
    DifferentiableOn ℂ ((projectiveScalarChart i).symm.trans (projectiveScalarChart j))
      ((projectiveScalarChart i).symm.trans (projectiveScalarChart j)).source := by
  cases i <;> cases j
  · apply differentiableOn_id.congr
    intro z hz
    change projectiveFiniteChart (projectiveFiniteChart.symm z) = z
    exact projectiveFiniteChart.right_inv hz.1
  · have hne : ∀ z ∈ (projectiveFiniteChart.symm.trans projectiveInfinityChart).source,
        z ≠ 0 := by
      intro z hz
      have hz' : projectiveFiniteChart.symm z ∈ projectiveInfinityChart.source := hz.2
      rw [projectiveFiniteChart_symm, projectiveInfinityChart_source] at hz'
      intro hzero
      exact hz' (congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) hzero)
    apply (differentiableOn_inv.mono (fun z hz ↦ hne z hz)).congr
    intro z hz
    change projectiveInfinityChart (projectiveFiniteChart.symm z) = z⁻¹
    rw [projectiveFiniteChart_symm, projectiveInfinityChart_coe (hne z hz)]
  · have hne : ∀ z ∈ (projectiveInfinityChart.symm.trans projectiveFiniteChart).source,
        z ≠ 0 := by
      intro z hz hzero
      subst z
      have hmem : projectiveInfinityChart.symm (0 : ℂ) ∈ projectiveFiniteChart.source := hz.2
      rw [projectiveInfinityChart_symm, projectiveReciprocal_zero,
        projectiveFiniteChart_source] at hmem
      simp at hmem
    apply (differentiableOn_inv.mono (fun z hz ↦ hne z hz)).congr
    intro z hz
    change projectiveFiniteChart (projectiveInfinityChart.symm z) = z⁻¹
    rw [projectiveInfinityChart_symm, projectiveReciprocal_coe (hne z hz),
      projectiveFiniteChart_coe]
  · apply differentiableOn_id.congr
    intro z hz
    change projectiveInfinityChart (projectiveInfinityChart.symm z) = z
    exact projectiveInfinityChart.right_inv hz.1

/-- These actual charts now live on the original projectivization quotient itself. -/
def projectiveQuotientScalarChart (b : Bool) :
    OpenPartialHomeomorph (Projectivization ℂ (Fin 2 → ℂ)) ℂ :=
  projectiveLineHomeomorph.symm.transOpenPartialHomeomorph (projectiveScalarChart b)

theorem projectiveQuotientScalarChart_source (b : Bool) :
    (projectiveQuotientScalarChart b).source =
      projectiveLineHomeomorph.symm ⁻¹' (projectiveScalarChart b).source := rfl

theorem projectiveQuotientScalarChart_target (b : Bool) :
    (projectiveQuotientScalarChart b).target = univ := projectiveScalarChart_target b

/-- Every actual original projective point is covered by one of the two genuine affine charts. -/
theorem projectiveQuotientScalarChart_cover (p : Projectivization ℂ (Fin 2 → ℂ)) :
    ∃ b : Bool, p ∈ (projectiveQuotientScalarChart b).source := by
  rcases projectiveLine_chart_cover (projectiveLineHomeomorph.symm p) with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- Actual quotient-chart holomorphic compatibility follows from genuine inverse cancellation. -/
theorem differentiableOn_projectiveQuotientScalarChart_transition (i j : Bool) :
    DifferentiableOn ℂ
      ((projectiveQuotientScalarChart i).symm.trans (projectiveQuotientScalarChart j))
      ((projectiveQuotientScalarChart i).symm.trans (projectiveQuotientScalarChart j)).source := by
  have hsource :
      ((projectiveQuotientScalarChart i).symm.trans (projectiveQuotientScalarChart j)).source ⊆
        ((projectiveScalarChart i).symm.trans (projectiveScalarChart j)).source := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have h : projectiveLineHomeomorph.symm
        (projectiveLineHomeomorph ((projectiveScalarChart i).symm z)) ∈
          (projectiveScalarChart j).source := hz.2
    change (projectiveScalarChart i).symm z ∈ (projectiveScalarChart j).source
    simpa only [Homeomorph.symm_apply_apply] using h
  apply ((differentiableOn_projectiveScalarChart_transition i j).mono hsource).congr
  intro z _
  change (projectiveScalarChart j) (projectiveLineHomeomorph.symm
    (projectiveLineHomeomorph ((projectiveScalarChart i).symm z))) =
      (projectiveScalarChart j) ((projectiveScalarChart i).symm z)
  rw [Homeomorph.symm_apply_apply]

/-- The genuine one-coordinate orthonormal equivalence to the original SGPT complex model. -/
def projectiveModelEquiv : ℂ ≃L[ℂ] ComplexModel 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr.toContinuousLinearEquiv

/-- The original quotient affine charts in SGPT's actual one-dimensional complex model. -/
def projectiveModelChart (b : Bool) :
    OpenPartialHomeomorph (Projectivization ℂ (Fin 2 → ℂ)) (ComplexModel 1) :=
  (projectiveQuotientScalarChart b).trans
    projectiveModelEquiv.toHomeomorph.toOpenPartialHomeomorph

theorem projectiveModelChart_source (b : Bool) :
    (projectiveModelChart b).source = (projectiveQuotientScalarChart b).source := by
  simp [projectiveModelChart]

/-- Actual inverse linear coordinates put each genuine model overlap inside the scalar overlap. -/
theorem projectiveModelChart_transition_source (i j : Bool) :
    ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source ⊆
      projectiveModelEquiv.symm ⁻¹'
        ((projectiveQuotientScalarChart i).symm.trans (projectiveQuotientScalarChart j)).source := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change projectiveModelEquiv.symm z ∈ (projectiveQuotientScalarChart i).target
    rw [projectiveQuotientScalarChart_target]
    exact mem_univ _
  · have h : (projectiveModelChart i).symm z ∈ (projectiveModelChart j).source := hz.2
    rw [projectiveModelChart_source] at h
    change (projectiveQuotientScalarChart i).symm (projectiveModelEquiv.symm z) ∈
      (projectiveQuotientScalarChart j).source
    exact h

/-- Actual linear coordinate change transports the genuine holomorphic scalar transitions. -/
theorem differentiableOn_projectiveModelChart_transition (i j : Bool) :
    DifferentiableOn ℂ ((projectiveModelChart i).symm.trans (projectiveModelChart j))
      ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source := by
  have hi : DifferentiableOn ℂ (fun z : ComplexModel 1 ↦
      ((projectiveQuotientScalarChart i).symm.trans (projectiveQuotientScalarChart j))
        (projectiveModelEquiv.symm z))
      ((projectiveModelChart i).symm.trans (projectiveModelChart j)).source :=
    (differentiableOn_projectiveQuotientScalarChart_transition i j).comp
      projectiveModelEquiv.symm.toContinuousLinearMap.differentiable.differentiableOn
      (fun z hz ↦ projectiveModelChart_transition_source i j hz)
  apply (projectiveModelEquiv.toContinuousLinearMap.differentiable.differentiableOn.comp
    hi (fun _ _ ↦ mem_univ _)).congr
  intro z _
  rfl

/-- A genuine holomorphic atlas on the original quotient projective line, with no compatibility input. -/
def projectiveLineAtlas : SGPT.PSH.VariableComplexAtlas (Projectivization ℂ (Fin 2 → ℂ)) where
  Index := Bool
  dimension := fun _ ↦ 1
  chart := projectiveModelChart
  cover := fun p ↦ by
    obtain ⟨b, hb⟩ := projectiveQuotientScalarChart_cover p
    exact ⟨b, by rwa [projectiveModelChart_source]⟩
  holomorphic := differentiableOn_projectiveModelChart_transition

end SGPT.Toric
