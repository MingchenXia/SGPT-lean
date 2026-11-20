import SGPT.Toric.ProjectiveToricDescent
import SGPT.Toric.ProjectiveLineLogSingularity

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical

/-- The actual two-point complement of the original projective torus. -/
def projectiveToricBoundary : Set (Projectivization ℂ (Fin 2 → ℂ)) :=
  {p | p = projectiveOrigin ∨ p = projectiveInfinity}

/-- Actual quotient-chart inverses are the genuine finite and reciprocal point sections. -/
theorem projectiveModelChart_symm_onePoint (b : Bool) (z : ComplexModel 1) :
    (projectiveModelChart b).symm z = projectiveLineHomeomorph
      (if b then projectiveReciprocal ((z 0 : ℂ) : OnePoint ℂ) else ((z 0 : ℂ) : OnePoint ℂ)) := by
  cases b
  · change projectiveLineHomeomorph (projectiveFiniteChart.symm (projectiveModelEquiv.symm z)) = _
    rw [projectiveFiniteChart_symm, projectiveModelEquiv_symm_apply]
    rfl
  · change projectiveLineHomeomorph (projectiveInfinityChart.symm (projectiveModelEquiv.symm z)) = _
    rw [projectiveInfinityChart_symm, projectiveModelEquiv_symm_apply]
    rfl

/-- Every actual boundary chart has exactly the original coordinate-zero locus. -/
theorem projectiveToricBoundary_chart_iff (b : Bool) (z : ComplexModel 1) :
    (projectiveModelChart b).symm z ∈ projectiveToricBoundary ↔ z 0 = 0 := by
  simp only [projectiveToricBoundary, mem_ofPred_eq, projectiveOrigin, projectiveInfinity,
    projectiveModelChart_symm_onePoint, PiLp.zero_apply, Bool.false_eq_true, ↓reduceIte,
    projectiveReciprocal_zero, projectiveLineHomeomorph.injective.eq_iff]
  cases b
  · simp
  · by_cases hz : z 0 = 0
    · simp [hz]
    · rw [projectiveReciprocal_coe hz]
      simp [hz]

/-- The genuine two-point boundary has actual finite holomorphic equations, not an analytic-set premise. -/
theorem hasAnalyticChartEquations_projectiveToricBoundary :
    projectiveLineAtlas.HasAnalyticChartEquations projectiveToricBoundary := by
  change ∀ (b : Bool) (z : ComplexModel 1), z ∈ (projectiveModelChart b).target →
    ∃ W : Set (ComplexModel 1), IsOpen W ∧ z ∈ W ∧
      W ⊆ (projectiveModelChart b).target ∧ ∃ (N : ℕ) (g : Fin N → ComplexModel 1 → ℂ),
        (∀ j, DifferentiableOn ℂ (g j) W) ∧
          ∀ y ∈ W, (projectiveModelChart b).symm y ∈ projectiveToricBoundary ↔ ∀ j, g j y = 0
  intro b z _
  refine ⟨univ, isOpen_univ, mem_univ _, ?_, 1, (fun _ y ↦ y 0), ?_, ?_⟩
  · intro y _
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  · intro _
    change DifferentiableOn ℂ (fun y : ComplexModel 1 ↦ y 0) univ
    fun_prop
  · intro y _
    simpa only [Fin.forall_fin_one] using projectiveToricBoundary_chart_iff b y

/-- Every original projective neighborhood genuinely meets the torus. -/
theorem interior_projectiveToricBoundary : interior projectiveToricBoundary = ∅ := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
    change Bool at b
    let e := projectiveModelChart b
    let D := e.target ∩ e.symm ⁻¹' interior projectiveToricBoundary
    have hD : IsOpen D := e.isOpen_inter_preimage_symm isOpen_interior
    have hx : e p ∈ D := ⟨e.mapsTo hb, by
      change e.symm (e p) ∈ interior projectiveToricBoundary
      rwa [e.left_inv hb]⟩
    obtain ⟨w, hw, hwD⟩ := (projectiveCoordinate_frequently_ne_zero (e p)).and_eventually
      (hD.mem_nhds hx) |>.exists
    have hz := (projectiveToricBoundary_chart_iff b w).mp (interior_subset hwD.2)
    apply hw
    rw [projectiveModelEquiv_symm_apply, hz]
  · intro h
    exact False.elim h

/-- Closedness follows from the produced original holomorphic equations. -/
theorem isClosed_projectiveToricBoundary : IsClosed projectiveToricBoundary :=
  hasAnalyticChartEquations_projectiveToricBoundary.isClosed projectiveLineAtlas

/-- The actual projective torus lies in the genuine finite chart. -/
theorem projectiveToricBoundary_compl_subset_finite_source :
    projectiveToricBoundaryᶜ ⊆ (projectiveModelChart false).source := by
  intro p hp
  obtain ⟨q, rfl⟩ := projectiveLineHomeomorph.surjective p
  cases q with
  | infty =>
    exfalso
    apply hp
    change _ = projectiveOrigin ∨ _ = projectiveInfinity
    right
    simp [projectiveInfinity, projectiveModelChart_symm_onePoint]
  | coe z =>
    rw [projectiveModelChart_source, projectiveQuotientScalarChart_source]
    change projectiveLineHomeomorph.symm (projectiveLineHomeomorph (z : OnePoint ℂ)) ∈
      projectiveFiniteChart.source
    rw [projectiveLineHomeomorph.symm_apply_apply, projectiveFiniteChart_source]
    exact ⟨z, rfl⟩

/-- The original open-torus coordinate condition is exactly the actual off-boundary condition. -/
theorem projectiveToricBoundary_chart_off_iff (b : Bool) (z : ComplexModel 1) :
    (projectiveModelChart b).symm z ∉ projectiveToricBoundary ↔ z ∈ complexTorus 1 := by
  rw [projectiveToricBoundary_chart_iff]
  simp only [complexTorus, mem_ofPred_eq, Fin.forall_fin_one]

/-- Every original off-boundary point has its true nonzero finite-chart coordinate. -/
theorem projectiveFiniteCoordinate_mem_torus_of_off_boundary
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    projectiveModelChart false p ∈ complexTorus 1 := by
  apply (projectiveToricBoundary_chart_off_iff false _).mp
  rwa [(projectiveModelChart false).left_inv
    (projectiveToricBoundary_compl_subset_finite_source hp)]

end SGPT.Toric
