import SGPT.Toric.ProjectiveToricReverse

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- Every actual original theta potential is the true analytic filling of
its own torus values, with compact bounds and uniqueness produced. -/
theorem projectiveThetaPSH_eq_analyticExtension
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    u = analyticExtension projectiveToricBoundary u := by
  obtain ⟨C, hC⟩ := exists_upper_bound_projectiveThetaPSH hu
  have hb : LocallyBoundedAboveOff projectiveToricBoundary u :=
    fun _ ↦ ⟨univ, Filter.univ_mem, C, fun p _ _ ↦ hC p⟩
  exact (hu.isThetaPSHOn projectiveToricBoundaryᶜ).analyticExtension_unique
    hasAnalyticChartEquations_projectiveToricBoundary interior_projectiveToricBoundary hb hu
    (fun _ _ ↦ rfl)

/-- Genuine finite-additive comparisons of actual torus values extend
pointwise to both original boundary poles. -/
theorem projectiveThetaPSH_le_add_of_le_off
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (C : ℝ) (h : ∀ p ∉ projectiveToricBoundary, u p ≤ v p + (C : EReal)) :
    ∀ p, u p ≤ v p + (C : EReal) := by
  have hfill : analyticExtension projectiveToricBoundary u ≤
      analyticExtension projectiveToricBoundary (fun p ↦ v p + (C : EReal)) := by
    apply uscRegularization_mono
    intro p
    by_cases hp : p ∈ projectiveToricBoundary
    · simp [hp]
    · simpa only [if_neg hp] using h p hp
  intro p
  calc
    u p = analyticExtension projectiveToricBoundary u p :=
      congrFun (projectiveThetaPSH_eq_analyticExtension hu) p
    _ ≤ analyticExtension projectiveToricBoundary (fun q ↦ v q + (C : EReal)) p := hfill p
    _ = analyticExtension projectiveToricBoundary v p + (C : EReal) :=
      analyticExtension_add_coe_apply projectiveToricBoundary v continuous_const.continuousAt
    _ = v p + (C : EReal) := by rw [← projectiveThetaPSH_eq_analyticExtension hv]

/-- The same original finite additive constant compares global invariant
potentials exactly when it compares their literal corrected descents. -/
theorem projectiveToricCorrectedDescent_le_add_iff
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) (C : ℝ) :
    (∀ p, u p ≤ v p + (C : EReal)) ↔
      ∀ x, projectiveToricCorrectedDescent u x ≤ projectiveToricCorrectedDescent v x + (C : EReal) := by
  constructor
  · intro h x
    let p := OnePoint.equivProjectivization ℂ ((expCoordinates x 0 : ℂ) : OnePoint ℂ)
    change u p + (projectiveLineLogPartition (x 0) : EReal) ≤
      (v p + (projectiveLineLogPartition (x 0) : EReal)) + (C : EReal)
    exact (add_le_add (h p) (le_refl (projectiveLineLogPartition (x 0) : EReal))).trans_eq
      (add_right_comm (v p) (C : EReal) (projectiveLineLogPartition (x 0) : EReal))
  · intro h
    apply projectiveThetaPSH_le_add_of_le_off hu hv C
    intro p hp
    let e := projectiveModelChart false
    let z := e p
    have hz : z ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
    have hs : p ∈ e.source := projectiveToricBoundary_compl_subset_finite_source hp
    have htu := projectiveToricCorrectedDescent_tropicalPullback hiu hz
    have htv := projectiveToricCorrectedDescent_tropicalPullback hiv hz
    change projectiveToricCorrectedDescent u (tropicalization z) =
      u (e.symm z) + (projectiveFSPotential z : EReal) at htu
    change projectiveToricCorrectedDescent v (tropicalization z) =
      v (e.symm z) + (projectiveFSPotential z : EReal) at htv
    rw [show e.symm z = p from e.left_inv hs] at htu htv
    have hcost := h (tropicalization z)
    rw [htu, htv] at hcost
    have hshift := add_le_add hcost
      (le_refl ((-projectiveFSPotential z : ℝ) : EReal))
    have huCancel : (u p + (projectiveFSPotential z : EReal)) +
        ((-projectiveFSPotential z : ℝ) : EReal) = u p := by
      simpa only [zero_sub, EReal.coe_zero, add_zero] using
        corrected_add_sub (u p) (projectiveFSPotential z) 0
    have hvCancel : ((v p + (projectiveFSPotential z : EReal)) + (C : EReal)) +
        ((-projectiveFSPotential z : ℝ) : EReal) = v p + (C : EReal) := by
      rw [add_right_comm (v p) (projectiveFSPotential z : EReal) (C : EReal)]
      simpa only [zero_sub, EReal.coe_zero, add_zero] using
        corrected_add_sub (v p + (C : EReal)) (projectiveFSPotential z) 0
    rwa [huCancel, hvCancel] at hshift

/-- Actual whole-space pointwise order matches original corrected convex order. -/
theorem projectiveToricCorrectedDescent_le_iff
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    u ≤ v ↔ projectiveToricCorrectedDescent u ≤ projectiveToricCorrectedDescent v := by
  change (∀ p, u p ≤ v p) ↔
    ∀ x, projectiveToricCorrectedDescent u x ≤ projectiveToricCorrectedDescent v x
  simpa only [EReal.coe_zero, add_zero] using
    projectiveToricCorrectedDescent_le_add_iff hu hv hiu hiv 0

/-- Original global singularity order is exactly the actual convex
descent's additive comparison, with the same real witness. -/
theorem projectiveToricCorrectedDescent_singularityLE_iff
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    SGPT.PSH.SingularityLE u v ↔
      SGPT.PSH.SingularityLE (projectiveToricCorrectedDescent u) (projectiveToricCorrectedDescent v) := by
  rw [SGPT.PSH.singularityLE_iff_exists_real, SGPT.PSH.singularityLE_iff_exists_real]
  exact exists_congr fun C ↦ projectiveToricCorrectedDescent_le_add_iff hu hv hiu hiv C

/-- The literal original reversed-order Legendre transform in the true Euclidean pairing. -/
def projectiveToricLegendre
    (u : Projectivization ℂ (Fin 2 → ℂ) → EReal) : EuclideanSpace ℝ (Fin 1) → EReal :=
  SGPT.Convex.conjugate (innerₗ (EuclideanSpace ℝ (Fin 1)))
    (projectiveToricCorrectedDescent u)

/-- Actual source support growth closes the original convex descent, so its
genuine reversed Legendre transform recovers every original value. -/
theorem conjugate_projectiveToricLegendre
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    SGPT.Convex.conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip
      (projectiveToricLegendre u) = projectiveToricCorrectedDescent u := by
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  exact (SGPT.Convex.biconjugate_eq_convexClosure_of_isContPerfPair _ hf.1.1).trans
    (SGPT.Convex.convexClosure_eq_self_of_isClosedConvex
      (SGPT.Convex.isClosedConvex_of_mem_growthClass _ isCompact_projectiveMomentInterval
        nonempty_projectiveMomentInterval hf))

/-- The actual original Legendre functions reverse the exact pointwise convex order. -/
theorem projectiveToricCorrectedDescent_le_iff_legendre
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    projectiveToricCorrectedDescent u ≤ projectiveToricCorrectedDescent v ↔
      projectiveToricLegendre v ≤ projectiveToricLegendre u := by
  constructor
  · intro h y
    exact SGPT.Convex.conjugate_antitone (innerₗ (EuclideanSpace ℝ (Fin 1))) h y
  · intro h x
    have hh := SGPT.Convex.conjugate_antitone
      (innerₗ (EuclideanSpace ℝ (Fin 1))).flip h x
    rwa [conjugate_projectiveToricLegendre hu hiu,
      conjugate_projectiveToricLegendre hv hiv] at hh

/-- The original additive singularity comparison reverses under the literal
Legendre functions, with no lost infinite values. -/
theorem projectiveToricCorrectedDescent_singularityLE_iff_legendre
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    SGPT.PSH.SingularityLE (projectiveToricCorrectedDescent u) (projectiveToricCorrectedDescent v) ↔
      SGPT.PSH.SingularityLE (projectiveToricLegendre v) (projectiveToricLegendre u) := by
  constructor
  · exact SGPT.Convex.conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin 1)))
  · intro h
    have hh := SGPT.Convex.conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin 1))).flip h
    rwa [conjugate_projectiveToricLegendre hu hiu,
      conjugate_projectiveToricLegendre hv hiv] at hh

/-- All three original pointwise comparisons agree on the actual projective-line model. -/
theorem projectiveThetaPSH_le_iff_legendre
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    u ≤ v ↔ projectiveToricLegendre v ≤ projectiveToricLegendre u :=
  (projectiveToricCorrectedDescent_le_iff hu hv hiu hiv).trans
    (projectiveToricCorrectedDescent_le_iff_legendre hu hv hiu hiv)

/-- All three original singularity preorders agree on the actual projective-line model. -/
theorem projectiveThetaPSH_singularityLE_iff_legendre
    {u v : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v) :
    SGPT.PSH.SingularityLE u v ↔
      SGPT.PSH.SingularityLE (projectiveToricLegendre v) (projectiveToricLegendre u) :=
  (projectiveToricCorrectedDescent_singularityLE_iff hu hv hiu hiv).trans
    (projectiveToricCorrectedDescent_singularityLE_iff_legendre hu hv hiu hiv)

end SGPT.Toric
