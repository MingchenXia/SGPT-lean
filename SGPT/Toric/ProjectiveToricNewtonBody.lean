import SGPT.Toric.ProjectiveLogLog
import SGPT.Toric.LogLogAlexandrovMass
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- The literal closure of the entire finite Legendre domain, independently
defined before any body computation. -/
def convexNewtonBody {E : Type*} [TopologicalSpace E] (G : E → EReal) : Set E :=
  closure (effectiveDomain G)

/-- The actual original finite-facet entropy has precisely its closed facet
region as its Newton set, including an empty region. -/
theorem convexNewtonBody_facetEntropy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (L : ι → E →L[ℝ] ℝ) (a : ι → ℝ) :
    convexNewtonBody (facetEntropy L a) = facetRegion L a := by
  rw [convexNewtonBody, effectiveDomain_facetEntropy]
  exact (isClosed_facetRegion L a).closure_eq

/-- The source Newton body uses the actual original projective Legendre
function, without replacing its finite domain by a prescribed interval. -/
def projectiveToricNewtonBody
    (u : Projectivization ℂ (Fin 2 → ℂ) → EReal) : Set (EuclideanSpace ℝ (Fin 1)) :=
  convexNewtonBody (projectiveToricLegendre u)

/-- The completed attained entropy conjugate and genuine biconjugation give
the actual reverse conjugate of the original reference partition. -/
theorem conjugate_projectiveLineLogPartition (m : ℝ) :
    conjugate scalarPairing (fun x : ℝ ↦ (projectiveLineLogPartition x : EReal)) m =
      projectiveLineEntropy m := by
  have hpartition : conjugate scalarPairing projectiveLineEntropy =
      fun x : ℝ ↦ (projectiveLineLogPartition x : EReal) :=
    funext conjugate_projectiveLineEntropy
  have hb := biconjugate_eq_convexClosure_of_isContPerfPair scalarPairing
    (isConvex_of_isClosedConvex isClosedConvex_projectiveLineEntropy)
  rw [hpartition, scalarPairing_flip,
    convexClosure_eq_self_of_isClosedConvex isClosedConvex_projectiveLineEntropy] at hb
  exact congrFun hb m

/-- Genuine singleton-coordinate surjectivity identifies the entire original
Euclidean Legendre transform of the reference zero potential. -/
theorem projectiveToricLegendre_zero (m : EuclideanSpace ℝ (Fin 1)) :
    projectiveToricLegendre (fun _ ↦ 0) m = projectiveLineEntropy (m 0) := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) := by
    intro r
    exact ⟨WithLp.toLp 2 (fun _ : Fin 1 ↦ r), rfl⟩
  calc
    _ = ⨆ x : EuclideanSpace ℝ (Fin 1),
        (↑(x 0 * m 0) : EReal) - (projectiveLineLogPartition (x 0) : EReal) := by
      unfold projectiveToricLegendre conjugate projectiveToricCorrectedDescent
        projectiveToricDescent
      congr 1
      funext x
      simp [innerₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        mul_comm]
    _ = conjugate scalarPairing
        (fun x : ℝ ↦ (projectiveLineLogPartition x : EReal)) (m 0) := by
      simpa only [conjugate, scalarPairing, LinearMap.mul_apply'] using
        hsurj.iSup_comp (fun r : ℝ ↦
          (↑(r * m 0) : EReal) - (projectiveLineLogPartition r : EReal))
    _ = projectiveLineEntropy (m 0) := conjugate_projectiveLineLogPartition (m 0)

/-- The original reference Newton body is the genuine original moment interval. -/
theorem projectiveToricNewtonBody_zero :
    projectiveToricNewtonBody (fun _ ↦ 0) = projectiveMomentInterval := by
  have hdomain : effectiveDomain (projectiveToricLegendre (fun _ ↦ 0)) =
      projectiveMomentInterval := by
    ext m
    change projectiveToricLegendre (fun _ ↦ 0) m < ⊤ ↔ 0 ≤ m 0 ∧ m 0 ≤ 1
    rw [projectiveToricLegendre_zero]
    have h := effectiveDomain_facetEntropy projectiveLineFacets projectiveLineOffsets
    rw [projectiveLineFacetRegion_eq] at h
    change m 0 ∈ effectiveDomain (facetEntropy projectiveLineFacets projectiveLineOffsets) ↔ _
    rw [h]
    rfl
  rw [projectiveToricNewtonBody, convexNewtonBody, hdomain]
  exact isCompact_projectiveMomentInterval.isClosed.closure_eq

/-- The checked entire section conjugate is a true singleton indicator,
whose finite domain is already closed in the original Euclidean space. -/
theorem projectiveToricNewtonBody_logSingularity :
    projectiveToricNewtonBody projectiveLogSingularity = {projectiveMomentOne} := by
  rw [projectiveToricNewtonBody, convexNewtonBody,
    projectiveToricLegendre_logSingularity, effectiveDomain_indicator]
  exact isClosed_singleton.closure_eq

/-- The actual log-log Legendre domain includes one and excludes zero in the
literal original singleton Euclidean coordinate. -/
theorem effectiveDomain_projectiveToricLegendre_logLog :
    effectiveDomain (projectiveToricLegendre projectiveLogLogPotential) =
      {m : EuclideanSpace ℝ (Fin 1) | 0 < m 0 ∧ m 0 ≤ 1} := by
  ext m
  change projectiveToricLegendre projectiveLogLogPotential m < ⊤ ↔
    0 < m 0 ∧ m 0 ≤ 1
  rw [projectiveLogLogPotential_legendre, ← logLogConjugate_eq_source,
    ← conjugate_scalar_logLogProfile]
  change m 0 ∈ effectiveDomain
    (conjugate scalarPairing (fun x : ℝ ↦ (logLogProfile x : EReal))) ↔ _
  rw [effectiveDomain_conjugate_scalar_logLogProfile]
  rfl

/-- The true closure of the actual half-open domain is the original closed
moment interval; no closed-domain hypothesis fills in zero prematurely. -/
theorem projectiveToricNewtonBody_logLog :
    projectiveToricNewtonBody projectiveLogLogPotential = projectiveMomentInterval := by
  rw [projectiveToricNewtonBody, convexNewtonBody,
    effectiveDomain_projectiveToricLegendre_logLog]
  let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun t ↦ WithLp.toLp 2 (fun _ ↦ t)
  have hf : Continuous f := by fun_prop
  have himage : f '' Ioc (0 : ℝ) 1 =
      {m : EuclideanSpace ℝ (Fin 1) | 0 < m 0 ∧ m 0 ≤ 1} := by
    ext m
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hm
      refine ⟨m 0, hm, ?_⟩
      ext i
      rw [Fin.eq_zero i]
  apply le_antisymm
  · exact closure_minimal (fun _ hm ↦ ⟨hm.1.le, hm.2⟩)
      isCompact_projectiveMomentInterval.isClosed
  · intro m hm
    have hcl := image_closure_subset_closure_image (s := Ioc (0 : ℝ) 1) hf
    rw [himage] at hcl
    apply hcl
    refine ⟨m 0, ?_, ?_⟩
    · rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
      exact hm
    · ext i
      rw [Fin.eq_zero i]

/-- The original zero moment lies in P and is genuinely absent from the
finite log-log conjugate domain. -/
theorem effectiveDomain_logLog_ssubsetMomentInterval :
    effectiveDomain (projectiveToricLegendre projectiveLogLogPotential) ⊂
      projectiveMomentInterval := by
  rw [effectiveDomain_projectiveToricLegendre_logLog]
  apply ssubset_iff_subset_ne.mpr
  refine ⟨fun _ hm ↦ ⟨hm.1.le, hm.2⟩, ?_⟩
  intro heq
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ projectiveMomentInterval := by
    simp [projectiveMomentInterval]
  rw [← heq] at hzero
  simp at hzero

/-- Every displayed original Newton-body example clause, with the genuine
finite-domain/closure distinction retained. -/
theorem original_projective_toric_newton_example :
    projectiveToricNewtonBody (fun _ ↦ 0) = projectiveMomentInterval ∧
    projectiveToricNewtonBody projectiveLogSingularity = {projectiveMomentOne} ∧
    projectiveToricNewtonBody projectiveLogLogPotential = projectiveMomentInterval ∧
    effectiveDomain (projectiveToricLegendre projectiveLogLogPotential) ⊂
      projectiveMomentInterval :=
  ⟨projectiveToricNewtonBody_zero, projectiveToricNewtonBody_logSingularity,
    projectiveToricNewtonBody_logLog, effectiveDomain_logLog_ssubsetMomentInterval⟩

end SGPT.Toric
