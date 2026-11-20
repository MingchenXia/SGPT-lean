import SGPT.Toric.ProjectiveToricNewtonBody
import SGPT.Toric.Conjugacy

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- Actual properness and the literal off-body top rule give the nonempty
compact convex closure of the genuine finite domain inside the same body. -/
theorem convexNewtonBody_properties_of_closedProperOnBody
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsCompact P) {G : E → EReal}
    (hG : G ∈ ClosedProperOnBody P) :
    (convexNewtonBody G).Nonempty ∧ IsCompact (convexNewtonBody G) ∧
      Convex ℝ (convexNewtonBody G) ∧ convexNewtonBody G ⊆ P := by
  have hdomain : effectiveDomain G ⊆ P := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hG.2.2 m hmP)
  have hbody : convexNewtonBody G ⊆ P := closure_minimal hdomain hP.isClosed
  obtain ⟨m, hm⟩ := hG.1.2.1
  exact ⟨⟨m, subset_closure hm⟩, hP.of_isClosed_subset isClosed_closure hbody,
    (convex_effectiveDomain hG.1.1).closure, hbody⟩

/-- Thin original Newton readback of the completed whole raw-subgradient
image theorem; nondifferentiable subgradient intervals remain present. -/
theorem convexNewtonBody_conjugate_eq_closure_rawSubgradientImage
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    convexNewtonBody (conjugate B f) = closure (rawSubgradientImage B f) :=
  (closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf hlsc).symm

/-- The actual original source potential internally produces every Newton
body property, without an assumed convexity or growth certificate. -/
theorem projectiveToricNewtonBody_properties
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (projectiveToricNewtonBody u).Nonempty ∧ IsCompact (projectiveToricNewtonBody u) ∧
      Convex ℝ (projectiveToricNewtonBody u) ∧
      projectiveToricNewtonBody u ⊆ projectiveMomentInterval := by
  exact convexNewtonBody_properties_of_closedProperOnBody isCompact_projectiveMomentInterval
    (conjugate_mem_closedProperOnBody_of_mem_growthClass _
      isCompact_projectiveMomentInterval convex_projectiveMomentInterval
      (projectiveToricCorrectedDescent_mem_growthClass hu hi))

/-- Literal source `∇F` is the multivalued supporting-subgradient union,
whose closure is the actual original projective Newton body. -/
theorem projectiveToricNewtonBody_eq_closure_rawSubgradientImage
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNewtonBody u = closure
      (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin 1)))
        (projectiveToricCorrectedDescent u)) := by
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  exact convexNewtonBody_conjugate_eq_closure_rawSubgradientImage _ hf.1
    (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_mem_growthClass _
      isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval hf))

end SGPT.Toric
