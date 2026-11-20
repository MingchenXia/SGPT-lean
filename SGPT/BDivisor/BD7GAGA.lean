import SGPT.BDivisor.BD7Cofinal
import SGPT.BDivisor.BD7Morphisms
import SGPT.BDivisor.GMMorphism

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov
open scoped Manifold ContDiff
local instance gagaPointTopology {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f

local instance gagaPointCharts {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n

/-- The GAGA theorem for holomorphic maps of smooth projective schemes supplies the
morphism algebraization used by the blow-up model system. -/
theorem gagaMorphismsSmooth : GAGAMorphismsSmooth := by
  intro V W gV gW n m _ _ EV EW φ hφ
  have := EV.isSeparated
  have := EV.quasiCompact
  have := EW.isSeparated
  have := EW.quasiCompact
  obtain ⟨F, hF, -⟩ :=
    GM.exists_unique_morphism_of_holomorphic_smooth gV EV n gW EW m φ
      (hφ.mdifferentiable (by simp))
  exact ⟨F, hF⟩

section Transition

universe u

variable {n : ℕ}
  {V : Type u} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V] [IsComplexManifold n V]
  {V' : Type u} [TopologicalSpace V'] [ChartedSpace (ComplexModel n) V'] [IsComplexManifold n V']
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Y' : Type u} [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']

/-- A commuting square of holomorphic maps intertwines the two class pullbacks.
For algebraized models, the square comes from `exists_algebraic_domination` with GAGA. -/
theorem classPullback_transition_square
    (e : V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (e' : V' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y')
    {q : V' → V} {k : Y' → Y}
    (hq : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q)
    (hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ k)
    (h : ∀ z, e (q z) = k (e' z)) (α : RealBottChern n Y) :
    classPullback hq (classPullback e.contMDiff α) =
      classPullback e'.contMDiff (classPullback hk α) := by
  rw [← classPullback_comp e.contMDiff hq, ← classPullback_comp hk e'.contMDiff]
  exact classPullback_congr (funext h) _ _ α

end Transition

end SGPT.BDivisor.BD7
