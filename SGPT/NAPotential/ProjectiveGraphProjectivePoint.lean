import SGPT.NAPotential.ProjectiveGraphPointSquare
import SGPT.NAPotential.ProjectiveGraphLiteralDifferential

/-!
# Native projective point coordinates in the original projective manifold

Blueprint: `projective-graph-projective-point.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphNativeReadback ProjectiveGraphRegularEvaluation
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual identity closed embedding of native projective space. -/
def identityEmbedding (N : ℕ) : ClosedProjectiveEmbedding (polynomialProjStructureMap ℂ N) where
  ambientDimension := N
  map := 𝟙 _
  closedImmersion := inferInstance
  over_base := Category.id_comp _

section Differential
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsProper f]
local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance pointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Original projective-point tangent injection in the SAME original manifold charts. -/
theorem projectivePoint_mfderiv_injective (p : SchemeComplexPoint f) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension)
      (projectivePoint f E n) p) := by
  have hD : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension)
      (projectivePoint f E n) p := by
    have h : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞
        (projectivePoint f E n) p := by
      let i := frameIndex f E p
      have hi := mem_coordOpen_frameIndex f E p
      have hF : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, Fin (E.ambientDimension + 1) → ℂ) ∞
          (homCoords f E n i) p := by
        rw [contMDiffAt_pi_space]
        intro k
        exact contMDiffAt_of_eventually_mdifferentiableAt
          (schemeOpenRegularFunction_holomorphicAt f n E _ (ratio E i k) p hi)
      apply ComplexProjectiveSpace.contMDiffAt_of_lift hF (homCoords_ne_zero f E n i hi)
      filter_upwards [(isOpen_coordOpen_points f E i).mem_nhds hi] with q hq
      exact ⟨homCoords_ne_zero f E n i hq, projectivePoint_eq f E n i hq⟩
    exact h.mdifferentiableAt (by simp)
  rw [hD.mfderiv]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, fderivWithin_univ]
  exact (isHolomorphicEmbedding_projectivePoint f E n).immersion p
    (chartIndex (projectivePoint f E n p)) (mem_affineChart_chartIndex _)
end Differential

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
