import SGPT.NAPotential.ProjectiveGraphProjectivePoint

/-! The actual original projective-point map is holomorphic in every smooth dimension.
Blueprint: `projective-graph-projective-point.tex`. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHolomorphic

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  (n : ℕ) [SmoothOfRelativeDimension n f] [IsProper f]
local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance pointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The actual original projective-point map is holomorphic, including dimension zero. -/
theorem projectivePoint_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞ (projectivePoint f E n) := by
  intro p
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

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHolomorphic
