import SGPT.NAPotential.ProjectiveGraphLiteralImmersion

/-!
# The SAME literal original graph-open immersion has injective differential

No native graph chart or derivative certificate is supplied: the actual map is
manufactured from the literal original normalized Segre algebra generators.
Blueprint: `projective-graph-affine-immersion.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphLiteralDifferential

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] {s : ℕ} (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)
  (n : ℕ) [SmoothOfRelativeDimension n
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :=
  schemeAnalyticPointTopology _
local instance targetTopology : TopologicalSpace (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticPointTopology _
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :=
  schemeAnalyticTNChartedSpace _ n
local instance targetCharts : ChartedSpace (ComplexModel (segreDim E.ambientDimension s)) (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticTNChartedSpace _ _

/-- Actual literal original graph-open map is holomorphic in the original TN charts. -/
theorem literalOpenProjectiveMap_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) ∞
      (schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
        (literalOpenProjectiveMap_overBase E j hU b W)) :=
  NativeSchemeImmersion.contMDiff_pointMap _ _ _ _ n _ ∞

/-- **Actual literal original graph-open differential is injective** in the original TN charts. -/
theorem literalOpenProjectiveMap_mfderiv_injective
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s))
      (schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
        (literalOpenProjectiveMap_overBase E j hU b W)) p) :=
  NativeSchemeImmersion.immersion_mfderiv_injective _ _ _ _ n _ p

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphLiteralDifferential
