import SGPT.NAPotential.ProjectiveGraphProjectiveReadback
import SGPT.NAPotential.ProjectiveGraphProjectiveHolomorphic

/-!
# The SAME original product graph map has injective differential

The actual native immersion is identified with the original Segre image in the
original projective manifold. Native tangent injection then transfers through
actual holomorphic chain rules, with no derivative certificate supplied.
Blueprint: `projective-graph-projective-point.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductDifferential

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open ProjectiveGraphCentredChart ProjectiveGraphNativeReadback ProjectiveGraphPointSquare
open ProjectiveGraphProjectiveReadback ProjectiveGraphProjectivePoint ProjectiveGraphProjectiveHolomorphic
open ProjectiveGraphLiteralDifferential ProjectiveGraphSegre
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)

/-- **Exact equality in the ORIGINAL projective manifold** between the same native immersion and original product graph Segre image. -/
theorem originalSegre_native_square
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    projectivePoint (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))
      (identityEmbedding (segreDim E.ambientDimension s)) (segreDim E.ambientDimension s)
        (schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
          (literalOpenProjectiveMap_overBase E j hU b W) p) =
      segreAmbientMap (m := m) E
        (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p) := by
  have hpivot : ProjectiveGraphPointEvaluation.graphPointEval (f := f)
      (coordOpen E j) (isAffineOpen_coordOpen E j) b W p
        (literalCoordinates E j hU b (coordSegrePivot E j s)) ≠ 0 := by
    rw [literalCoordinates_pivot, map_one]
    exact one_ne_zero
  rw [literalOpenProjectiveMap_point, nativeVectorPoint_projectivePoint _ _ _
    (evaluatedCoordinates_ne_zero E j b W p) hpivot]
  exact (segreAmbientMap_openGraphMap_eq (m := m) E j b W p).symm

variable [SmoothOfRelativeDimension (m + 1)
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)]
  [IsSeparated (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)]
  [QuasiCompact (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) := schemeAnalyticPointTopology _
local instance sourceCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) := schemeAnalyticTNChartedSpace _ _
local instance sourceManifold : IsComplexManifold (m + 1) (SchemeComplexPoint
    (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) := schemeAnalyticTN_isComplexManifold _ _
local instance nativeTopology : TopologicalSpace (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticPointTopology _
local instance nativeCharts : ChartedSpace (ComplexModel (segreDim E.ambientDimension s)) (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticTNChartedSpace _ _
local instance nativeManifold : IsComplexManifold (segreDim E.ambientDimension s) (SchemeComplexPoint
    (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))) := schemeAnalyticTN_isComplexManifold _ _

/-- **The SAME actual original product graph map has injective differential**, without an immersion certificate. -/
theorem openGraphMap_mfderiv_injective
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s))
      (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W) p) := by
  let a := schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
    (literalOpenProjectiveMap_overBase E j hU b W)
  let h : SchemeComplexPoint (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s)) →
      ComplexProjectiveSpace (segreDim E.ambientDimension s) := projectivePoint (polynomialProjStructureMap ℂ (segreDim E.ambientDimension s))
    (identityEmbedding (segreDim E.ambientDimension s)) (segreDim E.ambientDimension s)
  let g := openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
  let t := segreAmbientMap (m := m) (s := s) E
  have ha := (literalOpenProjectiveMap_contMDiff E j b W (m + 1)).mdifferentiable (by simp)
  have hh : MDifferentiable 𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s))
      𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) h := by
    have hhol := projectivePoint_contMDiff _ (identityEmbedding (segreDim E.ambientDimension s))
      (segreDim E.ambientDimension s)
    change ContMDiff 𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s))
      𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) ∞ h at hhol
    exact hhol.mdifferentiable (by simp)
  have hg := (openGraphMap_contMDiff (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W).mdifferentiable (by simp)
  have ht := (contMDiff_segreAmbientMap (m := m) (s := s) E).mdifferentiable (by simp)
  have hfun : h ∘ a = t ∘ g := funext (originalSegre_native_square (m := m) E j b W)
  have hcomp : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) (h ∘ a) p) := by
    rw [mfderiv_comp p (hh _) (ha _)]
    exact (projectivePoint_mfderiv_injective _ (identityEmbedding (segreDim E.ambientDimension s))
      (segreDim E.ambientDimension s) (a p)).comp
        (literalOpenProjectiveMap_mfderiv_injective E j b W (m + 1) p)
  rw [hfun, mfderiv_comp p (ht _) (hg _)] at hcomp
  intro v w hvw
  apply hcomp
  exact congrArg (mfderiv 𝓘(ℂ, ComplexModel ((m + 1) + s))
    𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) t (g p)) hvw

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProductDifferential
