import SGPT.Projective.OriginalAlgebraicCurveChernTest
import SGPT.Projective.OriginalCurveNativeGeometry

/-! Exact original fractional degree/Chern dictionary for the ACTUAL
retained original CI terminal curve and actual total nativeMap.
Blueprint: original-curve-over-chern-test.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Manifold ContDiff

local instance retainedCurveTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance retainedCurveCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance retainedCurveManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) (g : Y ⟶ X)
  (fY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 fY] [IsSeparated fY] [QuasiCompact fY]
  (hcomp : g ≫ f = fY) (EY : ClosedProjectiveEmbedding fY)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

omit [IsSeparated f] [QuasiCompact f] in
theorem originalAlgebraicCurveFractionalDegree_eq_degreeAlong_of_over
    (P : OriginalHyperplaneFractionalPresentation fY EY ((Scheme.Modules.pullback g).obj L))
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint fY)) :
    let : CompactSpace (SchemeComplexPoint fY) := EY.analyticCompact
    ((P.degree (matePullbackAtlas g a) p : ℤ) : ℝ) =
      degreeAlong κ (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fY f g hcomp 1 n ∞)
        (H.curvature a) := by
  cases hcomp
  exact originalAlgebraicCurveFractionalDegree_eq_degreeAlong f n E g EY a H P p κ

namespace OriginalCurveOver
variable {f n E}

theorem fractionalDegree_eq_degreeAlong (C : OriginalCurveOver f)
    (P : OriginalHyperplaneFractionalPresentation C.structureMap (C.embedding E)
      ((Scheme.Modules.pullback C.inclusion).obj L))
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint C.structureMap)) :
    let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
    ((P.degree (matePullbackAtlas C.inclusion a) p : ℤ) : ℝ) =
      degreeAlong κ (C.nativeMap n).contMDiff (H.curvature a) :=
  originalAlgebraicCurveFractionalDegree_eq_degreeAlong_of_over f n E C.inclusion
    C.structureMap C.over_base (C.embedding E) a H P p κ

end OriginalCurveOver
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
