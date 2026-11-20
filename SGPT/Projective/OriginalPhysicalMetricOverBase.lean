import SGPT.Projective.OriginalPhysicalMetricPullback
import SGPT.NAPotential.NativeSchemeImmersion

/-! Actual original physical pullback metric and literal Chern-form
square over a PROVED original coefficient-field structure triangle.
Blueprint: original-physical-metric-over-base.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
    (h : X ⟶ Y) (hh : h ≫ fY=fX) (n m : ℕ)
    [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension m fY]
    (EX : ClosedProjectiveEmbedding fX) (EY : ClosedProjectiveEmbedding fY)

local instance metricOverSourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance metricOverTargetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY
local instance metricOverSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint fX) :=
  schemeAnalyticTNChartedSpace fX n
local instance metricOverTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint fY) :=
  schemeAnalyticTNChartedSpace fY m
local instance metricOverSourceManifold [IsSeparated fX] [QuasiCompact fX] :
    IsComplexManifold n (SchemeComplexPoint fX) := schemeAnalyticTN_isComplexManifold fX n
local instance metricOverTargetManifold [IsSeparated fY] [QuasiCompact fY] :
    IsComplexManifold m (SchemeComplexPoint fY) := schemeAnalyticTN_isComplexManifold fY m

variable {L : Y.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric fY m EY L)

/-- Actual inherited original physical metric on the literal original
pulled line over the retained original source structural morphism. The
proved structure triangle is transported by equality induction. -/
def originalPhysicalPullbackMetricOver :
    SchemeLineBundleMetric fX n EX ((Scheme.Modules.pullback h).obj L) := by
  cases hh
  exact originalPhysicalPullbackMetric fY h n m EX EY a H

/-- The SAME produced physical pullback metric has the true original
Chern-form pullback under the ACTUAL retained native morphism, with no
metric/frame/Chern/map-comparison certificate. -/
theorem originalPhysicalPullbackMetricOver_curvature :
    letI := EX.isSeparated
    letI := EX.quasiCompact
    letI := EY.isSeparated
    letI := EY.quasiCompact
    ((originalPhysicalPullbackMetricOver fX fY h hh n m EX EY a H).curvature
      (matePullbackAtlas h a)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback
        (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fX fY h hh n m ∞)
        (H.curvature a)).val := by
  cases hh
  exact originalPhysicalPullbackMetric_curvature fY h n m EX EY a H

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
