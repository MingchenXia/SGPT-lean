import SGPT.Projective.OriginalPulledPhysicalFibres
import SGPT.Projective.AlgebraicNativeCutProducer

/-! Original physical positive line data and literal true algebraic
restrictions. Blueprint: original-positive-line-restriction.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance originalPositiveTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalPositiveCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalPositiveManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Only ACTUAL original physical line data, no cut, curve, period or comparison certificate. -/
structure OriginalPositiveLine where
  sheaf : X.Modules
  atlas : LineBundleAtlas sheaf
  metric : SchemeLineBundleMetric f n E sheaf
  positive : letI := E.isSeparated; letI := E.quasiCompact; (metric.curvature atlas).val.IsKahler

namespace OriginalPositiveLine
variable {f n E}

/-- Literal original fixed physical Chern form. -/
def curvature (P : OriginalPositiveLine f n E) :
    letI := E.isSeparated; letI := E.quasiCompact;
      ClosedRealOneOneForm n (SchemeComplexPoint f) := P.metric.curvature P.atlas

/-- The genuine original associated native positive line, no abstract numerical substitute. -/
def native (P : OriginalPositiveLine f n E) :
    letI := E.isSeparated; letI := E.quasiCompact;
      NativePositiveLine n (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact schemeNativePositiveLine f n E P.atlas P.metric P.positive

variable {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y) (k : ℕ)
  [SmoothOfRelativeDimension k g] (EY : ClosedProjectiveEmbedding g)
  [SmoothOfRelativeDimension n (h ≫ g)] (EX : ClosedProjectiveEmbedding (h ≫ g))

/-- ACTUAL original closed-immersion pullback, inheriting the SAME original physical metric. -/
def restrict [IsClosedImmersion h] (P : OriginalPositiveLine g k EY) :
    OriginalPositiveLine (h ≫ g) n EX where
  sheaf := (Scheme.Modules.pullback h).obj P.sheaf
  atlas := matePullbackAtlas h P.atlas
  metric := originalPhysicalPullbackMetric g h n k EX EY P.atlas P.metric
  positive := originalPhysicalPullbackMetric_isKahler g h n k EX EY P.atlas P.metric P.positive

/-- Its original sheaf is LITERALLY the actual original sheaf pullback. -/
theorem restrict_sheaf [IsClosedImmersion h] (P : OriginalPositiveLine g k EY) :
    (P.restrict (n := n) g h k EY EX).sheaf = (Scheme.Modules.pullback h).obj P.sheaf := rfl

/-- Its physical Chern form is the true original pullback, not a supplied comparison. -/
theorem restrict_curvature [IsClosedImmersion h] (P : OriginalPositiveLine g k EY) :
    letI := EX.isSeparated; letI := EX.quasiCompact;
    letI := EY.isSeparated; letI := EY.quasiCompact;
    (P.restrict (n := n) g h k EY EX).curvature.val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (schemeComplexPointMap_contMDiff g h n k ∞) P.curvature).val :=
  originalPhysicalPullbackMetric_curvature g h n k EX EY P.atlas P.metric

end OriginalPositiveLine
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
