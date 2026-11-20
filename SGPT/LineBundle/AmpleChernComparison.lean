import SGPT.LineBundle.AmpleChernMetricIndependence
import SGPT.LineBundle.AmplePositiveMetric

/-! The original algebraic ample intersection number equals the actual
Chern integral, with every required positive metric manufactured from P. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Okounkov

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [Nonempty (SchemeComplexPoint f)]

local instance comparisonChernTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance comparisonChernCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance comparisonChernManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m + 1)
local instance comparisonChernMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance comparisonChernBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- An actual ample polarization and any actual smooth physical metric on
the original L give the actual algebraic complete-intersection length
number as the actual smooth Chern integral. The positive metric is
manufactured from P; no desired intersection or RR certificate is an input. -/
theorem selfIntersection_eq_slotIntegral {L : X.Modules}
    (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ κ : KahlerBackground (m + 1) (SchemeComplexPoint f),
      P.selfIntersection (m + 1) = slotIntegral κ (fun _ : Fin (m + 1) => H.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  dsimp only
  intro κ
  obtain ⟨K, hK⟩ := exists_positive_metric_of_amplePolarization f (m + 1) E P a
  let κK : KahlerBackground (m + 1) (SchemeComplexPoint f) := ⟨K.curvature a, hK⟩
  exact selfIntersection_eq_slotIntegral_of_semipositive_metric f E P a H K κK.isSemipositive κ

end SGPT.LineBundle.AmpleChern
