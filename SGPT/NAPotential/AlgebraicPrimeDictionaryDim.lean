import SGPT.NAPotential.AlgebraicPrimeDictionaryMain
import SGPT.NAPotential.PLCurveDimZero

/-! The original piecewise-linear hull comparison in every dimension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.NAPotential.AlgebraicPrimeDictionary
open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich SGPT.NAPotential.BJPrep
open SGPT.NAPotential.Berkovich.PiecewiseLinearData

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f]
local instance pointTopologyDim : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointChartsDim : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance pointManifoldDim : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- The printed piecewise-linear hull identity on the revised divisorial
set, including dimension zero and the trivial valuation, for arbitrary θ. -/
theorem curveAn_eq_naPotentialAnAt_hull_dim (E : ClosedProjectiveEmbedding f)
    (D : PiecewiseLinearData θ) (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (v : sourceDivisorialSet f) :
    D.curveAn n E v = naPotentialAnAt n E (hullNAPotential D) ω v := by
  cases n with
  | zero => exact PLCurveDimZero.curveAn_eq_naPotentialAnAt_hull E D ω v
  | succ k => exact curveAn_eq_naPotentialAnAt_hull E D ω v

end SGPT.NAPotential.AlgebraicPrimeDictionary
