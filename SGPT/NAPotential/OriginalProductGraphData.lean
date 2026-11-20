import SGPT.NAPotential.GraphDivisorFunctionOrder
import SGPT.NAPotential.ProjectiveGraphProductDifferential
import SGPT.NAPotential.ProjectiveGraphProductLocal
import SGPT.NAPotential.ProjectiveGraphOpenMembership
import SGPT.NAPotential.ProjectiveGraphUniqueness

/-!
# Actual original product graph data of every algebraic divisor

Complete blueprint: `original-product-graph-data.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.OriginalProductGraphData

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.NAPotential.Berkovich SGPT.NAPotential.AlgPrimes3
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Okounkov
open GraphDivisorFunctionOrder GraphDivisorAnalyticTrace
open ProjectiveGraphCentredChart ProjectiveGraphCoordinateCharts ProjectiveGraphAnalyticMap
open ProjectiveGraphSegre ProjectiveGraphOpenMembership ProjectiveGraphUniqueness
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves BlowupTowers
open scoped Topology Manifold ContDiff
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance originalTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance originalManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

set_option maxHeartbeats 1600000 in
/-- The ORIGINAL divisor produces all ACTUAL product graph data, using one prescribed
original coefficient chart, the SAME actual graph generators and SAME native smooth open. -/
theorem productGraphData_nonempty (E : ClosedProjectiveEmbedding f) (D : PrimeDivisorOver X) :
    Nonempty (ProductGraphData m E D) := by
  obtain ⟨j, hpj⟩ := exists_coordOpen E (D.π D.point)
  let : Nonempty (coordOpen E j) := ⟨⟨D.π D.point, hpj⟩⟩
  obtain ⟨s, b, z, W, hzW, hsm, hsep, hqc, hι, n₀, Ψ, hord⟩ :=
    exists_productDivisorNormalOrder (m := m) E D j hpj
  let := hsm
  let := hsep
  let := hqc
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let fW := openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
  let : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
  let : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
    schemeAnalyticTNChartedSpace fW (m + 1)
  let : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
    schemeAnalyticTN_isComplexManifold fW (m + 1)
  obtain ⟨V, hV, hVU, r, hr, hmem, huniq⟩ := exists_regularGraph_unique (m := m) E b
  refine ⟨{
    V := V
    nonempty_V := ⟨genericPoint X, hV⟩
    s := s
    r := r
    Γ₀ := globalRelationGraph (m := m) E b
    isAnalytic_Γ₀ := isComplexAnalyticSubset_globalRelationGraph (m := m) E b
    graphMap_mem := hmem
    eq_graphMap := fun q hq hx => (huniq q hq hx).symm
    N := CMfd.of (SchemeComplexPoint fW)
    ι := openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W
    contMDiff_ι := hι
    ι_mem := openGraphMap_mem_globalRelationGraph (m := m) E
      (coordOpen E j) (isAffineOpen_coordOpen E j) b W
    injective_mfderiv_ι := ProjectiveGraphProductDifferential.openGraphMap_mfderiv_injective
      (m := m) E j b W
    ι_local := ProjectiveGraphProductLocal.openGraphMap_local (m := m) E j b W
    interior_ι_B := openGraphMap_base_interior (f := f) (m := m)
      (coordOpen E j) (isAffineOpen_coordOpen E j) b W V hV
    n₀ := n₀
    Δ := productDivisorLocus (m := m) E j b z.asIdeal
    isAnalytic_Δ := isComplexAnalyticSubset_productDivisorLocus (m := m) E j b z.asIdeal
    flattening := Ψ
    ord_eq := hord }⟩

/-- The actual original high-codimension graph producer, with no supplied output data. -/
theorem highCodimProductGraphData (E : ClosedProjectiveEmbedding f) :
    HighCodimProductGraphData m E := by
  intro D _
  exact productGraphData_nonempty E D

end SGPT.NAPotential.OriginalProductGraphData
