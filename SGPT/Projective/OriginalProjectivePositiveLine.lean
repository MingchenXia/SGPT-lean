import SGPT.Projective.OriginalSchemeChernNeronSeveri
import SGPT.Projective.OriginalTwistedCurveSection
import SGPT.NAPotential.FSPosAlgebraic

/-! The SAME original embedding's actual hyperplane sheaf and physical
Fubini--Study metric discharge the positive original line input.
Blueprint: original-projective-positive-line.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance originalHyperplaneTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalHyperplaneCharts (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance originalHyperplaneManifold (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

/-- The SAME original embedding's literal hyperplane sheaf/atlas/physical metric. -/
def originalHyperplanePositiveLine : OriginalPositiveLine f n E where
  sheaf := hyperplaneBundle E
  atlas := hyperplaneAtlas E
  metric := fubiniStudyMetric f E n
  positive := fubiniStudy_curvature_isKahler f n E

/-- ANY actual original physical line Chern class belongs to the native Cartier span. -/
theorem originalProjectiveLine_chern_mem_neronSeveri {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) :
    RealBottChern.ofRepresentative (H.curvature a) ∈
      SGPT.BDivisor.DFAlg.neronSeveri n (SchemeComplexPoint f) :=
  originalSchemeLine_chern_mem_neronSeveri f n E a H (originalHyperplanePositiveLine f n E)

include f E in
/-- Actual ordinary original section of a literal hyperplane twist/power, on ALL original components. -/
theorem exists_originalProjectiveTwisted_curveSection [SmoothOfRelativeDimension 1 f]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L) :
    ∃ M : ℕ, 0 < M ∧ ∃ d : ℕ, 0 < d ∧
      ∃ s : bundlePowerGlobalSections (bundleTensor L (bundleTensorPower (hyperplaneBundle E) M)) d,
        SectionNonzeroOnComponents f E s :=
  exists_originalTwisted_curveSection f E a H (originalHyperplanePositiveLine f 1 E)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
