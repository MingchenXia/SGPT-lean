import SGPT.Projective.OriginalAlgebraicAmplePositive
import SGPT.Projective.WholeOriginalAlgebraicCI

/-! PURE original algebraic ample tuple chooses the SAME whole original CI
BEFORE any testing line/metric; raw independent original INTEGER degree and
true cutting-power quotient compare to ANY later smooth mixed Chern tuple.
No source mixed product definition. Blueprint: original-algebraic-ample-ci-tower.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped BigOperators

local instance algebraicMixedTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance algebraicMixedCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance algebraicMixedManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ)
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (L : Fin k → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i)) (AP : ∀ i, SGPT.LineBundle.AmplePolarization f (L i))

/-- Actual ORIGINAL algebraic line/atlas/ample polarizations ONLY determine
the original positive cutting data, before ANY testing line or metric. -/
def originalAlgebraicAmpleCuttingLines : Fin k → OriginalPositiveLine f (k + 1) E :=
  fun i => originalPositiveLineOfAlgebraicAmple f (k + 1) E (a i) (AP i)

/-- Actual ENTIRE original algebraic CI tower chosen from ORIGINAL algebraic
ample data only, BEFORE ANY test line, test metric, or later cutting metrics. -/
def originalAlgebraicAmpleCITower :
    WholeOriginalCITower k f E (originalAlgebraicAmpleCuttingLines f k E L a AP) :=
  Classical.choice (exists_wholeOriginalCITower k f E (originalAlgebraicAmpleCuttingLines f k E L a AP))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
