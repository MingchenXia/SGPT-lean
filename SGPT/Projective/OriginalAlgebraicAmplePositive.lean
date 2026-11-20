import SGPT.Projective.OriginalPositiveLineRestriction
import SGPT.LineBundle.AmplePositiveMetric

/-! Actual ORIGINAL algebraic ample polarization manufactures the SAME
original positive physical line, no metric or Chern-output input.
Blueprint: original-algebraic-ample-positive.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance algebraicAmplePositiveTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance algebraicAmplePositiveCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance algebraicAmplePositiveManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- ONLY actual original algebraic line/atlas/ample polarization are inputs.
Its genuine original embedding/FS pullback/root metric producer manufactures
the SAME positive physical original line before any CI/testing choices. -/
def originalPositiveLineOfAlgebraicAmple {L : X.Modules} (a : LineBundleAtlas L)
    (P : SGPT.LineBundle.AmplePolarization f L) : OriginalPositiveLine f n E where
  sheaf := L
  atlas := a
  metric := (SGPT.LineBundle.AmpleChern.exists_positive_metric_of_amplePolarization f n E P a).choose
  positive := (SGPT.LineBundle.AmpleChern.exists_positive_metric_of_amplePolarization f n E P a).choose_spec

/-- The manufactured positive line is the SAME actual original algebraic sheaf. -/
theorem originalPositiveLineOfAlgebraicAmple_sheaf {L : X.Modules} (a : LineBundleAtlas L)
    (P : SGPT.LineBundle.AmplePolarization f L) :
    (originalPositiveLineOfAlgebraicAmple f n E a P).sheaf = L := rfl

/-- Its actual atlas is LITERALLY the prescribed original algebraic atlas. -/
theorem originalPositiveLineOfAlgebraicAmple_atlas {L : X.Modules} (a : LineBundleAtlas L)
    (P : SGPT.LineBundle.AmplePolarization f L) :
    (originalPositiveLineOfAlgebraicAmple f n E a P).atlas = a := rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
