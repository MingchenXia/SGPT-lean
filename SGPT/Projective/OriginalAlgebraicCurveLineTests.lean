import SGPT.Projective.OriginalCurveLineDegree
import SGPT.Projective.OriginalCurveOverChernTest
import SGPT.Projective.WholeOriginalCIPeriod

/-! Unconditional independent ORIGINAL line degrees on ACTUAL original
smooth algebraic curves and ENTIRE SAME actual original CI terminal curves.
Blueprint: original-algebraic-curve-line-tests.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Projective.NumEq
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NefMixedMass
open scoped Manifold ContDiff BigOperators

local instance originalLineTestTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance originalLineTestCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance originalLineTestManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section Curves
variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) (g : Y ⟶ X)
  (fY : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 fY] [IsSeparated fY] [QuasiCompact fY]
  (hcomp : g ≫ f = fY) (EY : ClosedProjectiveEmbedding fY)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

omit [IsSeparated f] [QuasiCompact f] in
theorem originalAlgebraicCurveLineDegree_eq_degreeAlong
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint fY)) :
    let : CompactSpace (SchemeComplexPoint fY) := EY.analyticCompact
    ((originalCurveLineDegree fY EY (matePullbackAtlas g a) p : ℤ) : ℝ) =
      degreeAlong κ (SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap fY f g hcomp 1 n ∞)
        (H.curvature a) :=
  originalAlgebraicCurveFractionalDegree_eq_degreeAlong_of_over f n E g fY hcomp EY a H
    (originalCurveLinePresentation fY EY (matePullbackAtlas g a)) p κ

namespace OriginalCurveOver
variable {f n E}

theorem lineDegree_eq_degreeAlong (C : OriginalCurveOver f)
    (p : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint C.structureMap)) :
    let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
    ((originalCurveLineDegree C.structureMap (C.embedding E) (matePullbackAtlas C.inclusion a) p : ℤ) : ℝ) =
      degreeAlong κ (C.nativeMap n).contMDiff (H.curvature a) :=
  C.fractionalDegree_eq_degreeAlong a H
    (originalCurveLinePresentation C.structureMap (C.embedding E) (matePullbackAtlas C.inclusion a)) p κ

end OriginalCurveOver
end Curves

namespace WholeOriginalCITower

theorem terminal_originalLineDegree_eq_power_product (k : ℕ) {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (T : WholeOriginalCITower k f E P) {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (k + 1) E L) (p : Spec (.of ℂ))
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((originalCurveLineDegree (terminal k f T).structureMap ((terminal k f T).embedding E)
      (matePullbackAtlas (terminal k f T).inclusion a) p : ℤ) : ℝ) =
      (∏ i, (powers k T i : ℝ)) *
        slotIntegral κ (Fin.cons (H.curvature a) (fun i => (P i).curvature)) := by
  let C := terminal k f T
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
  let κC := C.nativeBackground (k + 1) κ
  have hcurve := C.lineDegree_eq_degreeAlong a H p κC
  exact hcurve.trans (terminal_degree_eq_power_product k f T κ κC (H.curvature a))

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
