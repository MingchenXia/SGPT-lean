import SGPT.Projective.OriginalHyperplaneFractionalDegree
import SGPT.Projective.OriginalPhysicalMetricPullback
import SGPT.Projective.NumEqCurves

/-! ACTUAL original algebraic curve fractional degree = SAME original
native Chern degreeAlong under the ACTUAL original scheme point map.
Blueprint: original-algebraic-curve-chern-test.tex. -/
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
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff

local instance originalCurveTestTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance originalCurveTestCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance originalCurveTestManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) (g : Y ⟶ X)
  [SmoothOfRelativeDimension 1 (g ≫ f)] [IsSeparated (g ≫ f)] [QuasiCompact (g ≫ f)]
  (EY : ClosedProjectiveEmbedding (g ≫ f))
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (P : OriginalHyperplaneFractionalPresentation (g ≫ f) EY ((Scheme.Modules.pullback g).obj L))

omit [IsSeparated f] [QuasiCompact f] in
theorem originalAlgebraicCurveFractionalDegree_eq_degreeAlong (p : Spec (.of ℂ))
    (κ : KahlerBackground 1 (SchemeComplexPoint (g ≫ f))) :
    let : CompactSpace (SchemeComplexPoint (g ≫ f)) := EY.analyticCompact
    ((P.degree (matePullbackAtlas g a) p : ℤ) : ℝ) =
      degreeAlong κ (schemeComplexPointMap_contMDiff f g 1 n ∞) (H.curvature a) := by
  let : CompactSpace (SchemeComplexPoint (g ≫ f)) := EY.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint (g ≫ f)) := borel _
  let : BorelSpace (SchemeComplexPoint (g ≫ f)) := ⟨rfl⟩
  have h := originalHyperplaneFractionalDegree_eq_ChernPeriod (g ≫ f) EY (matePullbackAtlas g a)
    (originalPhysicalPullbackMetric f g 1 n EY E a H) P p κ
  refine h.trans ?_
  apply slotIntegral_eq_of_bottChernRel
  intro i
  fin_cases i
  exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
    (originalPhysicalPullbackMetric_curvature f g 1 n EY E a H)

omit [IsSeparated f] [QuasiCompact f] in
theorem originalAlgebraicCurveFractionalDegree_zero_iff_degreeAlong (p : Spec (.of ℂ))
    (κ : KahlerBackground 1 (SchemeComplexPoint (g ≫ f))) :
    let : CompactSpace (SchemeComplexPoint (g ≫ f)) := EY.analyticCompact
    P.degree (matePullbackAtlas g a) p = 0 ↔
      degreeAlong κ (schemeComplexPointMap_contMDiff f g 1 n ∞) (H.curvature a) = 0 := by
  let : CompactSpace (SchemeComplexPoint (g ≫ f)) := EY.analyticCompact
  have h := originalAlgebraicCurveFractionalDegree_eq_degreeAlong f n E g EY a H P p κ
  constructor
  · intro hz
    simpa only [hz, Int.cast_zero] using h.symm
  · intro hz
    have hc : ((P.degree (matePullbackAtlas g a) p : ℤ) : ℝ) = 0 := h.trans hz
    exact_mod_cast hc

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
