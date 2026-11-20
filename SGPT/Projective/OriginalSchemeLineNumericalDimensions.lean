import SGPT.Projective.OriginalSchemeLineNumericalKernel

/-! EVERY actual original dimension, including genuine zero-dimensional
forms and original zero-step curve tower. Explicit smooth embedded tests.
Blueprint: original-scheme-line-numerical-dimensions.tex. -/
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
open NefMixedMass

local instance originalDimensionTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance originalDimensionCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance originalDimensionManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

theorem originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests_dim_one
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E a) :
    RealBottChern.ofRepresentative (H.curvature a) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let A := originalHyperplanePositiveLine f 1 E
  let κ : KahlerBackground 1 (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  let P : Fin 0 → OriginalPositiveLine f 1 E := Fin.elim0
  have hz := slotIntegral_originalPositive_tuple_eq_zero_of_curveTests 0 f E a H hnum P κ
  have htuple : (Fin.cons (H.curvature a) (fun i : Fin 0 => (P i).curvature) :
      Fin 1 → ClosedRealOneOneForm 1 (SchemeComplexPoint f)) = fun _ => H.curvature a := by
    funext i
    fin_cases i
    rfl
  rw [htuple] at hz
  exact ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one κ (H.curvature a) hz

theorem originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E a) :
    RealBottChern.ofRepresentative (H.curvature a) = 0 := by
  cases n with
  | zero =>
    have hz : H.curvature a = 0 := by
      apply ClosedRealOneOneForm.ext
      intro e z
      apply ContinuousAlternatingMap.ext
      intro v
      change ((H.curvature a).val.coeff e z) v = 0
      exact ((H.curvature a).val.coeff e z).map_coord_zero (0 : Fin 2) (Subsingleton.elim (v 0) 0)
    rw [hz, RealBottChern.ofRepresentative_zero]
  | succ n =>
    cases n with
    | zero => exact originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests_dim_one f E a H hnum
    | succ m => exact originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests f E a H hnum

theorem originalSmoothEmbeddedCurveZeroTests_iff_chernClass_eq_zero_allDims
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) :
    OriginalSmoothEmbeddedCurveZeroTests f E a ↔ RealBottChern.ofRepresentative (H.curvature a) = 0 :=
  ⟨originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims f n E a H,
    originalSmoothEmbeddedCurveZeroTests_of_chernClass_eq_zero f n E a H⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
