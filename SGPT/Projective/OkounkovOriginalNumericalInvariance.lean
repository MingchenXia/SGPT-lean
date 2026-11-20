import SGPT.Projective.OkounkovOriginalBodyClassInvariance
import SGPT.Projective.OriginalSchemeChernNeronSeveri
import SGPT.Projective.OriginalSchemeLineNumericalDimensions
import SGPT.Projective.NumEqNSCurveInjectivity

/-! Actual existing native numerical equivalence AND independent original integer curve tests.
Blueprint: okounkov-original-numerical-invariance.tex. No full scheme N1/normalization claim. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.NAPotential.FSPos
open SGPT.Projective.NumEq
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Okounkov.OriginalDifference

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)] [IsSeparated f] [QuasiCompact f]
  {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
  (b : LineBundleAtlas L') (K : SchemeLineBundleMetric f n E L')

local instance originalNumericalBodyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalNumericalBodyCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalNumericalBodyManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Existing ORIGINAL native compact-curve numerical tests manufacture actual class equality, all dimensions. -/
theorem original_chernClass_eq_of_native_numericallyEquivalent
    (hnum : NumericallyEquivalent (H.curvature a) (K.curvature b)) :
    RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let A : OriginalPositiveLine f n E :=
    { sheaf := hyperplaneBundle E, atlas := hyperplaneAtlas E, metric := fubiniStudyMetric f E n,
      positive := fubiniStudy_isKahler f E n }
  have hNSH := originalSchemeLine_chern_mem_neronSeveri f n E a H A
  have hNSK := originalSchemeLine_chern_mem_neronSeveri f n E b K A
  have hNSA := originalPositiveLine_chern_mem_neronSeveri f n E A
  have hproj : SGPT.Trace.Bertini.IsProjectiveManifold n (SchemeComplexPoint f) :=
    SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mpr
      ⟨A.curvature,A.positive,hNSA⟩
  exact ofRepresentative_eq_of_numericallyEquivalent_of_isProjectiveManifold hproj
    (H.curvature a) (K.curvature b) hNSH hNSK hnum

/-- Independent ORIGINAL integer degrees on actual whole smooth embedded curves suffice for the actual class equality. -/
theorem original_chernClass_eq_of_original_integer_curve_tests
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E (originalDifferenceAtlas a b)) :
    RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b) := by
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let Q := originalDifferenceMetric a b f n E H K
  have hzero := originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests_allDims f n E
    (originalDifferenceAtlas a b) Q hnum
  rw [RealBottChern.ofRepresentative_eq_of_geometricallyEq (originalDifferenceMetric_curvature a b f n E H K),
    RealBottChern.ofRepresentative_add,RealBottChern.ofRepresentative_neg] at hzero
  exact (sub_eq_zero.mp (show RealBottChern.ofRepresentative (K.curvature b) -
    RealBottChern.ofRepresentative (H.curvature a) = 0 from hzero)).symm

variable (hbig : SGPT.LineBundle.IsBig f L n) (hbig' : SGPT.LineBundle.IsBig f L' n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
  (c : X) (hc : IsNonnegAt v c)
include hbig hbig' hv hc

/-- Existing original native numerical predicate, literal ORIGINAL bodies, arbitrary valuations/dimensions. -/
theorem okounkovBody_eq_of_native_numericallyEquivalent_allDimensions
    (hnum : NumericallyEquivalent (H.curvature a) (K.curvature b)) :
    okounkovBody v c a = okounkovBody v c b :=
  okounkovBody_eq_of_chernClass_eq_allDimensions f n E a H b K hbig hbig' v hv c hc
    (original_chernClass_eq_of_native_numericallyEquivalent f n E a H b K hnum)

omit c hc in
/-- Source canonical center internally produced, existing original native numerical tests unchanged. -/
theorem centreOkounkovBody_eq_of_native_numericallyEquivalent_allDimensions
    (hnum : NumericallyEquivalent (H.curvature a) (K.curvature b)) :
    haveI := E.isProper
    centreOkounkovBody f v a = centreOkounkovBody f v b :=
  centreOkounkovBody_eq_of_chernClass_eq_allDimensions f n E a H b K hbig hbig' v hv
    (original_chernClass_eq_of_native_numericallyEquivalent f n E a H b K hnum)

/-- Independent ORIGINAL integer smooth embedded curve tests suffice, all components and all dimensions retained. -/
theorem okounkovBody_eq_of_original_integer_curve_tests_allDimensions
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E (originalDifferenceAtlas a b)) :
    okounkovBody v c a = okounkovBody v c b := by
  let H₀ := schemeLineBundleMetric f n E a
  let K₀ := schemeLineBundleMetric f n E b
  exact okounkovBody_eq_of_chernClass_eq_allDimensions f n E a H₀ b K₀ hbig hbig' v hv c hc
    (original_chernClass_eq_of_original_integer_curve_tests f n E a H₀ b K₀ hnum)

omit c hc in
/-- Canonical-center body equality under pure ORIGINAL independent integer curve tests, no class/body comparison input. -/
theorem centreOkounkovBody_eq_of_original_integer_curve_tests_allDimensions
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E (originalDifferenceAtlas a b)) :
    haveI := E.isProper
    centreOkounkovBody f v a = centreOkounkovBody f v b := by
  let H₀ := schemeLineBundleMetric f n E a
  let K₀ := schemeLineBundleMetric f n E b
  exact centreOkounkovBody_eq_of_chernClass_eq_allDimensions f n E a H₀ b K₀ hbig hbig' v hv
    (original_chernClass_eq_of_original_integer_curve_tests f n E a H₀ b K₀ hnum)

end SGPT.Okounkov.OriginalBook
