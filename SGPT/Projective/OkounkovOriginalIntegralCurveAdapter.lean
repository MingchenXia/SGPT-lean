import SGPT.Projective.OkounkovOriginalCurveComponentDegree
import SGPT.Projective.OkounkovOriginalNumericalInvariance
import SGPT.Projective.OriginalCITerminalDegreeTransport

/-! Literal all-INTEGRAL original degree tests suffice; true whole component and pullback readers internal.
Blueprint: okounkov-original-integral-curve-adapter.tex. No singular normalization/N1 quotient claim. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.OriginalDifference

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
  [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)

/-- ONLY actual integral smooth embedded ORIGINAL curves and independent original structural INTEGER degree. -/
def OriginalIntegralSmoothEmbeddedCurveZeroTests {N : X.Modules} (q : LineBundleAtlas N) : Prop :=
  ∀ C : OriginalCurveOver f, IsIntegral C.source → ∀ p : Spec (.of ℂ),
    originalCurveLineDegree C.structureMap (C.embedding E) (matePullbackAtlas C.inclusion q) p = 0

/-- Genuine ALL-component original integer degree/pullback/embedding adapters manufacture whole smooth tests. -/
theorem originalSmoothCurveTests_of_integralSmoothCurveTests {N : X.Modules} (q : LineBundleAtlas N)
    (hnum : OriginalIntegralSmoothEmbeddedCurveZeroTests f E q) :
    OriginalSmoothEmbeddedCurveZeroTests f E q := by
  intro C p
  let EC := C.embedding E
  let : IsSeparated C.structureMap := EC.isSeparated
  let : QuasiCompact C.structureMap := EC.quasiCompact
  let := smoothProjective_componentIndex_finite C.structureMap EC
  let : Fintype ↥(_root_.irreducibleComponents C.source) := Fintype.ofFinite _
  rw [CurveComponents.originalCurveLineDegree_eq_sum_components C.structureMap EC
    (matePullbackAtlas C.inclusion q) p]
  apply Finset.sum_eq_zero
  intro i _
  let U := smoothProjectiveComponentOpen C.structureMap 1 EC i.val i.property
  let Ei := smoothProjective_componentEmbedding C.structureMap 1 EC i.val i.property
  let : IsClosedImmersion U.ι := smoothProjective_component_closedImmersion C.structureMap 1 EC i.val i.property
  let : SmoothOfRelativeDimension 1 (U.ι ≫ C.structureMap) :=
    smoothProjective_component_smoothDimension C.structureMap 1 EC i.val i.property
  let D : OriginalCurveOver f :=
    { source := U, structureMap := U.ι ≫ C.structureMap, inclusion := U.ι ≫ C.inclusion,
      over_base := by rw [Category.assoc,C.over_base],closed := inferInstance,smooth := inferInstance }
  let : IsSeparated (U.ι ≫ C.structureMap) := Ei.isSeparated
  let : QuasiCompact (U.ι ≫ C.structureMap) := Ei.quasiCompact
  have hIntegral : IsIntegral D.source := smoothProjective_component_isIntegral C.structureMap 1 EC i.val i.property
  have htest := hnum D hIntegral p
  have hE : D.embedding E = Ei := by
    simp only [D,Ei,EC,U,OriginalCurveOver.embedding,smoothProjective_componentEmbedding,Category.assoc]
  rw [hE] at htest
  have hiso := originalCurveLineDegree_eq_of_sheafIso (U.ι ≫ C.structureMap) Ei
    (matePullbackAtlas U.ι (matePullbackAtlas C.inclusion q))
    (matePullbackAtlas (U.ι ≫ C.inclusion) q)
    ((Scheme.Modules.pullbackComp U.ι C.inclusion).app N) p
  exact hiso.trans htest

variable [IsIntegral X] (n : ℕ) [SmoothOfRelativeDimension n f]
  [Nonempty (SchemeComplexPoint f)] {L L' : X.Modules}
  (a : LineBundleAtlas L) (b : LineBundleAtlas L')
  (hbig : SGPT.LineBundle.IsBig f L n) (hbig' : SGPT.LineBundle.IsBig f L' n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
  (c : X) (hc : IsNonnegAt v c)
include hbig hbig' hv hc

/-- Stronger than printed numerical invariance: ONLY smooth INTEGRAL original curve tests, all valuations/dimensions. -/
theorem okounkovBody_eq_of_original_integral_curve_tests_allDimensions
    (hnum : OriginalIntegralSmoothEmbeddedCurveZeroTests f E (originalDifferenceAtlas a b)) :
    okounkovBody v c a = okounkovBody v c b :=
  okounkovBody_eq_of_original_integer_curve_tests_allDimensions f n E a b hbig hbig' v hv c hc
    (originalSmoothCurveTests_of_integralSmoothCurveTests f E (originalDifferenceAtlas a b) hnum)

omit c hc in
/-- Whole printed source stronger root: actual ORIGINAL integral degree tests, canonical center produced, no N1 redefinition. -/
theorem centreOkounkovBody_eq_of_original_integral_curve_tests_allDimensions
    (hnum : OriginalIntegralSmoothEmbeddedCurveZeroTests f E (originalDifferenceAtlas a b)) :
    haveI := E.isProper
    centreOkounkovBody f v a = centreOkounkovBody f v b :=
  centreOkounkovBody_eq_of_original_integer_curve_tests_allDimensions f n E a b hbig hbig' v hv
    (originalSmoothCurveTests_of_integralSmoothCurveTests f E (originalDifferenceAtlas a b) hnum)

end SGPT.Okounkov.OriginalBook
