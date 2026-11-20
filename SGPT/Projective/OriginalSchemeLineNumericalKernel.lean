import SGPT.Projective.OriginalAlgebraicCurveLineTests
import SGPT.Projective.NativeCITowerPeriodBase
import SGPT.Projective.NumEqCurveComponents
import SGPT.Projective.OriginalPositiveTensorTwist

/-! Genuine ORIGINAL smooth embedded algebraic curve degree-test kernel
of a SAME original line; actual original algebraic CI curves and Hodge.
Blueprint: original-scheme-line-numerical-kernel.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
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
open scoped Manifold ContDiff BigOperators

local instance originalNumericalTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance originalNumericalCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance originalNumericalManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- PURE original smooth embedded algebraic curve tests, using independent ORIGINAL integer degree. -/
def OriginalSmoothEmbeddedCurveZeroTests {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L) : Prop :=
  ∀ (C : OriginalCurveOver f) (p : Spec (.of ℂ)),
    originalCurveLineDegree C.structureMap (C.embedding E) (matePullbackAtlas C.inclusion a) p = 0

theorem slotIntegral_originalPositive_tuple_eq_zero_of_curveTests (k : ℕ) {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (k + 1) E L) (hnum : OriginalSmoothEmbeddedCurveZeroTests f E a)
    (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    slotIntegral κ (Fin.cons (H.curvature a) (fun i => (P i).curvature)) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  obtain ⟨T⟩ := exists_wholeOriginalCITower k f E P
  let p : Spec (.of ℂ) := genericPoint _
  have h := WholeOriginalCITower.terminal_originalLineDegree_eq_power_product k f E P T a H p κ
  rw [hnum (WholeOriginalCITower.terminal k f T) p, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (WholeOriginalCITower.powers_real_prod_pos k T).ne'

theorem originalSmoothEmbeddedCurveZeroTests_of_chernClass_eq_zero
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L)
    (hzero : RealBottChern.ofRepresentative (H.curvature a) = 0) :
    OriginalSmoothEmbeddedCurveZeroTests f E a := by
  let A := originalHyperplanePositiveLine f n E
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  have hn := isNumericallyTrivial_of_ofRepresentative_eq_zero hzero
  intro C p
  let : CompactSpace (SchemeComplexPoint C.structureMap) := C.native_compact E
  let κC := C.nativeBackground n κ
  have hcurve := C.lineDegree_eq_degreeAlong a H p κC
  have hz := degreeAlong_eq_zero_of_isNumericallyTrivial_compactCurve (H.curvature a) hn κC (C.nativeMap n).contMDiff
  exact_mod_cast hcurve.trans hz

theorem originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests
    {m : ℕ} {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (m + 2) f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 2) E L)
    (hnum : OriginalSmoothEmbeddedCurveZeroTests f E a) :
    RealBottChern.ofRepresentative (H.curvature a) = 0 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let A := originalHyperplanePositiveLine f (m + 2) E
  let κ : KahlerBackground (m + 2) (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  let alpha := H.curvature a
  have hfirst := slotIntegral_originalPositive_tuple_eq_zero_of_curveTests (m + 1) f E a H hnum (fun _ => A) κ
  have h1 : slotIntegral κ (oneSlot κ alpha) = 0 := by
    rw [oneSlot_eq_cons]
    exact hfirst
  obtain ⟨M, _hM, hpos⟩ := exists_positive_originalTensorTwist f (m + 2) E a H A
  let Q : OriginalPositiveLine f (m + 2) E :=
    { sheaf := bundleTensor L (bundleTensorPower A.sheaf M)
      atlas := pairwiseTensorAtlas a (A.atlas.tensorPower M)
      metric := H.tensorProduct (A.metric.tensorPower A.atlas M) a (A.atlas.tensorPower M)
      positive := hpos }
  have htwist := slotIntegral_originalPositive_tuple_eq_zero_of_curveTests (m + 1) f E a H hnum
    (Fin.cons Q (fun _ : Fin m => A)) κ
  have hperiod : slotIntegral κ
      (Fin.cons alpha (Fin.cons (alpha + (M : ℝ) • κ.form) (fun _ : Fin m => κ.form))) = 0 := by
    have heq := slotIntegral_eq_of_bottChernRel κ
      (Fin.cons alpha (fun i => ((Fin.cons Q (fun _ : Fin m => A) :
        Fin (m + 1) → OriginalPositiveLine f (m + 2) E) i).curvature))
      (Fin.cons alpha (Fin.cons (alpha + (M : ℝ) • κ.form) (fun _ : Fin m => κ.form)))
      (fun i => by
        refine Fin.cases (ClosedRealOneOneForm.BottChernRel.refl alpha) (fun j => ?_) i
        refine Fin.cases ?_ (fun _ => ClosedRealOneOneForm.BottChernRel.refl κ.form) j
        exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
          (originalTensorTwist_curvature f (m + 2) E a H A M))
    exact heq.symm.trans htwist
  rw [← update_oneSlot_eq_cons κ alpha (alpha + (M : ℝ) • κ.form),
    slotIntegral_update_add κ (oneSlot κ alpha) 1,
    slotIntegral_update_smul κ (oneSlot κ alpha) 1] at hperiod
  have hrestore : Function.update (oneSlot κ alpha) 1 κ.form = oneSlot κ alpha := by
    apply Function.update_eq_self_iff.mpr
    simp [oneSlot]
  rw [hrestore, h1, smul_zero, add_zero] at hperiod
  exact ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero κ alpha h1 hperiod

theorem originalSmoothEmbeddedCurveZeroTests_iff_chernClass_eq_zero
    {m : ℕ} {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (m + 2) f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 2) E L) :
    OriginalSmoothEmbeddedCurveZeroTests f E a ↔ RealBottChern.ofRepresentative (H.curvature a) = 0 :=
  ⟨originalLine_chernClass_eq_zero_of_smoothEmbeddedCurveTests f E a H,
    originalSmoothEmbeddedCurveZeroTests_of_chernClass_eq_zero f (m + 2) E a H⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
