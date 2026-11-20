import SGPT.BDivisor.BD3CurveLineDegree
import SGPT.Projective.OriginalComponentPeriod
import SGPT.Projective.OriginalPhysicalMetricPullback

/-! Actual independent ORIGINAL arbitrary-line INTEGER degree sums over ALL true integral clopen components.
Blueprint: okounkov-original-curve-component-degree.tex. No singular normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook.CurveComponents
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass ModificationMassInvariance
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

attribute [local instance] componentPeriodTopology componentPeriodCharts componentPeriodManifold
  componentPeriodMeasurable componentPeriodBorel actualComponentSmooth actualComponentSeparated
  actualComponentQuasiCompact actualComponentTopology actualComponentCharts actualComponentManifold
  actualComponentMeasurable actualComponentBorel actualComponentCompact

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L)

private theorem componentDegree_eq_pulledChernPeriod_bd7 (H : SchemeLineBundleMetric f 1 E L)
    (C : ↥(_root_.irreducibleComponents X)) (p : Spec (.of ℂ))
    (κ : KahlerBackground 1
      (SchemeComplexPoint ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f))) :
    ((originalCurveLineDegree_bd3
      ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
      (smoothProjective_componentEmbedding f 1 E C.val C.property)
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a) p : ℤ) : ℝ) =
      slotIntegral κ (pullbackTuple (schemeComplexPointMap_contMDiff f
        (smoothProjectiveComponentOpen f 1 E C.val C.property).ι 1 1 ∞)
        (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a))) := by
  let U := smoothProjectiveComponentOpen f 1 E C.val C.property
  let EC := smoothProjective_componentEmbedding f 1 E C.val C.property
  let aC := matePullbackAtlas U.ι a
  let HC := originalPhysicalPullbackMetric f U.ι 1 1 EC E a H
  have hd := originalCurveLineDegree_eq_ChernPeriod_bd3 (U.ι ≫ f) EC aC HC p κ
  rw [hd]
  have hgeo := originalPhysicalPullbackMetric_curvature f U.ι 1 1 EC E a H
  have hrel := ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo
  apply slotIntegral_eq_of_bottChernRel
  intro i
  refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
  simpa only [Fin.snoc_last,pullbackTuple] using hrel

/-- Independent ORIGINAL structural integer degree of ANY line equals ALL original component degrees. -/
theorem originalCurveLineDegree_eq_sum_components_bd7 (p : Spec (.of ℂ)) :
    let : Finite ↥(_root_.irreducibleComponents X) := smoothProjective_componentIndex_finite f E
    let : Fintype ↥(_root_.irreducibleComponents X) := Fintype.ofFinite _
    originalCurveLineDegree_bd3 f E a p =
      ∑ C : ↥(_root_.irreducibleComponents X), originalCurveLineDegree_bd3
        ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
        (smoothProjective_componentEmbedding f 1 E C.val C.property)
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a) p := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := smoothProjective_componentIndex_finite f E
  let : Fintype ↥(_root_.irreducibleComponents X) := Fintype.ofFinite _
  let H := schemeLineBundleMetric f 1 E a
  let κ := schemeProjectiveTNKahlerBackground f 1 E
  let κC (C : ↥(_root_.irreducibleComponents X)) := schemeProjectiveTNKahlerBackground
    ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f) 1
    (smoothProjective_componentEmbedding f 1 E C.val C.property)
  have hwhole := originalCurveLineDegree_eq_ChernPeriod_bd3 f E a H p κ
  have hsum := originalProjectiveComponent_slotIntegral_sum f 1 E κ κC
    (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a))
  have hcast : ((∑ C : ↥(_root_.irreducibleComponents X), originalCurveLineDegree_bd3
        ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
        (smoothProjective_componentEmbedding f 1 E C.val C.property)
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a) p : ℤ) : ℝ) =
      ((originalCurveLineDegree_bd3 f E a p : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    exact (Finset.sum_congr rfl (fun C _ => componentDegree_eq_pulledChernPeriod_bd7 f E a H C p (κC C))).trans
      (hsum.trans hwhole.symm)
  exact_mod_cast hcast.symm

end SGPT.Okounkov.OriginalBook.CurveComponents
