import SGPT.Projective.WholeCurveZeroDegree
import SGPT.Projective.OrdinaryCurveChernDegree
import SGPT.Projective.OriginalComponentPeriod
import SGPT.Projective.OriginalPhysicalMetricPullback

/-! ENTIRE actual original smooth projective curve, all components/nilpotents:
independent original effective-section algebraic degree = SAME original H Chern period.
Blueprint: whole-curve-chern-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass ModificationMassInvariance
open MixedMassClassInvariance SGPT.Okounkov SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped Topology Manifold BigOperators ContDiff
attribute [local instance] componentPeriodTopology componentPeriodCharts componentPeriodManifold
  componentPeriodMeasurable componentPeriodBorel actualComponentSmooth actualComponentSeparated
  actualComponentQuasiCompact actualComponentTopology actualComponentCharts actualComponentManifold
  actualComponentMeasurable actualComponentBorel actualComponentCompact
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
  (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s)

/-- EACH independently defined original component zero degree is SAME original pulled metric Chern period. -/
theorem curveComponentSectionZeroCycleDegree_eq_pulledChernPeriod
    (C : ↥(_root_.irreducibleComponents X)) (b : Spec (.of ℂ))
    (κ : KahlerBackground 1
      (SchemeComplexPoint ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f))) :
    ((curveComponentSectionZeroCycleDegree f E a s hs C b : ℤ) : ℝ) =
      slotIntegral κ (pullbackTuple (schemeComplexPointMap_contMDiff f
        (smoothProjectiveComponentOpen f 1 E C.val C.property).ι 1 1 ∞)
        (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a))) := by
  let U := smoothProjectiveComponentOpen f 1 E C.val C.property
  let EC := smoothProjective_componentEmbedding f 1 E C.val C.property
  let : SmoothOfRelativeDimension 1 (U.ι ≫ f) :=
    smoothProjective_component_smoothDimension f 1 E C.val C.property
  let : IsSeparated (U.ι ≫ f) := EC.isSeparated
  let : QuasiCompact (U.ι ≫ f) := EC.quasiCompact
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint (U.ι ≫ f)) :=
    schemeAnalyticTNChartedSpace (U.ι ≫ f) (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint (U.ι ≫ f)) :=
    schemeAnalyticTN_isComplexManifold (U.ι ≫ f) (0 + 1)
  let aC := matePullbackAtlas U.ι a
  let HC := originalPhysicalPullbackMetric f U.ι 1 1 EC E a H
  let := smoothProjective_component_isIntegral f 1 E C.val C.property
  have hd := ordinarySectionZeroCycleDegree_eq_originalChernPeriod (U.ι ≫ f) EC aC HC
    (originalCurveComponentSection f E s C) (hs C) b κ
  change ((curveComponentSectionZeroCycleDegree f E a s hs C b : ℤ) : ℝ) =
    slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (HC.curvature aC)) at hd
  rw [hd]
  have hgeo := originalPhysicalPullbackMetric_curvature f U.ι 1 1 EC E a H
  have hrel := ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo
  apply slotIntegral_eq_of_bottChernRel
  intro i
  refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
  simpa only [Fin.snoc_last, pullbackTuple] using hrel

/-- ENTIRE independent original effective-section degree equals SAME original supplied physical Chern period. -/
theorem wholeCurveSectionZeroCycleDegree_eq_originalChernPeriod
    (b : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f))
    (κC : ∀ C : ↥(_root_.irreducibleComponents X), KahlerBackground 1
      (SchemeComplexPoint ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f))) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ((wholeCurveSectionZeroCycleDegree f E a s hs b : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := smoothProjective_componentIndex_finite f E
  let : Fintype ↥(_root_.irreducibleComponents X) := Fintype.ofFinite _
  rw [wholeCurveSectionZeroCycleDegree_eq_sum_components f E a s hs b, Int.cast_sum]
  calc
    _ = ∑ C : ↥(_root_.irreducibleComponents X), slotIntegral (κC C)
        (pullbackTuple (schemeComplexPointMap_contMDiff f
          (smoothProjectiveComponentOpen f 1 E C.val C.property).ι 1 1 ∞)
          (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a))) :=
      Finset.sum_congr rfl (fun C _ =>
        curveComponentSectionZeroCycleDegree_eq_pulledChernPeriod f E a H s hs C b (κC C))
    _ = _ := originalProjectiveComponent_slotIntegral_sum f 1 E κ κC _

end SGPT.Projective.NumEq.AlgebraicCurveDegree
