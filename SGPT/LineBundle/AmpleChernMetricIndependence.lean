import SGPT.LineBundle.AmpleChernSameH0
import SGPT.Hodge.SourceSmoothMixedCohomology

/-! The actual ample diagonal Chern comparison extends across arbitrary
original smooth physical metrics by the proved global log-ratio and Stokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Okounkov SGPT.Hodge.BDivChain.SourceMixedOrderDraft

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [Nonempty (SchemeComplexPoint f)]

local instance metricChernTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance metricChernCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance metricChernManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance metricChernMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance metricChernBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [IsIntegral X] [Nonempty (SchemeComplexPoint f)] in
/-- Any two actual smooth physical metrics on the same original scheme
bundle have the same actual diagonal Chern integral, via the produced
smooth global log ratio and the original compact Stokes theorem. -/
theorem diagonal_chern_slotIntegral_metric_independent {L : X.Modules}
    (a : LineBundleAtlas L) (H K : SchemeLineBundleMetric f (m + 1) E L) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ κ : KahlerBackground (m + 1) (SchemeComplexPoint f),
      slotIntegral κ (fun _ : Fin (m + 1) => H.curvature a) =
        slotIntegral κ (fun _ : Fin (m + 1) => K.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  dsimp only
  intro κ
  have hclass := H.chernClass_independent K a a
  have hrel : ClosedRealOneOneForm.BottChernRel (H.curvature a) (K.curvature a) :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp hclass
  exact slotIntegral_eq_of_bottChernRel κ _ _ (fun _ => hrel)

/-- Given one actual smooth semipositive physical metric, the actual ample
self-intersection agrees with the Chern integral of every actual original
smooth physical metric. No intersection identity is supplied as a premise. -/
theorem selfIntersection_eq_slotIntegral_of_semipositive_metric {L : X.Modules}
    (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (H K : SchemeLineBundleMetric f (m + 1) E L)
    (hK : let := E.isSeparated; let := E.quasiCompact;
      (K.curvature a).val.IsSemipositive) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ κ : KahlerBackground (m + 1) (SchemeComplexPoint f),
      P.selfIntersection (m + 1) = slotIntegral κ (fun _ : Fin (m + 1) => H.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  dsimp only
  intro κ
  exact (selfIntersection_eq_slotIntegral_of_semipositive f E P a K hK κ).trans
    (diagonal_chern_slotIntegral_metric_independent f E a K H κ)

end SGPT.LineBundle.AmpleChern
