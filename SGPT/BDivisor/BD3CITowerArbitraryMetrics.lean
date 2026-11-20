import SGPT.BDivisor.BD3AlgebraicCurveLineTests
/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalCITowerArbitraryMetrics`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalCITowerArbitraryMetrics`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: ANY later smooth physical cutting metrics for the SAME actual original
whole CI raw degree, from true original metric independence/Stokes.
Blueprint: original-ci-tower-arbitrary-metrics.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open NefMixedMass SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped BigOperators

local instance arbitraryMetricTopology_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance arbitraryMetricCharts_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance arbitraryMetricManifold_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

namespace WholeOriginalCITower
variable {X : Scheme.{0}} (k : ℕ) (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (T : WholeOriginalCITower k f E P)

/-- The independent ORIGINAL terminal integer degree of ANY SAME actual
whole CI equals its actual positive-power product times the mixed period
of ANY later smooth metrics on the SAME original cutting sheaves. -/
theorem terminal_originalLineDegree_eq_power_product_of_metrics_bd3
    {M : X.Modules} (b : LineBundleAtlas M) (H : SchemeLineBundleMetric f (k + 1) E M)
    (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf) (p : Spec (.of ℂ))
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((originalCurveLineDegree_bd3 (terminal k f T).structureMap ((terminal k f T).embedding E)
      (matePullbackAtlas (terminal k f T).inclusion b) p : ℤ) : ℝ) =
      (∏ i, (powers k T i : ℝ)) *
        slotIntegral κ (Fin.cons (H.curvature b) (fun i => (K i).curvature (P i).atlas)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have hactual := terminal_originalLineDegree_eq_power_product_bd3 k f E P T b H p κ
  have hrel (i : Fin k) : ClosedRealOneOneForm.BottChernRel
      ((P i).curvature) ((K i).curvature (P i).atlas) := by
    have hclass := (P i).metric.chernClass_independent (K i) (P i).atlas (P i).atlas
    exact (RealBottChern.ofRepresentative_eq_iff _ _).mp hclass
  have hhead : ClosedRealOneOneForm.BottChernRel (H.curvature b) (H.curvature b) :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp rfl
  have hperiod := slotIntegral_eq_of_bottChernRel κ
    (Fin.cons (H.curvature b) (fun i => (P i).curvature))
    (Fin.cons (H.curvature b) (fun i => (K i).curvature (P i).atlas))
    (Fin.cases hhead hrel)
  exact hactual.trans (congrArg (fun z : ℝ => (∏ i, (powers k T i : ℝ)) * z) hperiod)

/-- The RAW independent original INTEGER terminal degree divided by the
true actual positive cutting powers is the later smooth mixed period.
No source intersection number is introduced or redefined by this theorem. -/
theorem terminal_originalLineDegree_quotient_of_metrics_bd3
    {M : X.Modules} (b : LineBundleAtlas M) (H : SchemeLineBundleMetric f (k + 1) E M)
    (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf) (p : Spec (.of ℂ))
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ((originalCurveLineDegree_bd3 (terminal k f T).structureMap ((terminal k f T).embedding E)
      (matePullbackAtlas (terminal k f T).inclusion b) p : ℤ) : ℝ) / (∏ i, (powers k T i : ℝ)) =
      slotIntegral κ (Fin.cons (H.curvature b) (fun i => (K i).curvature (P i).atlas)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  apply (div_eq_iff (powers_real_prod_pos k T).ne').mpr
  exact (terminal_originalLineDegree_eq_power_product_of_metrics_bd3 k f E P T b H K p κ).trans (mul_comm _ _)

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
