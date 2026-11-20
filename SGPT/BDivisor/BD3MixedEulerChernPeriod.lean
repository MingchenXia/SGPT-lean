import SGPT.BDivisor.BD3MixedEulerWholeTower
import SGPT.BDivisor.BD3CITowerArbitraryMetrics
import SGPT.Projective.OriginalProjectivePositiveLine

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalMixedEulerChernPeriod`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalMixedEulerChernPeriod`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Genuine ORIGINAL mixed Euler / actual cutting-power normalization and
SAME mixed Chern period. No source mixed-intersection definition.
Blueprint: original-mixed-euler-chern-period.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open scoped BigOperators

local instance mixedEulerChernTopology_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance mixedEulerChernCharts_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance mixedEulerChernManifold_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

namespace WholeOriginalCITower
variable {X : Scheme.{0}} (k : ℕ) (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (T : WholeOriginalCITower k f E P)

/-- Genuine original n-fold INTEGER Euler difference in actual original
GLOBAL cutting-power directions equals their actual power product times
mixed Chern period for ANY later metrics on the SAME original sheaves. -/
theorem mixedEuler_eq_power_product_of_metrics_bd3
    (A B : IntrinsicLineBundle X) (H : SchemeLineBundleMetric f (k + 1) E A.sheaf)
    (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf) (p : Spec (.of ℂ))
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    (originalMixedEulerDifference f E (originalCITowerCuttingDirections_bd3 k P T ++ [A]) B : ℝ) =
      (∏ i, (powers k T i : ℝ)) *
        slotIntegral κ (Fin.cons (H.curvature A.atlas) (fun i => (K i).curvature (P i).atlas)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  exact (congrArg (fun z : ℤ => (z : ℝ))
    (mixedEuler_eq_terminal_originalLineDegree_bd3 k f E P T A B p)).trans
      (terminal_originalLineDegree_eq_power_product_of_metrics_bd3 k f E P T A.atlas H K p κ)

/-- RAW independent original INTEGER mixed Euler divided by the TRUE
positive cutting powers is the actual mixed Chern period. No new source
intersection number is defined by an integral or diagonal polarization. -/
theorem mixedEuler_quotient_eq_period_of_metrics_bd3
    (A B : IntrinsicLineBundle X) (H : SchemeLineBundleMetric f (k + 1) E A.sheaf)
    (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf) (p : Spec (.of ℂ))
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    (originalMixedEulerDifference f E (originalCITowerCuttingDirections_bd3 k P T ++ [A]) B : ℝ) /
      (∏ i, (powers k T i : ℝ)) =
        slotIntegral κ (Fin.cons (H.curvature A.atlas) (fun i => (K i).curvature (P i).atlas)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  apply (div_eq_iff (powers_real_prod_pos k T).ne').mpr
  exact (mixedEuler_eq_power_product_of_metrics_bd3 k f E P T A B H K p κ).trans (mul_comm _ _)

/-- PURE original mixed-Euler/actual-power ratios for TWO actual whole
original towers coincide. Base testing twists may differ. The raw scheme
quantities are independent; no body, period or desired equality is an input. -/
theorem mixedEuler_quotient_independent_tower_bd3
    (S : WholeOriginalCITower k f E P) (A B C : IntrinsicLineBundle X) :
    (originalMixedEulerDifference f E (originalCITowerCuttingDirections_bd3 k P T ++ [A]) B : ℝ) /
      (∏ i, (powers k T i : ℝ)) =
    (originalMixedEulerDifference f E (originalCITowerCuttingDirections_bd3 k P S ++ [A]) C : ℝ) /
      (∏ i, (powers k S i : ℝ)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let H := schemeLineBundleMetric f (k + 1) E A.atlas
  let Q := originalHyperplanePositiveLine f (k + 1) E
  let κ : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨Q.curvature, Q.positive⟩
  let p : Spec (.of ℂ) := genericPoint _
  exact (mixedEuler_quotient_eq_period_of_metrics_bd3 k f E P T A B H (fun i => (P i).metric) p κ).trans
    (mixedEuler_quotient_eq_period_of_metrics_bd3 k f E P S A C H (fun i => (P i).metric) p κ).symm

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
