import SGPT.Projective.OriginalAlgebraicAmpleCITower
import SGPT.BDivisor.BD3MixedEulerChernPeriod
/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalAlgebraicMixedEulerChoice`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalAlgebraicMixedEulerChoice`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Independent ORIGINAL mixed Euler ratios for prescribed actual algebraic
ample lines: genuine choice independence and all-test single whole tower.
Blueprint: original-algebraic-mixed-euler-choice.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open scoped BigOperators

local instance algebraicEulerChoiceTopology_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance algebraicEulerChoiceCharts_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance algebraicEulerChoiceManifold_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ)
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (L : Fin k → X.Modules)
    (a : ∀ i, LineBundleAtlas (L i))
    (AP : ∀ i, SGPT.LineBundle.AmplePolarization f (L i))

/-- The raw ORIGINAL Euler ratio from ONE genuine whole CI is independent
of ALL original ample-polarization witnesses and actual whole CI choices.
No metric/background/period/independence premise; base twists may differ. -/
theorem originalAlgebraicMixedEuler_quotient_independent_choices_bd3
    (BP : ∀ i, SGPT.LineBundle.AmplePolarization f (L i))
    (T : WholeOriginalCITower k f E (originalAlgebraicAmpleCuttingLines f k E L a AP))
    (S : WholeOriginalCITower k f E (originalAlgebraicAmpleCuttingLines f k E L a BP))
    (A B C : IntrinsicLineBundle X) :
    (originalMixedEulerDifference f E
      (originalCITowerCuttingDirections_bd3 k (originalAlgebraicAmpleCuttingLines f k E L a AP) T ++ [A]) B : ℝ) /
        (∏ i, (WholeOriginalCITower.powers k T i : ℝ)) =
    (originalMixedEulerDifference f E
      (originalCITowerCuttingDirections_bd3 k (originalAlgebraicAmpleCuttingLines f k E L a BP) S ++ [A]) C : ℝ) /
        (∏ i, (WholeOriginalCITower.powers k S i : ℝ)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let H := schemeLineBundleMetric f (k + 1) E A.atlas
  let K := fun i => schemeLineBundleMetric f (k + 1) E (a i)
  let Q := originalHyperplanePositiveLine f (k + 1) E
  let κ : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨Q.curvature, Q.positive⟩
  let p : Spec (.of ℂ) := genericPoint _
  have hT := WholeOriginalCITower.mixedEuler_quotient_eq_period_of_metrics_bd3 k f E
    (originalAlgebraicAmpleCuttingLines f k E L a AP) T A B H K p κ
  have hS := WholeOriginalCITower.mixedEuler_quotient_eq_period_of_metrics_bd3 k f E
    (originalAlgebraicAmpleCuttingLines f k E L a BP) S A C H K p κ
  exact hT.trans hS.symm

/-- ONE WHOLE original algebraic CI chosen from prescribed ORIGINAL ample
sheaves/atlases/polarizations BEFORE ALL original test lines/base twists and
smooth metrics computes their raw original integer mixed Euler normalization.
No new source mixed-intersection value is defined by the period. -/
theorem exists_originalAlgebraicMixedEulerTower_before_all_tests_bd3 :
    ∃ T : WholeOriginalCITower k f E (originalAlgebraicAmpleCuttingLines f k E L a AP),
      ∀ (A B : IntrinsicLineBundle X) (H : SchemeLineBundleMetric f (k + 1) E A.sheaf)
        (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (L i))
        (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)),
        let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
        let : MeasurableSpace (SchemeComplexPoint f) := borel _
        let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
        (originalMixedEulerDifference f E
          (originalCITowerCuttingDirections_bd3 k (originalAlgebraicAmpleCuttingLines f k E L a AP) T ++ [A]) B : ℝ) /
          (∏ i, (WholeOriginalCITower.powers k T i : ℝ)) =
            slotIntegral κ (Fin.cons (H.curvature A.atlas) (fun i => (K i).curvature (a i))) := by
  refine ⟨originalAlgebraicAmpleCITower f k E L a AP, ?_⟩
  intro A B H K κ
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let p : Spec (.of ℂ) := genericPoint _
  exact WholeOriginalCITower.mixedEuler_quotient_eq_period_of_metrics_bd3 k f E
    (originalAlgebraicAmpleCuttingLines f k E L a AP) (originalAlgebraicAmpleCITower f k E L a AP)
    A B H K p κ

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
