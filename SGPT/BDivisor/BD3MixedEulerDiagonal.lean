import SGPT.BDivisor.BD3AlgebraicMixedEulerChoice
import SGPT.LineBundle.AmpleChernComparison

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalMixedEulerDiagonal`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalMixedEulerDiagonal`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: Actual ORIGINAL mixed Euler normalization agrees on the diagonal with
EXISTING original full-Artinian-flag-length / true ample-power^n.
No source number redefinition. Blueprint: original-mixed-euler-diagonal.tex.
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

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (k : ℕ)
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (AP : SGPT.LineBundle.AmplePolarization f L)

local instance originalEulerDiagonalTopology_bd3 : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalEulerDiagonalCharts_bd3 : ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance originalEulerDiagonalManifold_bd3 : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

/-- The raw actual ORIGINAL integer mixed Euler / SAME actual whole-CI
cutting powers is the PREEXISTING genuine original ample diagonal number,
full original Artinian flag length / actual AP.power^(k+1). No metric,
Euler/period/intersection comparison or normalization premise. -/
theorem originalMixedEuler_diagonal_eq_originalSelfIntersection_bd3
    (T : WholeOriginalCITower k f E
      (fun _ : Fin k => originalPositiveLineOfAlgebraicAmple f (k + 1) E a AP))
    (B : IntrinsicLineBundle X) :
    (originalMixedEulerDifference f E
      (originalCITowerCuttingDirections_bd3 k
        (fun _ : Fin k => originalPositiveLineOfAlgebraicAmple f (k + 1) E a AP) T ++
          [⟨L, a⟩]) B : ℝ) / (∏ i, (WholeOriginalCITower.powers k T i : ℝ)) =
      AP.selfIntersection (k + 1) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let Q := originalPositiveLineOfAlgebraicAmple f (k + 1) E a AP
  let κ : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨Q.curvature, Q.positive⟩
  let p : Spec (.of ℂ) := genericPoint _
  have hraw := WholeOriginalCITower.mixedEuler_quotient_eq_period_of_metrics_bd3 k f E
    (fun _ : Fin k => Q) T ⟨L, a⟩ B Q.metric (fun _ => Q.metric) p κ
  have hdiag := SGPT.LineBundle.AmpleChern.selfIntersection_eq_slotIntegral f E AP a Q.metric κ
  have htuple : (Fin.cons (Q.metric.curvature a) (fun _ : Fin k => Q.metric.curvature a) :
      Fin (k + 1) → ClosedRealOneOneForm (k + 1) (SchemeComplexPoint f)) =
      fun _ => Q.metric.curvature a := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change _ = slotIntegral κ
    (Fin.cons (Q.metric.curvature a) (fun _ : Fin k => Q.metric.curvature a)) at hraw
  rw [htuple] at hraw
  exact hraw.trans hdiag.symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
