import SGPT.Projective.NativeSectionLocalCurrent
import SGPT.Projective.DivisorCurrentShuffleArea
import SGPT.Foundations.Analysis.Pending.CurrentPairing

/-! The SAME complete native section current acts by its SAME original
Hausdorff area equation. Blueprint: `native-section-current-area.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ContDiff BigOperators Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.BDivisor.NSKodaira
open LelongPoincareDivisor CanonicalCurrentFrame
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (hL : IsSourceSmoothHermitianMetric L) (s : HolomorphicSections (n := m + 1) L.Fiber)
  (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)

/-- Full unchanged original native chart current = SAME scalar original
Hausdorff divisor-current action, with the actual original canonical frame. -/
theorem nativeSectionFrameCurrent_restrictChart_reading
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X) :
    let P := nativeSectionFramePresentation L hL s hdense E
    (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (nativeSectionDivisorMetric L hL s hdense)).restrictChart c (P.chartDomain_le c) =
        toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
          (DivisorIntegrationCurrent.divisorCurrent
            (P.differentiableOn_chartG c ⟨0, by change 0 < 1; omega⟩)
            (P.frequently_chartG_ne c ⟨0, by change 0 < 1; omega⟩)) := by
  let P := nativeSectionFramePresentation L hL s hdense E
  let b := canonicalBasis (m + 1)
  let k := degreeTwo (Nat.succ_pos m)
  let T := integrationCurrent b (Nat.succ_pos m) (nativeSectionDivisorMetric L hL s hdense)
  have hfrom : fromLocalCurrent b k (T.restrictChart c (P.chartDomain_le c)) =
      restrictForm (T.coefficients b c) (P.chartDomain_le c) := by
    ext v φ
    exact GlobalCurrent.coefficients_restrictChart b T c (P.chartDomain_le c) v φ
  have hread := hfrom.trans (nativeSectionFrameCurrent_coefficient_reading L hL s hdense E c)
  exact (CurrentPairing.toLocalCurrent_fromLocalCurrent b k
    (T.restrictChart c (P.chartDomain_le c))).symm.trans
      (congrArg (toLocalCurrent b k) hread)

/-- The actual complete original native current action is its SAME literal
signed-shuffle Hausdorff area integral of its SAME physical frame equation. -/
theorem nativeSectionFrameCurrent_area_action
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X) :
    let P := nativeSectionFramePresentation L hL s hdense E
    ∀ η : TestForm (P.chartDomain c) (Module.finrank ℝ (ComplexModel (m + 1)) - 2),
      (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (nativeSectionDivisorMetric L hL s hdense)).restrictChart c (P.chartDomain_le c) η =
          ∫ x, divisorShuffleDensity
              (P.chartG c ⟨0, by change 0 < 1; omega⟩)
              (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η x
            ∂(μHE[2 * (m + 1) - 2] : Measure (ComplexModel (m + 1))) := by
  let P := nativeSectionFramePresentation L hL s hdense E
  dsimp only
  intro η
  rw [nativeSectionFrameCurrent_restrictChart_reading L hL s hdense E c]
  exact divisorCurrent_wedgePairing_eq_integral _ _ _ η

end SGPT.Projective.NumEq.CompleteIntersections
