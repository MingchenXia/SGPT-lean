import SGPT.PSH.HermitianComparisonBackgroundTorsion
import SGPT.PSH.HermitianPureTraceSelectedReadback

/-! # The actual closed residual factors retain their ordinary BT traces -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonResidualTrace

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorCollar LocalBedfordTaylorForms
open HermitianComparisonOneFactor HermitianPureTraceReadback
open scoped Topology ContDiff Distributions

/-- Degree transport preserves the actual ordinary trace measure. -/
theorem traceMeasure_castLPC {n a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (T : LocalProductCurrent n U a) (hT : IsPositive T) :
    (isPositive_castLPC hab hT).traceMeasure = hT.traceMeasure := by
  cases hab
  rfl

/-- Equality of positive currents preserves their actual ordinary trace. -/
theorem traceMeasure_congr {n q : ℕ} {U : Opens (ComplexModel n)}
    {S T : LocalProductCurrent n U q} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : hS.traceMeasure = hT.traceMeasure := by
  cases heq
  rfl

/-- The closed factor of a residual subset is literally the ordinary BT
product of those selected corrected potentials and the original unit base. -/
theorem backgroundResidual_unit_traceMeasure {n p : ℕ} {U : Opens (ComplexModel n)}
    (hdeg : 1 + p = n) (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    (backgroundResidual p (oneCurrentOf (U := U) hdeg)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) v hv hσ s).positive.traceMeasure =
    (isPositive_btProduct s.card (1 + (p - s.card))
      (fun i => v (s.orderEmbOfFin rfl i))
      (oneCurrentOf (U := U) (by
        have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
        omega : 1 + (p - s.card) + s.card = n))
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun i => hv _)).1.traceMeasure := by
  classical
  unfold backgroundResidual
  dsimp only
  rw [traceMeasure_castLPC]
  apply traceMeasure_congr
  rw [cast_oneCurrentOf]
  exact (isPositive_btProduct _ _ _ _
    (isPositive_castLPC _ (isPositive_oneCurrentOf _))
    (isClosedAny_castLPC _ (isClosedAny_oneCurrentOf _)) (fun i => hv _)).1

end SGPT.PSH.HermitianComparisonResidualTrace
