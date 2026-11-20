import SGPT.PSH.HermitianPureTraceReadback
import SGPT.PSH.HermitianComparisonLowerTrace

/-! # The actual selected lower currents retain their original global readers -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianPureTraceReadback

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorCollar LocalBedfordTaylorForms
open Hermitian HermitianGlobalProducts HermitianProducts
  HermitianComparisonLowerTrace HermitianComparisonTraceDomination

/-- Displayed native degree transport changes no actual Hermitian trace measure. -/
theorem powerTraceMeasure_castLPC {n a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (T : LocalProductCurrent n U a) (hT : IsPositive T)
    {omega : ComplexModel n → RealForm n 2} (homega : ContDiffOn ℝ ∞ omega U)
    (homegaP : ∀ z ∈ U, IsSemipositiveOneOne (omega z)) :
    powerTraceMeasure (castLPC hab T) (isPositive_castLPC hab hT) homega homegaP =
      powerTraceMeasure T hT homega homegaP := by
  cases hab
  rfl

/-- Equality of the original currents gives equality of their actual power traces. -/
theorem powerTraceMeasure_congr {n q : ℕ} {U : Opens (ComplexModel n)}
    {S T : LocalProductCurrent n U q} (hS : IsPositive S) (hT : IsPositive T)
    {omega : ComplexModel n → RealForm n 2} (homega : ContDiffOn ℝ ∞ omega U)
    (homegaP : ∀ z ∈ U, IsSemipositiveOneOne (omega z)) (heq : S = T) :
    powerTraceMeasure S hS homega homegaP = powerTraceMeasure T hT homega homegaP := by
  subst T
  rfl

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The literal selected subset current is precisely the original patch
current of the selected global potentials. Both degree casts act on the
actual unit current and finite expansion; no analytic assumption is used. -/
theorem selectedBackgroundCurrent_eq_currentOfDegree
    (P : BackgroundPatch omega) (p r : ℕ) (hdeg : r + p = m + 1)
    (u : Fin p → M → EReal) (s : Finset (Fin p)) :
    selectedBackgroundCurrent p r (fun i => P.correctedReal (u i)) P.residual_smooth
      (oneCurrentOf (U := P.geometry.domain) hdeg) s =
      P.currentOfDegree s.card (p - s.card + r) (by
        have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
        omega) (fun i => u (s.orderEmbOfFin rfl i)) := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  unfold selectedBackgroundCurrent
  dsimp only
  rw [cast_oneCurrentOf (n := m + 1) (by omega : r + p = r + (p - s.card) + s.card)
    hdeg (by omega)]
  exact cast_backgroundExpansion_unit (n := m + 1) (k := s.card)
    (by omega : r + (p - s.card) = p - s.card + r) (by omega) (by omega)
    (fun i => P.correctedReal (u (s.orderEmbOfFin rfl i))) P.residual_smooth

end SGPT.PSH.HermitianPureTraceReadback
