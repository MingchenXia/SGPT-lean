import SGPT.Projective.DivisorCurrentShuffleArea
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials

/-! Exact original canonical divisor shuffle/normal wedge calibration,
including literal complementary casts. BP: `divisor-normal-shuffle-calibration.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms ConstantFormProducts TopDegreeDensity CanonicalCurrentFrame
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- The actual canonical divisor integrand is its genuine exterior-product
top density, for any actual pointwise normal-form reading. -/
theorem divisorShuffleDensity_eq_topDensity {m : ℕ} {Ω : Opens (ComplexModel (m + 1))}
    (g : ComplexModel (m + 1) → ℂ)
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel (m + 1)) - 2))
    (z : ComplexModel (m + 1)) (β : RealForm (m + 1) 2)
    (hβ : ∀ u v : ComplexModel (m + 1),
      β ![u, v] = DivisorIntegrationCurrent.divisorDensity g u v z) :
    divisorShuffleDensity g
      (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η z =
        topDensity (wedgeTo (by rw [complexModel_real_finrank]; omega :
          2 + (Module.finrank ℝ (ComplexModel (m + 1)) - 2) = 2 * (m + 1)) β (η z)) := by
  unfold divisorShuffleDensity
  refine (Finset.sum_congr rfl (fun s _ => ?_)).trans
    (CanonicalSmoothCurrentDensity.shuffleDensity_eq_topDensity
      (k := degreeTwo (Nat.succ_pos m)) β (η z))
  have hp : (fun i : Fin 2 => currentPairingBasis (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (s.out (Sum.inl i))) =
        ![currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
            (s.out (Sum.inl 0)),
          currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
            (s.out (Sum.inl 1))] := by
    funext i
    fin_cases i <;> rfl
  rw [hp, hβ]
  ring

/-- The SAME actual canonical shuffle in standard complementary degree,
with only the literal original degree equality undone. -/
theorem divisorShuffleDensity_eq_topDensity_standard {m : ℕ}
    {Ω : Opens (ComplexModel (m + 1))} (g : ComplexModel (m + 1) → ℂ)
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel (m + 1)) - 2))
    (z : ComplexModel (m + 1)) (β : RealForm (m + 1) 2)
    (hβ : ∀ u v : ComplexModel (m + 1),
      β ![u, v] = DivisorIntegrationCurrent.divisorDensity g u v z)
    (h : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) :
    divisorShuffleDensity g
      (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η z =
        topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
          β (castForm h.symm (η z))) := by
  refine (divisorShuffleDensity_eq_topDensity g η z β hβ).trans ?_
  apply congrArg (topDensity (n := m + 1))
  have hc := wedgeTo_castForm_right h
    (by rw [complexModel_real_finrank]; omega :
      2 + (Module.finrank ℝ (ComplexModel (m + 1)) - 2) = 2 * (m + 1))
    (by omega : 2 + 2 * m = 2 * (m + 1)) β (castForm h.symm (η z))
  simpa only [castForm_castForm, castForm_self] using hc

end SGPT.Projective.NumEq.CompleteIntersections
