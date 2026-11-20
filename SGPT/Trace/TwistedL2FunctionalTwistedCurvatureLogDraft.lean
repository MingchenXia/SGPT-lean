import SGPT.Trace.TwistedL2FunctionalTwistedAdjointYoungDraft

/-!
# Exact logarithmic-twist curvature identity

Pointwise support for the twisted L² argument. This establishes the local curvature algebra
independently of any BKN statement: after the shift p − log a, the a⁻¹ term
in the true Young error cancels the logarithmic Levi correction and leaves
exactly the original `twistedCurvature` with b⁻¹. The global analytic BKN
and all integration/domain steps remain unproved.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2.FunctionalTwistedCurvatureLogDraft

open Set Filter MeasureTheory Bundle Complex
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

variable {n : ℕ}

/-- Exact Levi identity for the actual log-shifted local weight. -/
theorem leviForm_sub_log (p a : ComplexModel n → ℝ) {z : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p z) (ha : ContDiffAt ℝ 2 a z) (ha0 : 0 < a z)
    (v : ComplexModel n) :
    a z * leviForm (fun w => p w - Real.log (a w)) z v =
      a z * leviForm p z v - leviForm a z v + holDerivSq a z v / a z := by
  have hlog : ContDiffAt ℝ 2 (fun w => Real.log (a w)) z :=
    (Real.contDiffAt_log.mpr ha0.ne').comp z ha
  have heq : (fun w => p w - Real.log (a w)) = p + (-(fun w => Real.log (a w))) := by
    funext w
    simp [sub_eq_add_neg]
  rw [heq]
  change a z * leviForm (p + (fun w => -Real.log (a w))) z v = _
  rw [leviForm_add hp hlog.neg]
  change a z * (leviForm p z v + leviForm (-(fun w => Real.log (a w))) z v) = _
  rw [leviForm_neg, leviForm_log_of_pos ha ha0]
  unfold holDerivSq
  field_simp [ha0.ne']
  ring

/-- The true book curvature is exactly the log-shifted Levi expression minus
the actual Young error. The b≠0 hypothesis is the original positivity premise. -/
theorem twistedCurvature_eq_log_shift_sub_young
    (p a b : ComplexModel n → ℝ) {z : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p z) (ha : ContDiffAt ℝ 2 a z)
    (ha0 : 0 < a z) (hb0 : 0 < b z) (v : ComplexModel n) :
    twistedCurvature a b p z v =
      a z * leviForm (fun w => p w - Real.log (a w)) z v -
        ((a z)⁻¹ + (b z)⁻¹) * holDerivSq a z v := by
  rw [leviForm_sub_log p a hp ha ha0]
  unfold twistedCurvature
  field_simp [ha0.ne', hb0.ne']
  ring

end SGPT.Trace.TwistedL2.FunctionalTwistedCurvatureLogDraft
