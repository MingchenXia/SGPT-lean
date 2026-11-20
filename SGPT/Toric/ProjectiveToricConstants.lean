import SGPT.Toric.ProjectiveToricOrder
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex

/-- The original finite constant adds literally to the corrected descent. -/
theorem projectiveToricCorrectedDescent_add_const
    (u : Projectivization ℂ (Fin 2 → ℂ) → EReal) (C : ℝ) :
    projectiveToricCorrectedDescent (fun p ↦ u p + (C : EReal)) =
      fun x ↦ projectiveToricCorrectedDescent u x + (C : EReal) := by
  funext x
  exact add_right_comm _ (C : EReal) (projectiveLineLogPartition (x 0) : EReal)

/-- The literal original Legendre function subtracts the same finite constant,
with all original infinite values retained. -/
theorem projectiveToricLegendre_add_const
    (u : Projectivization ℂ (Fin 2 → ℂ) → EReal) (C : ℝ) :
    projectiveToricLegendre (fun p ↦ u p + (C : EReal)) =
      fun y ↦ projectiveToricLegendre u y - (C : EReal) := by
  funext y
  let B := innerₗ (EuclideanSpace ℝ (Fin 1))
  let f := projectiveToricCorrectedDescent u
  have hcost (x : EuclideanSpace ℝ (Fin 1)) :
      (B x y : EReal) - (f x + (C : EReal)) =
        ((B x y : EReal) - f x) - (C : EReal) := by
    simpa only [add_zero, zero_add, zero_sub, sub_eq_add_neg] using
      (EReal.add_sub_add_comm (a := (B x y : EReal)) (b := 0)
        (c := f x) (d := (C : EReal)) (.inr (EReal.coe_ne_top C))
        (.inr (EReal.coe_ne_bot C)))
  simp only [projectiveToricLegendre, projectiveToricCorrectedDescent_add_const, conjugate]
  change (⨆ x, (B x y : EReal) - (f x + (C : EReal))) =
    (⨆ x, (B x y : EReal) - f x) - (C : EReal)
  simp_rw [hcost]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    SGPT.Foundations.Analysis.FirstPass.iSup_add_coe
      (fun x ↦ (B x y : EReal) - f x) (-C)

end SGPT.Toric
