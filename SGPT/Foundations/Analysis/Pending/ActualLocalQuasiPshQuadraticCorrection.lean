import SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection
import SGPT.Foundations.Analysis.FirstPass.QuasiPshSingularities

set_option autoImplicit false

/-! # A genuine positive correction of the original quasi-PSH reader

The local PSH decomposition and quadratic coefficient are internally
produced from the original nondegenerate quasi-PSH predicate.
-/

noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualLocalQuasiPshQuadraticCorrection
open FirstPass LocalBedfordTaylorCollar

variable {n : ℕ} {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}

/-- The original genuine quasi-PSH reader internally supplies a positive
quadratic, a genuine corrected PSH ball and its nonbottom point. -/
theorem exists_noncollapsed_positive_quadratic_correction
    (hu : LocalQuasiPshPotentialOn u U) {z : ComplexModel n} (hz : z ∈ U) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ball z r ⊆ U ∧
      PlurisubharmonicOn (fun x => u x + (ballPot A z 0 x : EReal)) (ball z r) ∧
      PlurisubharmonicOn (fun x => (ballPot A z 0 x : EReal)) (ball z r) ∧
      ∃ y ∈ ball z r, u y + (ballPot A z 0 y : EReal) ≠ ⊥ := by
  obtain ⟨p, h, ⟨P, hP, hzP, hp⟩, hh, heq⟩ := hu.2.1 z hz
  obtain ⟨S, hSsub, hS, hzS⟩ := _root_.mem_nhds_iff.mp (hh.and heq)
  let E : Opens (ComplexModel n) := ⟨U ∩ P ∩ S, (hu.1.inter hP).inter hS⟩
  have hzE : z ∈ E := ⟨⟨hz, hzP⟩, hzS⟩
  have hhE : ContDiffOn ℝ ∞ h E := fun x hx =>
    ((hSsub hx.2).1).contDiffWithinAt
  obtain ⟨A, r, hA, hr, hVE, hQ, hhQ⟩ :=
    ActualSmoothLocalQuadraticCorrection.exists_positive_quadratic_correction hhE hzE
  have hVU : ball z r ⊆ U := fun x hx => (hVE hx).1.1
  have hpV : PlurisubharmonicOn p (ball z r) :=
    (hp.plurisubharmonicOn hP).mono (fun x hx => (hVE hx).1.2)
  have hsum := hpV.add hhQ
  have hcorrected :
      PlurisubharmonicOn (fun x => u x + (ballPot A z 0 x : EReal)) (ball z r) := by
    intro x hx
    apply (hsum x hx).congr
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    rw [(hSsub (hVE hy).2).2, EReal.coe_add, add_assoc]
  obtain ⟨y, hy, huy⟩ := hu.2.2 z hz (ball z r) isOpen_ball (mem_ball_self hr)
  refine ⟨A, r, hA, hr, hVU, hcorrected, hQ, y, hy.2, ?_⟩
  exact EReal.add_ne_bot_iff.mpr ⟨huy, EReal.coe_ne_bot _⟩

end SGPT.Foundations.Analysis.Pending.ActualLocalQuasiPshQuadraticCorrection
