import SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar

set_option autoImplicit false

/-! # A genuinely produced positive local quadratic smooth correction

The operator-norm bound, positive coefficient and small actual ball
are produced from the original local smoothness, including complex zero.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalBedfordTaylorCollar
  KahlerDomination SmoothPotentialDomination

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Local smoothness itself produces a positive quadratic and the genuine
PSH corrected function on an actual smaller ball. -/
theorem exists_positive_quadratic_correction
    {b : ComplexModel n → ℝ} (hb : ContDiffOn ℝ ∞ b U)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ball z₀ r ⊆ (U : Set (ComplexModel n)) ∧
      PlurisubharmonicOn (fun z => (ballPot A z₀ 0 z : EReal)) (ball z₀ r) ∧
      PlurisubharmonicOn (fun z => ((b z + ballPot A z₀ 0 z : ℝ) : EReal))
        (ball z₀ r) := by
  obtain ⟨K, hK, hzK, hKU⟩ := exists_compact_subset U.isOpen hz₀
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_ddcForm hb).continuousOn.mono hKU)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ (interior_subset hzK))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hzK
  have hballU : ball z₀ r ⊆ (U : Set (ComplexModel n)) :=
    fun _ hz => hKU (interior_subset (hball hz))
  let A := Real.pi * (C + 1)
  have hA : 0 < A := mul_pos Real.pi_pos (by linarith)
  have hq : ContDiff ℝ ∞ (ballPot A z₀ 0) := contDiff_ballPot A z₀ 0
  have hqdiag (z v : ComplexModel n) :
      smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] = (C + 1) * ‖v‖ ^ 2 := by
    rw [smoothDDC_complexDiagonal_eq_leviForm
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      leviForm_ballPot]
    dsimp only [A]
    field_simp
  refine ⟨A, r, hA, hr, hballU, ?_, ?_⟩
  · exact plurisubharmonicOn_coe_of_smoothDDC_nonneg isOpen_ball hq.contDiffOn
      (fun z _ v => by rw [hqdiag]; positivity)
  · have hbb : ContDiffOn ℝ ∞ b (ball z₀ r) := hb.mono hballU
    apply plurisubharmonicOn_coe_of_smoothDDC_nonneg isOpen_ball
      (hbb.add hq.contDiffOn)
    intro z hz v
    rw [smoothDDC_add isOpen_ball hbb hq.contDiffOn hz,
      ContinuousAlternatingMap.add_apply, hqdiag]
    have hnorm : ‖smoothDDC b z‖ ≤ C := hC z (interior_subset (hball hz))
    have hlow := neg_norm_mul_le_lineValue (smoothDDC b z) v
    have hbound : ‖smoothDDC b z‖ * ‖v‖ ^ 2 ≤ C * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)
    nlinarith [sq_nonneg ‖v‖]

end SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection
