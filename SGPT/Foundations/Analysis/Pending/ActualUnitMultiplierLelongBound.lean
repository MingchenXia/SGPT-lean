import SGPT.Foundations.Analysis.Pending.ActualMultiplierLogarithmicExponent
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

set_option autoImplicit false

/-! # Actual unit multiplier membership bounds the manifold Lelong number -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound

open FirstPass FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves
  LelongNumberChartTransport

noncomputable section

/-- Each actual admissible logarithmic exponent is controlled by the preferred-chart
unit multiplier integral, so its supremum is bounded by the true real dimension. -/
theorem lelongNumber_le_of_unit_multiplierIdeal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (hn : 0 < n) {u : M → EReal} {c : ℝ} {x : M}
    (hmem : (multiplierIdeal (n := n) c u).mem x (fun _ => (1 : ℂ))) :
    lelongNumber (n := n) u x ≤
      ENNReal.ofReal ((Module.finrank ℝ (ComplexModel n) : ℝ) / c) := by
  classical
  let : Nontrivial (ComplexModel n) := by
    refine ⟨⟨0, EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ), ?_⟩⟩
    intro hEq
    have hnorm : ‖(EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ) : ComplexModel n)‖ = 1 := by
      simp
    rw [← hEq] at hnorm
    simp at hnorm
  apply lelongNumber_le_ofReal (n := n) (u := u) (x := x)
  intro γ hγ
  obtain ⟨C, hlog⟩ := hγ
  obtain ⟨R, hR, hbound⟩ := exists_chart_radius_of_eventually (n := n) hlog
  let e := complexChartAt (n := n) x
  have hcLog : ∀ᶠ z in 𝓝[≠] (e.val x),
      chartFunction u e z ≤ (((γ : ℝ) * Real.log ‖z - e.val x‖ + C : ℝ) : EReal) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz hzx
    have hnorm : 0 < ‖z - e.val x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    obtain ⟨hzt, hb⟩ := hbound z hnorm (by simpa only [mem_ball, dist_eq_norm] using hz)
    change u (e.val.symm z) ≤
      (((γ : ℝ) * Real.log ‖e.val (e.val.symm z) - e.val x‖ + C : ℝ) : EReal) at hb
    rw [e.val.right_inv hzt] at hb
    exact hb
  exact (ActualMultiplierLogarithmicExponent.logarithmic_exponent_lt_finrank_div_of_unit_multiplier
    volume hmem.2 hcLog).le

end

end SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
