import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Group.Bounded

/-! Finite Haar volume bounds the SAME closed full-dimensional convex body.
Blueprint: convex-finite-volume-bounded.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Metric MeasureTheory Bornology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {C : Set E}

theorem isBounded_of_isClosed_convex_interior_nonempty_measure_ne_top
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hinterior : (interior C).Nonempty) (hfinite : μ C ≠ ⊤) : IsBounded C := by
  obtain ⟨x, hx⟩ := hinterior
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hhalf : 0 < r / 2 := half_pos hr
  have hpositive : μ (ball (0 : E) (r / 2)) ≠ 0 := (measure_ball_pos μ 0 hhalf).ne'
  obtain ⟨K, _, hK, htail⟩ := hclosed.measurableSet.exists_isCompact_sdiff_lt hfinite hpositive
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine isBounded_iff_forall_norm_le.mpr ⟨2 * (r / 2 + R) + ‖x‖, fun y hy => ?_⟩
  let center : E := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hsmall : ball center (r / 2) ⊆ C := by
    intro w hw
    let z : E := (2 : ℝ) • w - y
    have hzw : z - x = (2 : ℝ) • (w - center) := by dsimp [z, center]; module
    have hz : z ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, hzw, norm_smul, Real.norm_eq_abs]
      have hdist : ‖w - center‖ < r / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hmid := hconvex (hball hz) hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have heq : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • y = w := by dsimp [z]; module
    exact heq ▸ hmid
  have hmeet : (ball center (r / 2) ∩ K).Nonempty := by
    by_contra hn
    have hsub : ball center (r / 2) ⊆ C \ K := by
      intro w hw
      exact ⟨hsmall hw, fun hwK => hn ⟨w, hw, hwK⟩⟩
    have hle := measure_mono (μ := μ) hsub
    rw [μ.addHaar_ball_center] at hle
    exact (not_lt_of_ge hle) htail
  obtain ⟨z, hzball, hzK⟩ := hmeet
  have hdist : ‖center - z‖ < r / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hzball
  have hcenter : ‖center‖ ≤ r / 2 + R :=
    (norm_le_norm_sub_add center z).trans (add_le_add hdist.le (hR z hzK))
  have hyexpr : y = (2 : ℝ) • center - x := by dsimp [center]; module
  calc
    ‖y‖ = ‖(2 : ℝ) • center - x‖ := congrArg norm hyexpr
    _ ≤ ‖(2 : ℝ) • center‖ + ‖x‖ := norm_sub_le _ _
    _ = 2 * ‖center‖ + ‖x‖ := by norm_num [norm_smul]
    _ ≤ 2 * (r / 2 + R) + ‖x‖ := by linarith

theorem isCompact_of_isClosed_convex_interior_nonempty_measure_ne_top
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hinterior : (interior C).Nonempty) (hfinite : μ C ≠ ⊤) : IsCompact C :=
  isCompact_iff_isClosed_bounded.mpr ⟨hclosed,
    isBounded_of_isClosed_convex_interior_nonempty_measure_ne_top μ hclosed hconvex hinterior hfinite⟩
end SGPT.Convex
