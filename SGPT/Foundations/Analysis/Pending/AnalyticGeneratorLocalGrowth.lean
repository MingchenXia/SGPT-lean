import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

/-! # Actual finite holomorphic generators internally supply local quadratic growth -/

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticGeneratorLocalGrowth

open FirstPass

noncomputable section

variable {n N : ℕ} {g : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}

/-- Actual several-variable holomorphic regularity and the finite family
internally produce a common neighborhood and a quadratic norm-square bound. -/
theorem exists_pos_quadratic_growth (hg : HolomorphicGeneratorsAt g x) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧ ∃ K : ℝ, 0 < K ∧
      ∀ y ∈ U, ∀ z ∈ U,
        generatorNormSq g z ≤ 2 * generatorNormSq g y + K * ‖z - y‖ ^ 2 := by
  classical
  obtain ⟨B, hB, hxB, hgB⟩ := hg
  have hsmooth (i : Fin N) : ContDiffAt ℂ 1 (g i) x :=
    ((contDiffOn_of_differentiableOn_complex (hgB i) hB).contDiffAt
      (hB.mem_nhds hxB)).of_le (by simp)
  choose L S hS hLip using fun i : Fin N => (hsmooth i).exists_lipschitzOnWith
  have hcommon : (⋂ i : Fin N, S i) ∈ 𝓝 x := Filter.iInter_mem.mpr hS
  obtain ⟨U, hUS, hU, hxU⟩ := _root_.mem_nhds_iff.mp hcommon
  let K : ℝ := 1 + 2 * ∑ i : Fin N, (L i : ℝ) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨U, hU, hxU, K, hK, ?_⟩
  intro y hy z hz
  have hyS (i : Fin N) : y ∈ S i := mem_iInter.mp (hUS hy) i
  have hzS (i : Fin N) : z ∈ S i := mem_iInter.mp (hUS hz) i
  have hterm (i : Fin N) : ‖g i z‖ ^ 2 ≤
      2 * ‖g i y‖ ^ 2 + 2 * (L i : ℝ) ^ 2 * ‖z - y‖ ^ 2 := by
    have hd : ‖g i z - g i y‖ ≤ (L i : ℝ) * ‖z - y‖ := by
      simpa only [dist_eq_norm] using (hLip i).dist_le_mul z (hzS i) y (hyS i)
    have hn : ‖g i z‖ ≤ ‖g i y‖ + (L i : ℝ) * ‖z - y‖ := by
      calc ‖g i z‖ ≤ ‖g i z - g i y‖ + ‖g i y‖ := by
            simpa only [sub_add_cancel] using norm_add_le (g i z - g i y) (g i y)
        _ ≤ _ := by linarith
    have hl : 0 ≤ (L i : ℝ) * ‖z - y‖ := mul_nonneg (L i).coe_nonneg (norm_nonneg _)
    nlinarith [norm_nonneg (g i z), norm_nonneg (g i y),
      sq_nonneg (‖g i y‖ - (L i : ℝ) * ‖z - y‖)]
  calc generatorNormSq g z
      ≤ ∑ i : Fin N, (2 * ‖g i y‖ ^ 2 + 2 * (L i : ℝ) ^ 2 * ‖z - y‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * generatorNormSq g y + (2 * ∑ i : Fin N, (L i : ℝ) ^ 2) * ‖z - y‖ ^ 2 := by
      simp only [generatorNormSq, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
    _ ≤ _ := by dsimp only [K]; nlinarith [sq_nonneg ‖z - y‖]

end

end SGPT.Foundations.Analysis.Pending.AnalyticGeneratorLocalGrowth
