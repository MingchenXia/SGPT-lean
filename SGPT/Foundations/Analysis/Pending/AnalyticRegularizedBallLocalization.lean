import SGPT.Foundations.Analysis.Pending.AnalyticGeneratorLocalGrowth

set_option autoImplicit false

/-! # Actual holomorphic poles produce uniform regularized-ball neighborhoods -/

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallLocalization

open FirstPass

noncomputable section

/-- Actual holomorphic regularity, a literal pole, and openness internally
produce a common neighborhood and all sufficiently small regularized balls. -/
theorem exists_uniform_regularized_balls
    {n N : ℕ} {g : Fin N → ComplexModel n → ℂ} {x : ComplexModel n}
    (hg : HolomorphicGeneratorsAt g x) (hpole : generatorNormSq g x = 0)
    {B : Set (ComplexModel n)} (hB : IsOpen B) (hxB : x ∈ B) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧ U ⊆ B ∧
      ∃ η₀ A : ℝ, 0 < η₀ ∧ 0 < A ∧ ∀ y ∈ U, ∀ η ∈ Ioo 0 η₀,
        0 < generatorNormSq g y + η ^ 2 ∧
        closedBall y (Real.sqrt (generatorNormSq g y + η ^ 2)) ⊆ B ∧
        ∀ z ∈ ball y (Real.sqrt (generatorNormSq g y + η ^ 2)),
          generatorNormSq g z ≤ A * (generatorNormSq g y + η ^ 2) := by
  classical
  obtain ⟨W, hW, hxW, K, hK, hquad⟩ :=
    AnalyticGeneratorLocalGrowth.exists_pos_quadratic_growth hg
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    ((hW.inter hB).mem_nhds ⟨hxW, hxB⟩)
  obtain ⟨D, hD, hxD, hgD⟩ := hg
  have hcontg (i : Fin N) : ContinuousAt (g i) x :=
    ((contDiffOn_of_differentiableOn_complex (hgD i) hD).contDiffAt
      (hD.mem_nhds hxD)).continuousAt
  have hcontF : ContinuousAt (generatorNormSq g) x := by
    unfold generatorNormSq
    exact tendsto_finsetSum _ fun i _ => (hcontg i).norm.pow 2
  have hsmall : {y : ComplexModel n | generatorNormSq g y < R ^ 2 / 16} ∈ 𝓝 x :=
    hcontF.eventually_lt continuousAt_const (by rw [hpole]; positivity)
  have hnear : ball x (R / 4) ∩ {y : ComplexModel n | generatorNormSq g y < R ^ 2 / 16} ∈ 𝓝 x :=
    inter_mem (ball_mem_nhds x (by positivity)) hsmall
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hnear
  have hyR {y : ComplexModel n} (hy : y ∈ U) : y ∈ ball x R := by
    have hd := mem_ball.mp (hUsub hy).1
    exact mem_ball.mpr (by linarith)
  refine ⟨U, hU, hxU, fun y hy => (hRsub (hyR hy)).2,
    R / 4, 2 + K, by positivity, by linarith, ?_⟩
  intro y hy η hη
  have hF : generatorNormSq g y < R ^ 2 / 16 := (hUsub hy).2
  have hηsq : η ^ 2 < (R / 4) ^ 2 := by nlinarith [hη.1, hη.2]
  have hS : 0 < generatorNormSq g y + η ^ 2 := by
    nlinarith [generatorNormSq_nonneg g y, sq_pos_of_pos hη.1]
  have hsqrt : Real.sqrt (generatorNormSq g y + η ^ 2) < R / 2 := by
    apply (Real.sqrt_lt hS.le (by positivity)).mpr
    nlinarith [sq_pos_of_pos hR]
  have hzR {z : ComplexModel n}
      (hz : z ∈ closedBall y (Real.sqrt (generatorNormSq g y + η ^ 2))) : z ∈ ball x R := by
    have hdzy := mem_closedBall.mp hz
    have hdyx := mem_ball.mp (hUsub hy).1
    exact mem_ball.mpr (by linarith [dist_triangle z y x])
  refine ⟨hS, fun z hz => (hRsub (hzR hz)).2, ?_⟩
  intro z hz
  have hzclosed := ball_subset_closedBall hz
  have hnorm : ‖z - y‖ ^ 2 ≤ generatorNormSq g y + η ^ 2 := by
    have hd : ‖z - y‖ ≤ Real.sqrt (generatorNormSq g y + η ^ 2) := by
      simpa only [dist_eq_norm] using mem_closedBall.mp hzclosed
    have hsq := Real.sq_sqrt hS.le
    nlinarith [norm_nonneg (z - y), Real.sqrt_nonneg (generatorNormSq g y + η ^ 2)]
  have hbase := hquad y (hRsub (hyR hy)).1 z (hRsub (hzR hzclosed)).1
  have hmul := mul_le_mul_of_nonneg_left hnorm hK.le
  nlinarith [sq_nonneg η]

end

end SGPT.Foundations.Analysis.Pending.AnalyticRegularizedBallLocalization
