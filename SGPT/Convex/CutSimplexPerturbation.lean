import SGPT.Convex.CutSimplexCompact

/-! Genuine feasible two-sided perturbations and exclusion of nonvertices.
No support-cardinality, sparse optimizer or extreme-point classification
certificate is accepted. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.CutSimplex

open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

/-- Every direction supported on strictly positive coordinates admits both
small feasible signs when it preserves the active barycentre, or when
there is actual barycentre slack. -/
theorem exists_small_feasible_perturbations (τ : ι → ℝ) (s : ℝ)
    {w d : ι → ℝ} (hw : w ∈ cut τ s) (hdSum : ∑ i, d i = 0)
    (hdSupport : ∀ i, d i ≠ 0 → 0 < w i)
    (hb : objective τ d = 0 ∨ s < objective τ w) :
    ∃ ε : ℝ, 0 < ε ∧ w + ε • d ∈ cut τ s ∧ w - ε • d ∈ cut τ s := by
  have hi (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ w i + t * d i := by
    by_cases hdi : d i = 0
    · exact Filter.Eventually.of_forall fun t => by simpa only [hdi, mul_zero, add_zero] using hw.1.1 i
    · have ho : IsOpen {t : ℝ | 0 < w i + t * d i} :=
        isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const _))
      have hzero : (0 : ℝ) ∈ {t : ℝ | 0 < w i + t * d i} := by
        simpa only [mem_ofPred_eq, zero_mul, add_zero] using hdSupport i hdi
      filter_upwards [ho.mem_nhds hzero] with t ht
      exact ht.le
  have hcoords : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ w i + t * d i :=
    Filter.eventually_all.mpr hi
  have hbary : ∀ᶠ t : ℝ in 𝓝 0, s ≤ objective τ w + t * objective τ d := by
    rcases hb with hz | hs
    · exact Filter.Eventually.of_forall fun t => by
        simpa only [mem_ofPred_eq, hz, mul_zero, add_zero] using hw.2
    · have ho : IsOpen {t : ℝ | s < objective τ w + t * objective τ d} :=
        isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const _))
      have hzero : (0 : ℝ) ∈ {t : ℝ | s < objective τ w + t * objective τ d} := by
        simpa only [mem_ofPred_eq, zero_mul, add_zero] using hs
      filter_upwards [ho.mem_nhds hzero] with t ht
      exact ht.le
  have hfeas : ∀ᶠ t : ℝ in 𝓝 0, w + t • d ∈ cut τ s := by
    filter_upwards [hcoords, hbary] with t hc hb
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact hc i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hw.1.2, hdSum, mul_zero, add_zero]
    · simpa only [mem_ofPred_eq, map_add, map_smul, smul_eq_mul] using hb
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hfeas
  have hp : w + (δ / 2) • d ∈ cut τ s := hball (show δ / 2 ∈ Metric.ball 0 δ from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ)
  have hn : w + (-(δ / 2)) • d ∈ cut τ s := hball (show -(δ / 2) ∈ Metric.ball 0 δ from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ)
  exact ⟨δ / 2, half_pos hδ, hp, by simpa only [neg_smul, sub_eq_add_neg] using hn⟩

/-- An actual nonzero feasible two-sided direction rules out extremeness.
The midpoint decomposition and its distinctness are produced explicitly. -/
theorem not_extreme_of_supported_direction (τ : ι → ℝ) (s : ℝ)
    {w d : ι → ℝ} (hw : w ∈ cut τ s) (hd : d ≠ 0) (hdSum : ∑ i, d i = 0)
    (hdSupport : ∀ i, d i ≠ 0 → 0 < w i)
    (hb : objective τ d = 0 ∨ s < objective τ w) :
    w ∉ (cut τ s).extremePoints ℝ := by
  intro hext
  obtain ⟨ε, hε, hp, hn⟩ := exists_small_feasible_perturbations τ s hw hdSum hdSupport hb
  have hm : w ∈ openSegment ℝ (w + ε • d) (w - ε • d) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := hext.2 hp hn hm
  apply hd
  funext i
  have hi := congrFun he i
  change w i + ε * d i = w i at hi
  have hz : ε * d i = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left hε.ne'

end SGPT.Convex.CutSimplex
