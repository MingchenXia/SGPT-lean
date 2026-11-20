import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Monotone near-limit sequences inside each directed tail

Independent metric-basis adaptation for the tail reduction in SGPT
PDF0243. A sequence is not asserted cofinal in the original index set.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.DirectedMetricNearLimitSequences

noncomputable section

/-- Every directed tail contains a monotone sequence converging in the
target metric and lying in any given eventual subset. No cofinality is asserted. -/
theorem exists_monotone_sequence_in_tail_tendsto
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {Y : Type*} [PseudoMetricSpace Y] {f : I → Y} {v : Y}
    (hlim : Tendsto f atTop (𝓝 v)) (i₀ : I) {S : Set I} (hS : S ∈ (atTop : Filter I)) :
    ∃ j : ℕ → I, Monotone j ∧ (∀ k, i₀ ≤ j k) ∧ (∀ k, j k ∈ S) ∧
      Tendsto (fun k => f (j k)) atTop (𝓝 v) := by
  classical
  have hub (a b : I) : ∃ c : I, a ≤ c ∧ b ≤ c := exists_ge_ge a b
  choose upper hleft hright using hub
  obtain ⟨iS, hiS⟩ := mem_atTop_sets.mp hS
  have hthreshold (k : ℕ) : ∃ a : I, ∀ b, a ≤ b → dist (f b) v < (1 / 2 : ℝ) ^ k :=
    eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) _ (pow_pos (by norm_num) k))
  choose threshold hclose using hthreshold
  let j : ℕ → I := Nat.rec (upper i₀ (upper iS (threshold 0)))
    (fun k old => upper old (threshold (k + 1)))
  have hstep (k : ℕ) : j k ≤ j (k + 1) := hleft (j k) (threshold (k + 1))
  have hmono : Monotone j := monotone_nat_of_le_succ hstep
  have hi₀ : i₀ ≤ j 0 := hleft i₀ (upper iS (threshold 0))
  have hstart : iS ≤ j 0 :=
    (hleft iS (threshold 0)).trans (hright i₀ (upper iS (threshold 0)))
  have hbound (k : ℕ) : threshold k ≤ j k := by
    cases k with
    | zero => exact (hright iS (threshold 0)).trans (hright i₀ (upper iS (threshold 0)))
    | succ k => exact hright (j k) (threshold (k + 1))
  refine ⟨j, hmono, (fun k => hi₀.trans (hmono (Nat.zero_le k))),
    (fun k => hiS _ (hstart.trans (hmono (Nat.zero_le k)))), ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hclose k (j k) (hbound k)).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

end
end SGPT.Foundations.Analysis.Pending.DirectedMetricNearLimitSequences
