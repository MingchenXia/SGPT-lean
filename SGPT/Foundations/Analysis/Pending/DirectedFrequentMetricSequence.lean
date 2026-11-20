import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Monotone near-limit sequences in a frequent directed subset -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.DirectedFrequentMetricSequence

noncomputable section

/-- A frequent directed subset supplies a monotone near-limit sequence;
no countable cofinality of the original directed preorder is assumed. -/
theorem exists_monotone_sequence_in_frequent_tendsto
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {Z : Type*} [PseudoMetricSpace Z] {f : I → Z} {z : Z}
    (hlim : Tendsto f atTop (𝓝 z)) (i₀ : I) {S : Set I}
    (hS : ∃ᶠ i in (atTop : Filter I), i ∈ S) :
    ∃ j : ℕ → I, Monotone j ∧ (∀ k, i₀ ≤ j k) ∧ (∀ k, j k ∈ S) ∧
      Tendsto (fun k => f (j k)) atTop (𝓝 z) := by
  classical
  have hub (a b : I) : ∃ c : I, a ≤ c ∧ b ≤ c := exists_ge_ge a b
  choose upper hleft hright using hub
  have hgood : ∀ a : I, ∃ b : I, a ≤ b ∧ b ∈ S := frequently_atTop.mp hS
  choose good hge hmem using hgood
  have hthreshold (k : ℕ) : ∃ a : I, ∀ b, a ≤ b → dist (f b) z < (1 / 2 : ℝ) ^ k :=
    eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) _ (pow_pos (by norm_num) k))
  choose threshold hclose using hthreshold
  let j : ℕ → I := Nat.rec (good (upper i₀ (threshold 0)))
    (fun k old => good (upper old (threshold (k + 1))))
  have hstep (k : ℕ) : j k ≤ j (k + 1) :=
    (hleft (j k) (threshold (k + 1))).trans (hge _)
  have hmono : Monotone j := monotone_nat_of_le_succ hstep
  have hi₀ : i₀ ≤ j 0 := (hleft i₀ (threshold 0)).trans (hge _)
  have hbound (k : ℕ) : threshold k ≤ j k := by
    cases k with
    | zero => exact (hright i₀ (threshold 0)).trans (hge _)
    | succ k => exact (hright (j k) (threshold (k + 1))).trans (hge _)
  have hjS (k : ℕ) : j k ∈ S := by
    cases k with
    | zero => exact hmem _
    | succ k => exact hmem _
  refine ⟨j, hmono, (fun k => hi₀.trans (hmono (Nat.zero_le k))), hjS, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hclose k (j k) (hbound k)).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

end
end SGPT.Foundations.Analysis.Pending.DirectedFrequentMetricSequence
