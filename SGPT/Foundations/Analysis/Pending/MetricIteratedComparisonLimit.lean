import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

/-! # Three actual limits of a continuous metric comparison -/

open Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.MetricIteratedComparisonLimit

/-- Three genuine limits of continuous comparisons force zero distance,
without requiring separation of the ambient pseudometric space. -/
theorem dist_eq_zero_of_iterated_comparison
    {X : Type*} [PseudoMetricSpace X] {a b : ℕ → X} {A B : X}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (Q : ℕ → X → X) (hQ : ∀ m, Continuous (Q m))
    (hQA : Tendsto (fun m => Q m A) atTop (𝓝 A))
    (hbound : ∀ m j, ∀ᶠ k in atTop, dist (a k) (b k) ≤ dist (a k) (Q m (a j))) :
    dist A B = 0 := by
  have hfirst (m j : ℕ) : dist A B ≤ dist A (Q m (a j)) :=
    le_of_tendsto_of_tendsto (ha.dist hb) (ha.dist tendsto_const_nhds) (hbound m j)
  have hsecond (m : ℕ) : dist A B ≤ dist A (Q m A) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_const_nhds.dist ((hQ m).tendsto A |>.comp ha))
      (Eventually.of_forall (hfirst m))
  have hzero : dist A B ≤ dist A A :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_const_nhds.dist hQA) (Eventually.of_forall hsecond)
  exact le_antisymm (by simpa only [dist_self] using hzero) dist_nonneg

end SGPT.Foundations.Analysis.Pending.MetricIteratedComparisonLimit
