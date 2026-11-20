import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false

/-! # Strict monotone row diagonals with actual vanishing metric errors -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NativeRowDiagonalSelection

noncomputable section

/-- Moving row targets admit a strict natural-number diagonal with
actual errors bounded by any prescribed positive vanishing tolerance. -/
theorem exists_strictMono_diagonal_of_tendsto_rows
    {A : Type*} [PseudoMetricSpace A] (w : ℕ → ℕ → A) (v : ℕ → A)
    (hrows : ∀ j, Tendsto (w j) atTop (𝓝 (v j)))
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ Tendsto k atTop atTop ∧
      (∀ j, dist (w j (k j)) (v j) < ε j) ∧
      Tendsto (fun j => dist (w j (k j)) (v j)) atTop (𝓝 0) := by
  classical
  have hthreshold (j : ℕ) : ∃ N : ℕ, ∀ l : ℕ, N ≤ l → dist (w j l) (v j) < ε j :=
    eventually_atTop.mp ((Metric.tendsto_nhds.mp (hrows j)) (ε j) (hε j))
  choose N hN using hthreshold
  let k : ℕ → ℕ := Nat.rec (N 0) (fun j old => max (N (j + 1)) (old + 1))
  have hstep (j : ℕ) : k j < k (j + 1) :=
    (Nat.lt_succ_self (k j)).trans_le (le_max_right (N (j + 1)) (k j + 1))
  have hk : StrictMono k := strictMono_nat_of_lt_succ hstep
  have hbound (j : ℕ) : N j ≤ k j := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left (N (j + 1)) (k j + 1)
  have hclose (j : ℕ) : dist (w j (k j)) (v j) < ε j := hN j (k j) (hbound j)
  exact ⟨k, hk, hk.tendsto_atTop, hclose,
    squeeze_zero (fun _ => dist_nonneg) (fun j => (hclose j).le) hεlim⟩

end
end SGPT.Foundations.Analysis.Pending.NativeRowDiagonalSelection
