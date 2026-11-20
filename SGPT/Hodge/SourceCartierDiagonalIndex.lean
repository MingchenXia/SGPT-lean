import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false
noncomputable section

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Filter

/-- An internally chosen natural diagonal index, exceeding every row's
actual threshold while remaining a genuine strict subsequence. -/
def fastIndex (threshold : ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0
  | i+1 => max (fastIndex threshold i + 1) (threshold (i+1))

theorem fastIndex_ge (threshold : ℕ → ℕ) (i : ℕ) : threshold i ≤ fastIndex threshold i := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact le_max_right _ _

theorem fastIndex_strictMono (threshold : ℕ → ℕ) : StrictMono (fastIndex threshold) := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem fastIndex_tendsto (threshold : ℕ → ℕ) : Tendsto (fastIndex threshold) atTop atTop :=
  (fastIndex_strictMono threshold).tendsto_atTop

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
