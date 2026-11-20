import Mathlib.GroupTheory.Perm.Fin

/-! # Exact slot reindexing for the nearby-trace recurrence -/

set_option autoImplicit false

namespace SGPT.PSH.HermitianBalayage

variable {α : Type*} {N : ℕ}

/-- A mixed tuple with an old-potential block, a new-potential block,
and the remaining Euclidean slots. -/
def mixedTuple (u v q : α) (j m : ℕ) : Fin N → α :=
  fun i => if (i : ℕ) < j then u else if (i : ℕ) < j + m then v else q

/-- Inserting the new potential at the block boundary restores one new slot. -/
theorem mixedTuple_insert_new (u v q : α) (j m : ℕ) (hjm : j + (m + 1) ≤ N + 1) :
    (⟨j, by omega⟩ : Fin (N + 1)).insertNth v (mixedTuple u v q j m : Fin N → α) =
      mixedTuple u v q j (m + 1) := by
  classical
  rw [Fin.insertNth_eq_iff]
  constructor
  · simp only [mixedTuple, Nat.lt_irrefl, if_false]
    rw [if_pos (by omega)]
  · funext i
    rw [Fin.removeNth_apply]
    by_cases hi : (i : ℕ) < j
    · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < ⟨j, by omega⟩ from hi)]
      simp only [mixedTuple, Fin.val_castSucc, hi, if_true]
    · rw [Fin.succAbove_of_le_castSucc _ _ (show (⟨j, by omega⟩ : Fin (N + 1)) ≤ i.castSucc by
        exact Nat.le_of_not_gt hi)]
      simp only [mixedTuple, Fin.val_succ]
      split_ifs <;> simp_all <;> omega

/-- Inserting the old potential instead advances its block by one. -/
theorem mixedTuple_insert_old (u v q : α) (j m : ℕ) (hjm : j + (m + 1) ≤ N + 1) :
    (⟨j, by omega⟩ : Fin (N + 1)).insertNth u (mixedTuple u v q j m : Fin N → α) =
      mixedTuple u v q (j + 1) m := by
  classical
  rw [Fin.insertNth_eq_iff]
  constructor
  · simp only [mixedTuple]
    rw [if_pos (by omega)]
  · funext i
    rw [Fin.removeNth_apply]
    by_cases hi : (i : ℕ) < j
    · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < ⟨j, by omega⟩ from hi)]
      simp only [mixedTuple, Fin.val_castSucc]
      rw [if_pos hi, if_pos (by omega)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (show (⟨j, by omega⟩ : Fin (N + 1)) ≤ i.castSucc by
        exact Nat.le_of_not_gt hi)]
      simp only [mixedTuple, Fin.val_succ]
      split_ifs <;> simp_all <;> omega

/-- Appending a Euclidean slot preserves the two potential blocks. -/
theorem mixedTuple_insert_flat_last (u v q : α) (j m : ℕ) (hjm : j + m ≤ N) :
    (Fin.last N).insertNth q (mixedTuple u v q j m : Fin N → α) =
      mixedTuple u v q j m := by
  classical
  rw [Fin.insertNth_eq_iff]
  constructor
  · simp only [mixedTuple, Fin.val_last]
    rw [if_neg (by omega), if_neg (by omega)]
  · funext i
    rw [Fin.removeNth_apply, Fin.succAbove_last]
    rfl

end SGPT.PSH.HermitianBalayage
