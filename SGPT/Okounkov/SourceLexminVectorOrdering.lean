import SGPT.Okounkov.ValuativeFirstCoordinate

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.SourceLexmin

/-- Prefixing the SAME real head preserves the actual finite-vector
lexicographic order, including a genuinely empty tail. -/
theorem toLex_cons_le_cons {m : ℕ} (a : ℝ) {x y : Fin m → ℝ}
    (h : toLex x ≤ toLex y) :
    toLex (Fin.cons a x : Fin (m + 1) → ℝ) ≤ toLex (Fin.cons a y : Fin (m + 1) → ℝ) := by
  rcases h.lt_or_eq with hlt | heq
  · apply le_of_lt
    obtain ⟨i, hi, hxy⟩ := hlt
    refine ⟨i.succ, ?_, ?_⟩
    · intro j hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · change a = a
        rfl
      · change x k = y k
        exact hi k (Fin.succ_lt_succ_iff.mp hj)
    · change x i < y i
      exact hxy
  · rw [toLex_inj] at heq
    rw [heq]

/-- A strict first-coordinate increase gives the original lex comparison;
there are no hidden finiteness or positive-tail-dimension assumptions. -/
theorem toLex_cons_lt_cons_of_head_lt {m : ℕ} {a b : ℝ}
    (hab : a < b) (x y : Fin m → ℝ) :
    toLex (Fin.cons a x : Fin (m + 1) → ℝ) < toLex (Fin.cons b y : Fin (m + 1) → ℝ) := by
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact (not_lt_of_ge (Fin.zero_le j) hj).elim
  · change a < b
    exact hab

end SGPT.Okounkov.SourceLexmin
