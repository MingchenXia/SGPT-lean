import SGPT.PSH.HermitianComparisonTraceAlgebra

/-!
# Pure-trace absorption with a global finite error sum

For constant competitors every torsion error is a lower pure trace. A
single finite sum bounds every selected trace, so telescoping absorbs all
errors at once without triangular selected-index bookkeeping.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonPureErrorAbsorption

open Finset

theorem le_add_mul_of_adjacent {a : ℕ → ℝ} {ε : ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hstep : ∀ k, m ≤ k → k < n → a k ≤ a (k + 1) + ε) :
    a m ≤ a n + (n - m : ℕ) * ε := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      have hprevious : ∀ k, m ≤ k → k < n → a k ≤ a (k + 1) + ε :=
        fun k hmk hkn => hstep k hmk (Nat.lt_trans hkn (Nat.lt_succ_self n))
      calc
        a m ≤ a n + (n - m : ℕ) * ε := ih hprevious
        _ ≤ (a (n + 1) + ε) + (n - m : ℕ) * ε :=
          add_le_add (hstep n hmn (Nat.lt_succ_self n)) (le_refl _)
        _ = a (n + 1) + (n + 1 - m : ℕ) * ε := by
          rw [Nat.succ_sub hmn, Nat.cast_succ]
          ring

theorem two_mul_nat_le_four_pow (n : ℕ) : 2 * (n : ℝ) ≤ (4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Absorption of the actual finite lower-trace budget needs no rank bound
relative to the replacement step: only that every error is a lower trace.
This is the scalar final step of the constant-competitor mass argument. -/
theorem zero_le_four_pow_mul_top {n : ℕ} (hn : 0 < n) {a : ℕ → ℝ} {ε : ℝ}
    (ha : ∀ k, k ≤ n → 0 ≤ a k) (hε : 0 ≤ ε)
    (hsmall : ε * (n : ℝ) ^ 2 ≤ (1 / 2 : ℝ))
    (hrec : ∀ k, k < n → a k ≤ a (k + 1) + ε * ∑ h ∈ range n, a h) :
    a 0 ≤ (4 : ℝ) ^ n * a n := by
  let S : ℝ := ∑ h ∈ range n, a h
  have hS : 0 ≤ S := sum_nonneg fun k hk => ha k (mem_range.mp hk).le
  have herr : 0 ≤ ε * S := mul_nonneg hε hS
  have htel : ∀ k, k < n → a k ≤ a n + (n : ℝ) * (ε * S) := by
    intro k hk
    have h := le_add_mul_of_adjacent hk.le (fun j _ hj => hrec j hj)
    exact h.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.sub_le n k) herr))
  have hsum : S ≤ (n : ℝ) * (a n + (n : ℝ) * (ε * S)) := by
    have h := sum_le_sum (fun k hk => htel k (mem_range.mp hk))
    simpa only [sum_const, card_range, nsmul_eq_mul] using h
  have hsmallS := mul_le_mul_of_nonneg_right hsmall hS
  have hbound : S ≤ 2 * (n : ℝ) * a n := by nlinarith
  calc
    a 0 ≤ S := single_le_sum (fun k hk => ha k (mem_range.mp hk).le) (mem_range.mpr hn)
    _ ≤ 2 * (n : ℝ) * a n := hbound
    _ ≤ (4 : ℝ) ^ n * a n := mul_le_mul_of_nonneg_right (two_mul_nat_le_four_pow n) (ha n le_rfl)

end SGPT.PSH.HermitianComparisonPureErrorAbsorption
