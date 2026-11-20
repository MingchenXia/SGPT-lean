import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Polynomial
open scoped Topology

namespace SGPT.Foundations.Schemes

/-- Natural-argument actual polynomial evaluation divided by the bounding
power tends to the actual coefficient at that power, including zero. -/
theorem polynomial_eval_div_pow_tendsto_coeff (P : Polynomial ℝ) (n : ℕ)
    (hP : P.natDegree ≤ n) :
    Tendsto (fun m : ℕ ↦ P.eval (m : ℝ) / (m : ℝ) ^ n) atTop (𝓝 (P.coeff n)) := by
  by_cases hz : P = 0
  · simp [hz]
  let Q : Polynomial ℝ := X ^ n
  have hQ : Q ≠ 0 := pow_ne_zero _ X_ne_zero
  by_cases hlt : P.natDegree < n
  · have hd : P.degree < Q.degree := by
      rw [degree_eq_natDegree hz]
      simp only [Q, degree_X_pow]
      exact_mod_cast hlt
    have ht := (P.div_tendsto_atTop_zero_of_degree_lt Q hd).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Q, Function.comp_def, coeff_eq_zero_of_natDegree_lt hlt] using ht
  · have heq : P.natDegree = n := by omega
    have hd : P.degree = Q.degree := by
      rw [degree_eq_natDegree hz]
      simp only [Q, degree_X_pow, heq]
    have ht := (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq Q hd).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Q, Function.comp_def, ← heq] using ht

/-- Actual eventual polynomial inequalities preserve coefficients at a
common genuine degree bound. No leading-sign certificate is assumed. -/
theorem polynomial_coeff_le_of_eventually_eval_le (P Q : Polynomial ℝ) (n : ℕ)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (hPQ : ∀ᶠ m : ℕ in atTop, P.eval (m : ℝ) ≤ Q.eval (m : ℝ)) :
    P.coeff n ≤ Q.coeff n := by
  apply le_of_tendsto_of_tendsto (polynomial_eval_div_pow_tendsto_coeff P n hP)
    (polynomial_eval_div_pow_tendsto_coeff Q n hQ)
  filter_upwards [hPQ] with m hm
  exact div_le_div_of_nonneg_right hm (pow_nonneg (Nat.cast_nonneg _) _)

/-- Translation preserves the actual coefficient at a genuine upper degree
bound, even if the original polynomial has smaller degree or is zero. -/
theorem polynomial_comp_X_add_C_coeff_of_natDegree_le (P : Polynomial ℝ) (n : ℕ)
    (a : ℝ) (hP : P.natDegree ≤ n) :
    (P.comp (X + C a)).coeff n = P.coeff n := by
  have hd : (P.comp (X + C a)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  by_cases heq : P.natDegree = n
  · calc
      (P.comp (X + C a)).coeff n = (P.comp (X + C a)).leadingCoeff := by
        rw [← heq, ← hd, coeff_natDegree]
      _ = P.leadingCoeff := by
        rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact Nat.one_ne_zero),
          leadingCoeff_X_add_C, one_pow, mul_one]
      _ = P.coeff n := by rw [← heq, coeff_natDegree]
  · have hlt : P.natDegree < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hlt), coeff_eq_zero_of_natDegree_lt hlt]

end SGPT.Foundations.Schemes
