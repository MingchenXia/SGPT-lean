import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra

set_option autoImplicit false

/-!
# Polynomial coefficients from positive natural evaluations

The first-coefficient argument in Lu, arXiv:2005.04264v1, proof of
Theorem 1.2. Every coefficient is recovered from a finite polynomial
identity at all sufficiently large naturals, including degree one.
-/

namespace SGPT.Foundations.Analysis.Pending.PolynomialCoefficientRecovery

open Finset Polynomial

/-- All coefficients vanish when the finite polynomial expression vanishes
at every sufficiently large natural parameter. -/
theorem sum_coeff_eq_zero_of_forall_nat_ge {G : Type*} [Fintype G]
    (k : G → ℕ) (d : G → ℝ) (N0 : ℕ)
    (h : ∀ N : ℕ, N0 ≤ N → ∑ g, (N : ℝ) ^ k g * d g = 0) (r : ℕ) :
    ∑ g with k g = r, d g = 0 := by
  classical
  let p : ℝ[X] := ∑ g, C (d g) * X ^ k g
  have hroot (N : ℕ) (hN : N0 ≤ N) : p.IsRoot (N : ℝ) := by
    simp only [IsRoot, p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← h N hN]
    exact Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    have hnat : Set.Infinite ((fun N : ℕ => (N : ℝ)) '' Set.Ici N0) :=
      (Set.Ici_infinite N0).image Nat.cast_injective.injOn
    refine hnat.mono ?_
    rintro _ ⟨N, hN, rfl⟩
    exact hroot N hN
  have hp0 : p = 0 := p.eq_zero_of_infinite_isRoot hinf
  have hc := congrArg (fun q : ℝ[X] => q.coeff r) hp0
  simp only [p, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_filter]
  refine (Finset.sum_congr rfl fun g _ => ?_).trans hc
  simp only [eq_comm]

end SGPT.Foundations.Analysis.Pending.PolynomialCoefficientRecovery
