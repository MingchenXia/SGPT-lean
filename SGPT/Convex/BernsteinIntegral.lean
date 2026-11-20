import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open MeasureTheory

private theorem continuous_bernstein (n j : ℕ) :
    Continuous (fun t : ℝ => (bernsteinPolynomial ℝ n j).eval t) :=
  continuous_iff_continuousAt.mpr (fun t => (bernsteinPolynomial ℝ n j).hasDerivAt t |>.continuousAt)

private theorem adjacent_bernstein_integral (n j : ℕ) (hj : j < n) :
    (∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n j).eval t) =
      ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n (j + 1)).eval t := by
  have hder (t : ℝ) : HasDerivAt
      (fun s => (bernsteinPolynomial ℝ (n + 1) (j + 1)).eval s)
      (((n + 1 : ℕ) : ℝ) * ((bernsteinPolynomial ℝ n j).eval t -
        (bernsteinPolynomial ℝ n (j + 1)).eval t)) t := by
    simpa only [bernsteinPolynomial.derivative_succ_aux, Polynomial.eval_mul,
      Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_one, Nat.cast_add, Nat.cast_one] using
      (bernsteinPolynomial ℝ (n + 1) (j + 1)).hasDerivAt t
  have hcont : Continuous (fun t : ℝ => ((n + 1 : ℕ) : ℝ) *
      ((bernsteinPolynomial ℝ n j).eval t - (bernsteinPolynomial ℝ n (j + 1)).eval t)) :=
    continuous_const.mul ((continuous_bernstein n j).sub
      (continuous_bernstein n (j + 1)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t _ => hder t) (hcont.intervalIntegrable 0 1)
  have hne : j + 1 ≠ n + 1 := by omega
  simp only [bernsteinPolynomial.eval_at_0, bernsteinPolynomial.eval_at_1,
    hne, Nat.succ_ne_zero, ↓reduceIte, sub_zero] at he
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((continuous_bernstein n j).intervalIntegrable 0 1)
      ((continuous_bernstein n (j + 1)).intervalIntegrable 0 1)] at he
  have hp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  nlinarith

/-- Every actual Bernstein coefficient has integral exactly `1/(n+1)`, also
for dimension zero, by true polynomial differentiation and finite integration. -/
theorem integral_bernsteinPolynomial_eq (n j : ℕ) (hj : j ≤ n) :
    (∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n j).eval t) = 1 / (n + 1 : ℝ) := by
  have hconst : ∀ k : ℕ, k ≤ n →
      (∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n k).eval t) =
        ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n 0).eval t := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        exact (adjacent_bernstein_integral n k (by omega)).symm.trans (ih (by omega))
  have hsum (t : ℝ) : (∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval t) = 1 := by
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one] using
      congrArg (fun p : Polynomial ℝ => p.eval t) (bernsteinPolynomial.sum ℝ n)
  have hint : (∑ k ∈ Finset.range (n + 1),
      ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n k).eval t) = 1 := by
    rw [← intervalIntegral.integral_finsetSum (fun k _ =>
      (continuous_bernstein n k).intervalIntegrable 0 1)]
    simp_rw [hsum]
    norm_num
  have heq : (∑ k ∈ Finset.range (n + 1),
      ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n k).eval t) =
        ∑ _k ∈ Finset.range (n + 1), ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n 0).eval t := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hconst k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  rw [heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hint
  rw [hconst j hj]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith
end SGPT.Convex
