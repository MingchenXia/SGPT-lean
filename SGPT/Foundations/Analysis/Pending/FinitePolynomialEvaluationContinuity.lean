import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

/-! # Finite recovery of bounded-degree polynomial evaluation limits

Pure algebra/topology ingredient of SGPT PDF0235 Theorem 6.2.1.
Actual Lagrange interpolation produces the finite recovery formula.
No coefficient limit, distinguished-point limit, or countability is assumed.
-/

open Set Filter Polynomial
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.FinitePolynomialEvaluationContinuity

noncomputable section

private theorem eval_eq_sum_node_values {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (p : ℝ[X]) (hdegree : p.natDegree ≤ n) (a : ℝ) :
    p.eval a = ∑ k : Fin (n + 1), p.eval (nodes k) *
      (Lagrange.basis Finset.univ nodes k).eval a := by
  have hdeg : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (n : WithBot ℕ) := by exact_mod_cast hdegree
      _ < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_self n
  calc
    _ = (Lagrange.interpolate Finset.univ nodes (fun k => p.eval (nodes k))).eval a :=
      congrArg (fun r : ℝ[X] => r.eval a) (Lagrange.eq_interpolate hnodes.injOn hdeg)
    _ = _ := by simp [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]

/-- True finite Lagrange recovery produces any evaluation limit from the
node evaluation limits, for every incoming filter. -/
theorem tendsto_eval_of_finite_evaluations {n : ℕ} {I : Type*}
    (F : Filter I) (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (p : I → ℝ[X]) (q : ℝ[X]) (hdegree : ∀ i, (p i).natDegree ≤ n)
    (hqdegree : q.natDegree ≤ n)
    (hlim : ∀ k, Tendsto (fun i => (p i).eval (nodes k)) F (𝓝 (q.eval (nodes k))))
    (a : ℝ) : Tendsto (fun i => (p i).eval a) F (𝓝 (q.eval a)) := by
  have heq : (fun i => (p i).eval a) = fun i => ∑ k : Fin (n + 1),
      (p i).eval (nodes k) * (Lagrange.basis Finset.univ nodes k).eval a :=
    funext fun i => eval_eq_sum_node_values nodes hnodes (p i) (hdegree i) a
  rw [heq, eval_eq_sum_node_values nodes hnodes q hqdegree a]
  exact tendsto_finsetSum Finset.univ fun k _ =>
    (hlim k).mul_const ((Lagrange.basis Finset.univ nodes k).eval a)

end
end SGPT.Foundations.Analysis.Pending.FinitePolynomialEvaluationContinuity
