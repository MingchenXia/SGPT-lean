import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

/-! # Actual independent convex mixed-mass polynomials

SGPT PDF0234--0235, actual finite multilinearity ingredient of the
zero-target reduction in Theorem 6.2.1. No mixed limit is an input.
-/

open Set MeasureTheory Polynomial
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial

open FirstPass FirstPass.PositiveClasses RelativeEnergy MixedMass GlobalNonPluripolar
  GlobalMultilinearExpansion MixedMassProductCalculus EndpointMixedMassConvexCombination
  ThetaPshConvexCombination GlobalDiagonalScaling

noncomputable section

private def weightPolynomial {d : ℕ} (i : Fin d) (b : Fin d × Bool) : ℝ[X] :=
  if b.1 = i then (if b.2 then X else 1 - X) else 0

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual finite independent mixed masses are the coefficients of this
real polynomial, including the empty slot tuple in dimension zero. -/
def convexMixedMassPolynomial (θ : Fin n → ClosedRealOneOneForm n M)
    (u p : Fin n → M → EReal)
    (hu : ∀ a, IsThetaPshPotential (θ a).val (u a))
    (hp : ∀ a, IsThetaPshPotential (θ a).val (p a)) : ℝ[X] :=
  ∑ g : Fin n → Fin n × Bool,
    C ((globalMixedMass (fun k => θ (g k).1)
      (fun k => if (g k).2 then u (g k).1 else p (g k).1)
      (fun k => by split_ifs <;> first | exact (hu _).1 | exact (hp _).1)).toReal) *
      ∏ k, weightPolynomial k (g k)

omit [BorelSpace M] in
/-- Every term has at most one linear factor per slot, so the actual
independent convex mass polynomial has degree at most the dimension. -/
theorem natDegree_convexMixedMassPolynomial_le
    (θ : Fin n → ClosedRealOneOneForm n M) (u p : Fin n → M → EReal)
    (hu : ∀ a, IsThetaPshPotential (θ a).val (u a))
    (hp : ∀ a, IsThetaPshPotential (θ a).val (p a)) :
    (convexMixedMassPolynomial θ u p hu hp).natDegree ≤ n := by
  classical
  unfold convexMixedMassPolynomial
  apply natDegree_sum_le_of_forall_le
  intro g _
  apply (natDegree_C_mul_le _ _).trans
  calc
    _ ≤ ∑ k : Fin n, (weightPolynomial k (g k)).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _k : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro k _
      unfold weightPolynomial
      split_ifs
      · simp
      · exact (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp)
      · simp
    _ = n := by simp

/-- Nonnegative actual slot multilinearity identifies every closed-interval
polynomial evaluation with the real value of the genuine convex mixed mass. -/
theorem globalMixedMass_convexComb_toReal_eq_eval
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u p : Fin n → M → EReal}
    (hu : ∀ a, IsThetaPshPotential (θ a).val (u a))
    (hp : ∀ a, IsThetaPshPotential (θ a).val (p a))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (globalMixedMass θ (fun k => convexComb a (u k) (p k))
      (fun k => (isThetaPshPotential_convexComb_closed (hu k) (hp k) ha0 ha1).1)).toReal =
      (convexMixedMassPolynomial θ u p hu hp).eval a := by
  classical
  let c : Fin n → Fin n × Bool → ℝ := fun k b =>
    if b.1 = k then (if b.2 then a else 1 - a) else 0
  let α : Fin n × Bool → ClosedRealOneOneForm n M := fun b => θ b.1
  let pots : Fin n × Bool → M → EReal := fun b => if b.2 then u b.1 else p b.1
  have hpots (b : Fin n × Bool) : IsThetaPshPotential (α b).val (pots b) := by
    dsimp [α, pots]
    split_ifs <;> first | exact hu _ | exact hp _
  have hc (k : Fin n) (b : Fin n × Bool) : 0 ≤ c k b := by
    dsimp [c]
    split_ifs <;> first | exact ha0 | exact sub_nonneg.mpr ha1 | exact le_rfl
  have hF : (fun k => sumForm Finset.univ (c k) α) = θ := by
    funext k
    simp [sumForm, Fintype.sum_prod_type, c, α,
      ← add_smul, show a + (1 - a) = 1 by ring]
  have hQ : (fun k => sumPot Finset.univ (c k) pots) =
      fun k => convexComb a (u k) (p k) := by
    funext k x
    simp [sumPot, Fintype.sum_prod_type, c, pots, apply_ite, ite_mul, convexComb]
  have h := globalMixedMass_sumPot_expand_toReal omega hc hpots
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (fun k => (isThetaPshPotential_convexComb_closed (hu k) (hp k) ha0 ha1).1)] at h
  have hw (k : Fin n) (b : Fin n × Bool) : (weightPolynomial k b).eval a = c k b := by
    dsimp [weightPolynomial, c]
    split_ifs <;> simp only [eval_sub, eval_one, eval_X, eval_zero]
  simpa only [convexMixedMassPolynomial, eval_finsetSum, eval_mul, eval_C,
    eval_prod, hw, α, pots, globalMixedMass, mul_comm] using h

end
end SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial
