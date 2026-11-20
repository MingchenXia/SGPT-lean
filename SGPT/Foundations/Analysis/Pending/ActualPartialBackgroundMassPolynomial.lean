import SGPT.Foundations.Analysis.Pending.CanonicalBackgroundPolynomial
import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

/-! # Actual mixed-mass polynomials with selected smooth background slots

SGPT PDF0238 Corollary 6.2.9, finite multilinearity ingredient.
The existing `optForm`/`optPot` background conventions are reused.
-/

open Set MeasureTheory Polynomial
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassPolynomial

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass
  GlobalDiagonalScaling GlobalMultilinearExpansion MixedMassProductCalculus
  MixedMassBoundedDifference CanonicalBackgroundPolynomial KahlerDomination

noncomputable section

private def weightPolynomial {d : ℕ} (S : Finset (Fin d)) (k : Fin d) :
    Option (Fin d) → ℝ[X]
  | none => if k ∈ S then X else 0
  | some j => if j = k then 1 else 0

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual original and smooth-zero slot masses are the finite real
coefficients of this selected-background polynomial. -/
def partialBackgroundMassPolynomial (omega : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ k, IsThetaPshPotential (θ k).val (u k)) (S : Finset (Fin n)) : ℝ[X] :=
  ∑ g : Fin n → Option (Fin n),
    C ((globalMixedMass (fun k => optForm omega θ (g k))
      (fun k => optPot u (g k)) (fun k => optPot_psh omega hu (g k))).toReal) *
      ∏ k, weightPolynomial S k (g k)

omit [BorelSpace M] in
/-- Actual selected-background polynomials have degree at most the number
of slots, including the unique empty tuple in dimension zero. -/
theorem natDegree_partialBackgroundMassPolynomial_le (omega : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ k, IsThetaPshPotential (θ k).val (u k)) (S : Finset (Fin n)) :
    (partialBackgroundMassPolynomial omega θ u hu S).natDegree ≤ n := by
  classical
  unfold partialBackgroundMassPolynomial
  apply natDegree_sum_le_of_forall_le
  intro g _
  apply (natDegree_C_mul_le _ _).trans
  calc
    _ ≤ ∑ k : Fin n, (weightPolynomial S k (g k)).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _k : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro k _
      cases g k <;> simp only [weightPolynomial] <;> split_ifs <;> simp
    _ = n := by simp

/-- Genuine nonnegative selected-background slots and actual multilinearity
produce every polynomial evaluation, including the original value at zero. -/
theorem globalMixedMass_partial_background_toReal_eq_eval
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ k, IsThetaPshPotential (θ k).val (u k))
    (S : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a) :
    (globalMixedMass (fun k => θ k + (if k ∈ S then a else 0) • omega.form) u
      (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu k)
        (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))).1)).toReal =
      (partialBackgroundMassPolynomial omega θ u hu S).eval a := by
  classical
  let c : Fin n → Option (Fin n) → ℝ := fun k o => (weightPolynomial S k o).eval a
  have hc (k : Fin n) (o : Option (Fin n)) : 0 ≤ c k o := by
    cases o <;> dsimp [c, weightPolynomial] <;> split_ifs <;> simp [ha]
  have hpots (o : Option (Fin n)) :
      IsThetaPshPotential (optForm omega θ o).val (optPot u o) := by
    cases o with
    | none => exact (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
    | some k => exact hu k
  have hF : (fun k => sumForm Finset.univ (c k) (optForm omega θ)) =
      fun k => θ k + (if k ∈ S then a else 0) • omega.form := by
    funext k
    by_cases hk : k ∈ S
    simp [sumForm, Fintype.sum_option, c, weightPolynomial, optForm,
      apply_ite, ite_smul, hk, add_comm]
    simp [sumForm, Fintype.sum_option, c, weightPolynomial, optForm,
      apply_ite, ite_smul, hk]
  have hQ : (fun k => sumPot Finset.univ (c k) (optPot u)) = u := by
    funext k x
    simp [sumPot, Fintype.sum_option, c, weightPolynomial, optPot, apply_ite, ite_mul]
  have h := globalMixedMass_sumPot_expand_toReal omega hc hpots
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu k)
      (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))).1)] at h
  simpa only [partialBackgroundMassPolynomial, eval_finsetSum, eval_mul, eval_C,
    eval_prod, c, globalMixedMass, mul_comm] using h

end
end SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassPolynomial
