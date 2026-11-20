import SGPT.Foundations.Analysis.Pending.PolynomialCoefficientRecovery
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Zero and first polynomial coefficients of actual binary slot choices

The degree-one selection in Lu, arXiv:2005.04264v1, Theorem 1.2.
These finite identities identify the zero-reference term and each one-slot
term of an actual positive mixed-product expansion, including dimension zero.
-/

namespace SGPT.Foundations.Analysis.Pending.BinarySlotPolynomialCoefficients

noncomputable section

/-- The degree attached to choosing the moving potential in a binary slot. -/
def binaryDegree {n : ℕ} (g : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => g i = true).card

/-- The unique binary choice moving exactly slot `i`. -/
def oneSlotChoice {n : ℕ} (i : Fin n) : Fin n → Bool :=
  Function.update (fun _ => false) i true

theorem binaryDegree_oneSlotChoice {n : ℕ} (i : Fin n) :
    binaryDegree (oneSlotChoice i) = 1 := by
  have heq : (Finset.univ.filter fun j => oneSlotChoice i j = true) = {i} := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = i
    · subst hj
      simp [oneSlotChoice]
    · simp [oneSlotChoice, hj]
  simp [binaryDegree, heq]

/-- Degree zero retains precisely the constant reference choice. -/
theorem sum_binary_degree_zero {n : ℕ} (d : (Fin n → Bool) → ℝ) :
    (∑ g with binaryDegree g = 0, d g) = d (fun _ => false) := by
  classical
  rw [Finset.sum_eq_single (fun _ => false)]
  · intro g hg hne
    have hempty : (Finset.univ.filter fun i => g i = true) = ∅ :=
      Finset.card_eq_zero.mp (Finset.mem_filter.mp hg).2
    have hgfalse : ∀ i, g i = false := by
      intro i
      have hnot : g i ≠ true := by
        intro hi
        have hmem : i ∈ (Finset.univ.filter fun j => g j = true) := by simp [hi]
        simp [hempty] at hmem
      cases hi : g i <;> simp_all
    exact (hne (funext hgfalse)).elim
  · simp [binaryDegree]

/-- Degree one is the actual finite sum over its unique moving slot. -/
theorem sum_binary_degree_one {n : ℕ} (d : (Fin n → Bool) → ℝ) :
    (∑ g with binaryDegree g = 1, d g) = ∑ i : Fin n, d (oneSlotChoice i) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => oneSlotChoice i) ?_ ?_ ?_ ?_
  · intro i _
    simp [binaryDegree_oneSlotChoice]
  · intro i _ j _ heq
    by_contra hij
    have h := congrFun heq i
    simp [oneSlotChoice, Function.update_of_ne hij] at h
  · intro g hg
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hg).2
    refine ⟨i, Finset.mem_univ i, funext fun j => ?_⟩
    have hiff : g j = true ↔ j = i := by
      have hm : j ∈ (Finset.univ.filter fun k => g k = true) ↔ j ∈ ({i} : Finset (Fin n)) :=
        by rw [hi]
      simpa using hm
    by_cases hj : j = i
    · subst hj
      simp [oneSlotChoice, hiff.mpr rfl]
    · have hfalse : g j = false := by cases he : g j <;> simp_all
      simp [oneSlotChoice, Function.update_of_ne hj, hfalse]
  · intro i _
    rfl

end

end SGPT.Foundations.Analysis.Pending.BinarySlotPolynomialCoefficients
