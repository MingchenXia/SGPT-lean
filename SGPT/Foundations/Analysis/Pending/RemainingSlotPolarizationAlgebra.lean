import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

set_option autoImplicit false

/-!
# Finite polarization retaining a distinguished slot

Lu, arXiv:2005.04264v1, proof of Theorem 1.2. Indicator expansion
and inclusion-exclusion of the remaining labels, including the empty set.
-/

namespace SGPT.Foundations.Analysis.Pending.RemainingSlotPolarizationAlgebra

noncomputable section

/-- Relabel only the slots complementary to the distinguished slot. -/
def remainingMap {m : ℕ} (k : Fin (m + 1)) (g : Fin m → Fin m)
    (i : Fin (m + 1)) : Option (Fin m) :=
  (finSuccEquiv' k i).map g

/-- Nonnegative indicator coefficients of an actual remaining subset sum. -/
def remainingSubsetCoeff {m : ℕ} (k : Fin (m + 1)) (S : Finset (Fin m))
    (i : Fin (m + 1)) (j : Option (Fin m)) : ℝ :=
  match finSuccEquiv' k i, j with
  | none, none => 1
  | some _, some a => if a ∈ S then 1 else 0
  | _, _ => 0

theorem remainingSubsetCoeff_nonneg {m : ℕ} (k : Fin (m + 1))
    (S : Finset (Fin m)) (i : Fin (m + 1)) (j : Option (Fin m)) :
    0 ≤ remainingSubsetCoeff k S i j := by
  unfold remainingSubsetCoeff
  cases finSuccEquiv' k i <;> cases j <;> positivity

/-- Indicator products are one precisely for the supported maps. -/
theorem prod_remainingSubsetCoeff {m : ℕ} (k : Fin (m + 1))
    (S : Finset (Fin m)) (h : Fin (m + 1) → Option (Fin m)) :
    (∏ i, remainingSubsetCoeff k S i (h i)) =
      if h k = none ∧ ∀ j, ∃ a ∈ S, h (k.succAbove j) = some a then 1 else 0 := by
  classical
  by_cases hsupport : h k = none ∧ ∀ j, ∃ a ∈ S, h (k.succAbove j) = some a
  · rw [if_pos hsupport]
    apply Finset.prod_eq_one
    intro i _
    obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
    cases o with
    | none => simp [remainingSubsetCoeff, hsupport.1]
    | some j =>
      obtain ⟨a, ha, heq⟩ := hsupport.2 j
      simp [remainingSubsetCoeff, heq, ha]
  · rw [if_neg hsupport]
    by_contra hne
    have hc (i : Fin (m + 1)) : remainingSubsetCoeff k S i (h i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
    apply hsupport
    constructor
    · have hk := hc k
      cases heq : h k with
      | none => rfl
      | some a => simp [remainingSubsetCoeff, heq] at hk
    · intro j
      have hj := hc (k.succAbove j)
      cases heq : h (k.succAbove j) with
      | none => simp [remainingSubsetCoeff, heq] at hj
      | some a =>
        refine ⟨a, ?_, rfl⟩
        simpa [remainingSubsetCoeff, heq] using hj

/-- Reindex the actual indicator expansion by maps of the remaining labels. -/
theorem sum_remainingSubsetCoeff {m : ℕ} (k : Fin (m + 1))
    (S : Finset (Fin m)) (d : (Fin (m + 1) → Option (Fin m)) → ℝ) :
    ∑ h, (∏ i, remainingSubsetCoeff k S i (h i)) * d h =
      ∑ g : Fin m → Fin m with ∀ j, g j ∈ S, d (remainingMap k g) := by
  classical
  simp_rw [prod_remainingSubsetCoeff, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun g _ => remainingMap k g) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    refine ⟨by simp [remainingMap], fun j => ⟨g j, hg j, ?_⟩⟩
    simp [remainingMap]
  · intro g hg g' hg' heq
    funext j
    have h := congrFun heq (k.succAbove j)
    simpa [remainingMap] using h
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    choose g hg heq using hh.2
    refine ⟨g, by simpa using hg, ?_⟩
    funext i
    obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
    cases o with
    | none => simpa [remainingMap] using hh.1.symm
    | some j => simpa [remainingMap] using (heq j).symm
  · intro g _
    rfl

/-- A true permutation of all slots extending a remaining-label permutation. -/
def remainingPermutation {m : ℕ} (k : Fin (m + 1)) (sigma : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  ((finSuccEquiv' k).trans (Equiv.optionCongr sigma)).trans (finSuccEquiv' k).symm

theorem remainingPermutation_fixed {m : ℕ} (k : Fin (m + 1))
    (sigma : Equiv.Perm (Fin m)) : remainingPermutation k sigma k = k := by
  simp [remainingPermutation]

theorem remainingMap_perm {m : ℕ} (k : Fin (m + 1))
    (sigma : Equiv.Perm (Fin m)) (i : Fin (m + 1)) :
    remainingMap k sigma i = finSuccEquiv' k (remainingPermutation k sigma i) := by
  simp [remainingMap, remainingPermutation]

/-- Inclusion-exclusion isolates the actual remaining permutation coefficients. -/
theorem sum_signed_remainingSubsetCoeff {m : ℕ} (k : Fin (m + 1))
    (d : (Fin (m + 1) → Option (Fin m)) → ℝ)
    (hd : ∀ sigma : Equiv.Perm (Fin m), d (remainingMap k sigma) = d (remainingMap k id)) :
    ∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) *
        ∑ h, (∏ i, remainingSubsetCoeff k S i (h i)) * d h =
      (m.factorial : ℝ) * d (remainingMap k id) := by
  simp_rw [sum_remainingSubsetCoeff]
  exact PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul
    (fun g => d (remainingMap k g)) hd

end

end SGPT.Foundations.Analysis.Pending.RemainingSlotPolarizationAlgebra
