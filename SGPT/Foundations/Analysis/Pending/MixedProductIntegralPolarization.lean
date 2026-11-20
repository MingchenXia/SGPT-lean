import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option autoImplicit false

/-!
# Finite polarization of actual mixed test integrals

Actual nonnegative indicator-weight expansion and actual slot symmetry,
with finite-measure integration, yield the signed subset formula for the
mixed product. This supports ordinary mixed weak convergence in
Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2, including empty subsets and n=0.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.MixedProductIntegralPolarization

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open GlobalMultilinearExpansion MixedMassProductCalculus
open MixedSummandCapacityDomination PolarizationAlgebra GlobalSlotPerm GlobalDiagonalScaling

noncomputable section

/-- The actual nonnegative indicator coefficients of a subset. -/
def subsetWeight {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S then 1 else 0

theorem subsetWeight_nonneg {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    0 ≤ subsetWeight S i := by unfold subsetWeight; split_ifs <;> norm_num

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Indicator coefficients give the ordinary subset sum of forms. -/
theorem sumForm_subsetWeight_eq (S : Finset (Fin n))
    (alpha : Fin n → ClosedRealOneOneForm n M) :
    sumForm Finset.univ (subsetWeight S) alpha = sumForm S (fun _ => 1) alpha := by
  simp [sumForm, subsetWeight]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- Indicator coefficients give the ordinary subset sum, including poles. -/
theorem sumPot_subsetWeight_eq (S : Finset (Fin n)) (f : Fin n → M → EReal) :
    sumPot Finset.univ (subsetWeight S) f = sumPot S (fun _ => 1) f := by
  funext x
  simp [sumPot, subsetWeight, apply_ite, ite_mul]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every actual subset sum is genuine, including the empty zero sum. -/
theorem isThetaPshPotential_subsetSum {alpha : Fin n → ClosedRealOneOneForm n M}
    {f : Fin n → M → EReal} (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (S : Finset (Fin n)) :
    IsThetaPshPotential (sumForm S (fun _ => 1) alpha).val (sumPot S (fun _ => 1) f) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hz : sumPot (∅ : Finset (Fin n)) (fun _ => 1) f = fun _ => 0 := by
      funext x
      simp [sumPot]
    rw [hz]
    simpa only [sumForm, Finset.sum_empty] using
      (LocalPotentials.isThetaPshPotential_zero_iff (0 : ClosedRealOneOneForm n M)).mpr
        (fun _ _ _ _ => le_rfl)
  · exact isThetaPshPotential_sumPot hS (fun _ => one_pos) hf

/-- The actual diagonal subset product is the sum of its selected mixed
products; zero indicator coefficients are handled by the existing producer. -/
theorem diagonal_subsetSum_eq_sum_selected (omega : KahlerBackground n M)
    {alpha : Fin n → ClosedRealOneOneForm n M} {f : Fin n → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i)) (S : Finset (Fin n)) :
    diagonalPotentialMeasure (sumForm S (fun _ => 1) alpha) (sumPot S (fun _ => 1) f)
        (isThetaPshPotential_subsetSum hf S) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        globalMixedMeasure (fun j => alpha (g j)) (fun j => f (g j))
          (fun j => (hf (g j)).1) := by
  classical
  have h := globalMixedMeasure_sumPot_expand omega
    (c := fun _ => subsetWeight S) (fun _ => subsetWeight_nonneg S) hf
  have eF : (fun _ : Fin n => sumForm Finset.univ (subsetWeight S) alpha) =
      fun _ => sumForm S (fun _ => 1) alpha := funext fun _ => sumForm_subsetWeight_eq S alpha
  have eP : (fun _ : Fin n => sumPot Finset.univ (subsetWeight S) f) =
      fun _ => sumPot S (fun _ => 1) f := funext fun _ => sumPot_subsetWeight_eq S f
  rw [globalMixedMeasure_congr eF eP _ (fun _ => (isThetaPshPotential_subsetSum hf S).1)] at h
  rw [diagonalPotentialMeasure, h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : ∀ j, g j ∈ S
  · have hw : ∏ j, subsetWeight S (g j) = 1 := by simp [subsetWeight, hg]
    simp only [hw, ENNReal.ofReal_one, one_smul, if_pos hg]
  · have hw : ∏ j, subsetWeight S (g j) = 0 := by
      obtain ⟨j, hj⟩ := not_forall.mp hg
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [subsetWeight, hj]
    simp only [hw, ENNReal.ofReal_zero, zero_smul, if_neg hg]

/-- Integrate the actual finite selected-measure sum term by term. -/
theorem integral_diagonal_subsetSum_eq_sum_selected (omega : KahlerBackground n M)
    {alpha : Fin n → ClosedRealOneOneForm n M} {f : Fin n → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (S : Finset (Fin n)) (chi : C(M, ℝ)) :
    (∫ x, chi x ∂(diagonalPotentialMeasure (sumForm S (fun _ => 1) alpha)
      (sumPot S (fun _ => 1) f) (isThetaPshPotential_subsetSum hf S))) =
      ∑ g : Fin n → Fin n with ∀ j, g j ∈ S,
        ∫ x, chi x ∂(globalMixedMeasure (fun j => alpha (g j)) (fun j => f (g j))
          (fun j => (hf (g j)).1)) := by
  rw [diagonal_subsetSum_eq_sum_selected omega hf S]
  apply integral_finsetSum_measure
  intro g _
  have : IsFiniteMeasure (globalMixedMeasure (fun j => alpha (g j))
      (fun j => f (g j)) (fun j => (hf (g j)).1)) :=
    globalMixedMeasure_isFiniteMeasure omega (fun j => (hf (g j)).1)
  exact BoundedContinuousFunction.integrable
    (μ := globalMixedMeasure (fun j => alpha (g j)) (fun j => f (g j))
      (fun j => (hf (g j)).1)) (ContinuousMap.equivBoundedOfCompact M ℝ chi)

/-- Inclusion-exclusion and actual slot symmetry isolate n! times the actual
mixed continuous-test integral. This formula also retains the n=0 product. -/
theorem integral_mixed_eq_signed_diagonal_subsetSum (omega : KahlerBackground n M)
    {alpha : Fin n → ClosedRealOneOneForm n M} {f : Fin n → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i)) (chi : C(M, ℝ)) :
    ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
        ∫ x, chi x ∂(diagonalPotentialMeasure (sumForm S (fun _ => 1) alpha)
          (sumPot S (fun _ => 1) f) (isThetaPshPotential_subsetSum hf S)) =
      (n.factorial : ℝ) * ∫ x, chi x ∂(globalMixedMeasure alpha f (fun i => (hf i).1)) := by
  classical
  simp_rw [integral_diagonal_subsetSum_eq_sum_selected omega hf]
  apply sum_powerset_signed_eq_factorial_mul
  intro sigma
  rw [globalMixedMeasure_perm (fun i => (hf i).1) sigma]
  rfl

end

end SGPT.Foundations.Analysis.Pending.MixedProductIntegralPolarization
