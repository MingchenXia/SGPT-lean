import SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranchSeparators
import SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition

/-! Actual original irredundant germ components manufacture ONE all-branch separator.
Blueprint: prime-nov16-analytic-normalization-original-component-separators.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentSeparators
open AnalyticGermDecomposition

theorem exists_original_component_separators {n k : ℕ} (B : Fin k → Set (ComplexModel n))
    (hB : ∀ i,IsIrreducibleGerm (B i))
    (hpair : Pairwise fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) :
    ∃ t : Fin k → HolGerm (ComplexModel n),∀ i,t i ∉ vanishingIdeal (B i) ∧
      ∀ j,j ≠ i → t i ∈ vanishingIdeal (B j) := by
  classical
  have hex : ∀ i j : Fin k,∃ a : HolGerm (ComplexModel n),
      (j ≠ i → a ∈ vanishingIdeal (B j)) ∧ a ∉ vanishingIdeal (B i) := by
    intro i j
    let : (vanishingIdeal (B i)).IsPrime := (isIrreducibleGerm_iff_isPrime (hB i).1).mp (hB i)
    by_cases hji : j=i
    · refine ⟨1,fun h => (h hji).elim,?_⟩
      exact (vanishingIdeal (B i)).one_notMem
    · have hnle : ¬ vanishingIdeal (B j) ≤ vanishingIdeal (B i) := by
        intro hle
        exact hpair (Ne.symm hji) (le_of_vanishingIdeal_le (hB j).1 hle)
      obtain ⟨a,haj,hai⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨a,fun _ => haj,hai⟩
  choose a ha using hex
  let t : Fin k → HolGerm (ComplexModel n) := fun i => ∏ j,a i j
  refine ⟨t,?_⟩
  intro i
  let : (vanishingIdeal (B i)).IsPrime := (isIrreducibleGerm_iff_isPrime (hB i).1).mp (hB i)
  constructor
  · intro ht
    have hne : (∏ j,Ideal.Quotient.mk (vanishingIdeal (B i)) (a i j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _hj hz
      exact (ha i j).2 (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply hne
    simpa only [t,map_prod] using Ideal.Quotient.eq_zero_iff_mem.mpr ht
  · intro j hji
    exact Ideal.prod_mem _ (Finset.mem_univ j) ((ha i j).1 hji)

theorem weighted_separator_nonzero {n k : ℕ} (B : Fin k → Set (ComplexModel n))
    (hB : ∀ i,IsIrreducibleGerm (B i)) (t h : Fin k → HolGerm (ComplexModel n))
    (ht : ∀ i,t i ∉ vanishingIdeal (B i) ∧ ∀ j,j ≠ i → t i ∈ vanishingIdeal (B j))
    (hh : ∀ i,h i ∉ vanishingIdeal (B i)) (i : Fin k) :
    (∑ j,t j*h j) ∉ vanishingIdeal (B i) := by
  classical
  let P := vanishingIdeal (B i)
  let : P.IsPrime := (isIrreducibleGerm_iff_isPrime (hB i).1).mp (hB i)
  intro hz
  have hsum : Ideal.Quotient.mk P (∑ j,t j*h j)=
      Ideal.Quotient.mk P (t i)*Ideal.Quotient.mk P (h i) := by
    rw [map_sum]
    rw [Finset.sum_eq_single i]
    · exact map_mul _ _ _
    · intro j _hj hji
      rw [map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr ((ht j).2 i (Ne.symm hji)),zero_mul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  rw [hsum] at he
  rcases mul_eq_zero.mp he with he|he
  · exact (ht i).1 (Ideal.Quotient.eq_zero_iff_mem.mp he)
  · exact hh i (Ideal.Quotient.eq_zero_iff_mem.mp he)

theorem weighted_separator_intersection {n k : ℕ} (B : Fin k → Set (ComplexModel n))
    (t h : Fin k → HolGerm (ComplexModel n))
    (ht : ∀ i,∀ j,j ≠ i → t i ∈ vanishingIdeal (B j)) (i j : Fin k) (hij : i ≠ j) :
    (∑ l,t l*h l) ∈ vanishingIdeal (B i ∩ B j) := by
  classical
  apply Ideal.sum_mem
  intro l _hl
  apply Ideal.mul_mem_right
  by_cases hli : l=i
  · subst l
    exact vanishingIdeal_anti (inter_subset_right.eventuallyLE) (ht i j (Ne.symm hij))
  · exact vanishingIdeal_anti (inter_subset_left.eventuallyLE) (ht l i (Ne.symm hli))

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentSeparators
