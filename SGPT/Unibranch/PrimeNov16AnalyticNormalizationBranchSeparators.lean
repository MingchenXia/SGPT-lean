import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedAlgebra
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! Actual branch separators and true reduced non-zero-divisor criterion.
Blueprint: prime-nov16-analytic-normalization-branch-separators.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranchSeparators
open PrimeNov16AnalyticNormalizationBranches

theorem exists_actual_branch_separators (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ∃ t : minimalPrimes A → A,∀ p,t p ∉ p.val ∧ ∀ q,q ≠ p → t p ∈ q.val := by
  classical
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hex : ∀ p q : minimalPrimes A,∃ a : A,(q ≠ p → a ∈ q.val) ∧ a ∉ p.val := by
    intro p q
    by_cases hqp : q=p
    · refine ⟨1,fun h => (h hqp).elim,?_⟩
      intro hp
      exact p.property.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one)
    · have hnle : ¬ q.val ≤ p.val := by
        intro hle
        have hpq : p.val ≤ q.val := p.property.2 ⟨q.property.isPrime,bot_le⟩ hle
        exact hqp (Subtype.ext (hle.antisymm hpq))
      obtain ⟨a,haq,hap⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨a,fun _ => haq,hap⟩
  choose b hb using hex
  let t : minimalPrimes A → A := fun p => ∏ q,b p q
  refine ⟨t,?_⟩
  intro p
  let : p.val.IsPrime := p.property.isPrime
  constructor
  · intro hp
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    have hne : (∏ q : minimalPrimes A,Ideal.Quotient.mk p.val (b p q)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q _hq he
      exact (hb p q).2 (Ideal.Quotient.eq_zero_iff_mem.mp he)
    apply hne
    simpa only [t,map_prod] using hz
  · intro q hqp
    exact Ideal.prod_mem q.val (Finset.mem_univ q) ((hb p q).1 hqp)

theorem nonZeroDivisor_of_avoids_minimal_primes (A : Type*) [CommRing A] [IsReduced A]
    (h : A) (hh : ∀ p : minimalPrimes A,h ∉ p.val) : h ∈ nonZeroDivisors A := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro a ha
  apply branchMap_injective A
  funext p
  let : p.val.IsPrime := p.property.isPrime
  change Ideal.Quotient.mk p.val a = Ideal.Quotient.mk p.val 0
  rw [map_zero]
  have he := congrArg (Ideal.Quotient.mk p.val) ha
  rw [map_mul,map_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (fun hz => hh p (Ideal.Quotient.eq_zero_iff_mem.mp hz))

theorem nonZeroDivisor_avoids_minimal_primes (A : Type*) [CommRing A]
    (h : A) (hh : h ∈ nonZeroDivisors A) (p : minimalPrimes A) : h ∉ p.val :=
  fun hp => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hp p.property hh

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranchSeparators
