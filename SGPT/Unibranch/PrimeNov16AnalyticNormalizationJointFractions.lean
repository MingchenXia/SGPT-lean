import SGPT.Unibranch.PrimeNov16AnalyticNormalizationBranchSeparators

/-! A genuine SINGLE non-zero-divisor fraction across EVERY original branch.
Blueprint: prime-nov16-analytic-normalization-joint-fractions.tex. -/
set_option autoImplicit false
noncomputable section
open Set
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationJointFractions
open PrimeNov16AnalyticNormalizationBranches
open PrimeNov16AnalyticNormalizationBranchSeparators

theorem quotient_separator_sum {A : Type*} [CommRing A] [Fintype (minimalPrimes A)]
    (t : minimalPrimes A → A)
    (ht : ∀ p,∀ q,q ≠ p → t p ∈ q.val) (u : minimalPrimes A → A) (p : minimalPrimes A) :
    Ideal.Quotient.mk p.val (∑ q,t q*u q) = Ideal.Quotient.mk p.val (t p)*Ideal.Quotient.mk p.val (u p) := by
  classical
  rw [map_sum,← map_mul]
  apply Finset.sum_eq_single p
  · intro q _hq hqp
    rw [map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (ht q p (Ne.symm hqp)),zero_mul]
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

theorem exists_joint_fraction_denominator (A : Type*) [CommRing A]
    [IsReduced A] [IsNoetherianRing A]
    (u : ∀ p : minimalPrimes A,FractionRing (A ⧸ p.val)) :
    ∃ h ∈ nonZeroDivisors A,∃ g : A,∀ p : minimalPrimes A,
      algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val g) =
        algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val h)*u p := by
  classical
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  let : ∀ p : minimalPrimes A,IsDomain (A ⧸ p.val) := fun p => branch_isDomain A p
  obtain ⟨t,ht⟩ := exists_actual_branch_separators A
  have hex : ∀ p : minimalPrimes A,∃ a b : A,Ideal.Quotient.mk p.val b ≠ 0 ∧
      algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val a)/
        algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val b) = u p := by
    intro p
    let : p.val.IsPrime := p.property.isPrime
    obtain ⟨a,b,hb,he⟩ := IsFractionRing.div_surjective (A ⧸ p.val) (u p)
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a,b,mem_nonZeroDivisors_iff_ne_zero.mp hb,he⟩
  choose a b hb hfrac using hex
  let h : A := ∑ p,t p*b p
  let g : A := ∑ p,t p*a p
  have hquot (p : minimalPrimes A) : Ideal.Quotient.mk p.val h =
      Ideal.Quotient.mk p.val (t p)*Ideal.Quotient.mk p.val (b p) :=
    quotient_separator_sum t (fun p => (ht p).2) b p
  have gquot (p : minimalPrimes A) : Ideal.Quotient.mk p.val g =
      Ideal.Quotient.mk p.val (t p)*Ideal.Quotient.mk p.val (a p) :=
    quotient_separator_sum t (fun p => (ht p).2) a p
  have hNZ : h ∈ nonZeroDivisors A := by
    apply nonZeroDivisor_of_avoids_minimal_primes A h
    intro p hp
    let : p.val.IsPrime := p.property.isPrime
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hquot p] at hz
    exact (mul_ne_zero (fun he => (ht p).1 (Ideal.Quotient.eq_zero_iff_mem.mp he)) (hb p)) hz
  refine ⟨h,hNZ,g,?_⟩
  intro p
  let : p.val.IsPrime := p.property.isPrime
  have hbF : algebraMap (A ⧸ p.val) (FractionRing (A ⧸ p.val)) (Ideal.Quotient.mk p.val (b p)) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (A ⧸ p.val) (FractionRing (A ⧸ p.val))).ne (hb p)
  rw [hquot p,gquot p,map_mul,map_mul,← hfrac p]
  field_simp

theorem original_stalk_joint_fraction_denominator (X : SourceReducedComplexSpace) (x : X.obj.left)
    (u : ∀ p : minimalPrimes (X.obj.left.presheaf.stalk x).carrier,
      FractionRing ((X.obj.left.presheaf.stalk x).carrier ⧸ p.val)) :
    ∃ h ∈ nonZeroDivisors (X.obj.left.presheaf.stalk x).carrier,
      ∃ g : (X.obj.left.presheaf.stalk x).carrier,∀ p : minimalPrimes (X.obj.left.presheaf.stalk x).carrier,
        algebraMap _ (FractionRing ((X.obj.left.presheaf.stalk x).carrier ⧸ p.val)) (Ideal.Quotient.mk p.val g) =
          algebraMap _ (FractionRing ((X.obj.left.presheaf.stalk x).carrier ⧸ p.val)) (Ideal.Quotient.mk p.val h)*u p := by
  let : IsNoetherianRing (X.obj.left.presheaf.stalk x).carrier := original_stalk_noetherian X x
  have := X.isReduced_stalk x
  exact exists_joint_fraction_denominator _ u

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationJointFractions
