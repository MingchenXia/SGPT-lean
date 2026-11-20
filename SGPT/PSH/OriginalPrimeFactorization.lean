import SGPT.PSH.CommonPrimeNeighbourhood
import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGermFactoriality
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm OkaRelationSheaf OkaIdealOperations
open scoped Topology Manifold ContDiff

private theorem exists_mk_prime_product {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ) (hf : ∀ i, HolAt (f i) 0) :
    ∃ hP : HolAt (fun z => ∏ i ∈ s, f i z) 0,
      HolGerm.mk (fun z => ∏ i ∈ s, f i z) hP = ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (⟨eventually_differentiableAt_one, HolGerm.mk_one⟩ :
        ∃ hP : HolAt (fun _ : ComplexModel n => (1 : ℂ)) 0,
          HolGerm.mk (fun _ => (1 : ℂ)) hP = 1)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    obtain ⟨hP, hPC⟩ := ih
    refine ⟨eventually_differentiableAt_mul (hf i) hP, ?_⟩
    rw [HolGerm.mk_mul (f i) (fun z => ∏ j ∈ s, f j z) (hf i) hP, hPC]

/-- The ORIGINAL nonzero germ internally produces the entire distinct
prime family, positive actual multiplicities, unit and literal product. -/
theorem exists_original_distinct_prime_factorization {n : ℕ}
    (f : ComplexModel n → ℂ) (hf : HolAt f 0) (hF : HolGerm.mk f hf ≠ 0) :
    ∃ (r : ℕ) (q : Fin r → ComplexModel n → ℂ) (hq : ∀ i, HolAt (q i) 0)
      (a : Fin r → ℕ) (v : ComplexModel n → ℂ) (_hv : HolAt v 0),
      (∀ i, Prime (HolGerm.mk (q i) (hq i))) ∧
      (∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j)) ∧
      (∀ i, 0 < a i ∧ a i = multiplicity (HolGerm.mk (q i) (hq i)) (HolGerm.mk f hf)) ∧
      v 0 ≠ 0 ∧ (∀ᶠ z in 𝓝 0, v z ≠ 0) ∧
      f =ᶠ[𝓝 0] fun z => (∏ i, q i z ^ a i) * v z := by
  classical
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  let : StrongNormalizationMonoid (HolGerm (ComplexModel n)) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let S := UniqueFactorizationMonoid.normalizedFactors (HolGerm.mk f hf)
  let I := {Q : HolGerm (ComplexModel n) // Q ∈ S.toFinset}
  let e := Fintype.equivFin I
  let Q : Fin (Fintype.card I) → HolGerm (ComplexModel n) := fun i => (e.symm i).val
  let a : Fin (Fintype.card I) → ℕ := fun i => S.count (Q i)
  have hmem (i : Fin (Fintype.card I)) : Q i ∈ S :=
    Multiset.mem_toFinset.mp (e.symm i).property
  have hprime (i : Fin (Fintype.card I)) : Prime (Q i) :=
    UniqueFactorizationMonoid.prime_of_normalized_factor (Q i) (hmem i)
  have hnot (i j : Fin (Fintype.card I)) (hij : i ≠ j) : ¬Q i ∣ Q j := by
    intro hd
    have heq : Q i = Q j := UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
      (hmem i) (hmem j) ((hprime i).associated_of_dvd (hprime j) hd)
    exact hij (e.symm.injective (Subtype.ext heq))
  have hmult (i : Fin (Fintype.card I)) :
      0 < a i ∧ a i = multiplicity (Q i) (HolGerm.mk f hf) := by
    refine ⟨Multiset.count_pos.mpr (hmem i), ?_⟩
    have h := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (hprime i).irreducible hF
    rw [UniqueFactorizationMonoid.normalize_normalized_factor (Q i) (hmem i)] at h
    exact h.symm
  have hprod : (∏ i, Q i ^ a i) = S.prod := by
    calc
      _ = ∏ p : I, p.val ^ S.count p.val :=
        Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
      _ = ∏ p ∈ S.toFinset, p ^ S.count p :=
        Finset.prod_coe_sort S.toFinset (fun p => p ^ S.count p)
      _ = (∑ p ∈ S.toFinset, S.count p • ({p} : Multiset (HolGerm (ComplexModel n)))).prod := by
        simp only [Multiset.prod_sum, Multiset.prod_nsmul, Multiset.prod_singleton]
      _ = S.prod := by rw [Multiset.toFinset_sum_count_nsmul_eq]
  choose q hq hrep using fun i => HolGerm.exists_eq_mk (Q i)
  have hassoc : Associated (∏ i, Q i ^ a i) (HolGerm.mk f hf) := by
    rw [hprod]
    exact UniqueFactorizationMonoid.prod_normalizedFactors hF
  obtain ⟨unit, hunit⟩ := hassoc
  obtain ⟨v, hv, hunitrep⟩ := HolGerm.exists_eq_mk (unit : HolGerm (ComplexModel n))
  have hv0 : v 0 ≠ 0 := by
    have h := (HolGerm.isUnit_iff_eval_ne_zero _).mp unit.isUnit
    rwa [hunitrep, HolGerm.eval_mk] at h
  obtain ⟨hP, hPC⟩ := exists_mk_prime_product Finset.univ
    (fun i z => q i z ^ a i) (fun i => eventually_differentiableAt_pow (hq i) (a i))
  have hPprime : HolGerm.mk (fun z => ∏ i, q i z ^ a i) hP = ∏ i, Q i ^ a i := by
    rw [hPC]
    apply Finset.prod_congr rfl
    intro i _
    rw [HolGerm.mk_pow (q i) (hq i) (a i), ← hrep i]
  have hEq : HolGerm.mk f hf = HolGerm.mk (fun z => (∏ i, q i z ^ a i) * v z)
      (eventually_differentiableAt_mul hP hv) := by
    rw [HolGerm.mk_mul (fun z => ∏ i, q i z ^ a i) v hP hv, hPprime, ← hunitrep]
    exact hunit.symm
  refine ⟨Fintype.card I, q, hq, a, v, hv, ?_, ?_, ?_, hv0,
    hv.self_of_nhds.continuousAt.eventually_ne hv0, HolGerm.mk_eq_mk_iff.mp hEq⟩
  · intro i
    simpa only [hrep] using hprime i
  · intro i j hij
    simpa only [hrep] using hnot i j hij
  · intro i
    simpa only [hrep] using hmult i

#print axioms exists_original_distinct_prime_factorization

/-- The ORIGINAL nonzero holomorphic function produces its entire
prime-divisor factorization on ONE actual open neighborhood internally. -/
theorem exists_original_common_open_prime_factorization {m : ℕ}
    (f : ComplexModel (m + 1) → ℂ) (hf : HolAt f 0) (hF : HolGerm.mk f hf ≠ 0)
    (N : Set (ComplexModel (m + 1))) (hN : N ∈ 𝓝 0) :
    ∃ U : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ U ∧
      (U : Set (ComplexModel (m + 1))) ⊆ N ∧
      ∃ (r : ℕ) (q : Fin r → ComplexModel (m + 1) → ℂ)
        (hq : ∀ i, HolAt (q i) 0) (a : Fin r → ℕ) (v : ComplexModel (m + 1) → ℂ)
        (V : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) U),
        (∀ i, Prime (HolGerm.mk (q i) (hq i))) ∧
        (∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j)) ∧
        (∀ i, 0 < a i ∧ a i = multiplicity (HolGerm.mk (q i) (hq i)) (HolGerm.mk f hf)) ∧
        DifferentiableOn ℂ v U ∧ (∀ y ∈ U, v y ≠ 0) ∧
        (∀ y ∈ U, f y = (∏ i, q i y ^ a i) * v y) ∧
        (∀ y : U, f y = 0 ↔ ∃ i, y ∈ (V i).carrier) ∧
        ∀ i, (V i).carrier = {y : U | q i y = 0} ∧ (V i).dim = m ∧
          (∀ y : U, HolomorphicIdealSheaves.HolomorphicAt (m + 1) (fun z : U => q i z) y) ∧
          (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (V i).carrier).IsInvertible ∧
          ∀ (y : U) (b : U → ℂ),
            (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (V i).carrier).mem y b ↔
              HolomorphicIdealSheaves.IsInSpanAt (n := m + 1) (· = fun z : U => q i z) y b := by
  classical
  obtain ⟨r, q, hq, a, v, hv, hprime, hnot, hmult, _hv0, hvnon, hfactor⟩ :=
    exists_original_distinct_prime_factorization f hf hF
  let N' : Set (ComplexModel (m + 1)) :=
    {z | z ∈ N ∧ HolAt v z ∧ v z ≠ 0 ∧ f z = (∏ i, q i z ^ a i) * v z}
  have hN' : N' ∈ 𝓝 0 := by
    filter_upwards [hN, OkaRelationSheaf.HolAt.eventually hv, hvnon, hfactor]
      with z hz hhol hvz hfac
    exact ⟨hz, hhol, hvz, hfac⟩
  obtain ⟨U, h0U, hUN', V, hV⟩ := exists_common_open_prime_carriers q hq hprime hnot N' hN'
  have hvU : DifferentiableOn ℂ v U :=
    fun y hy => (hUN' hy).2.1.differentiableAt.differentiableWithinAt
  have hvne : ∀ y ∈ U, v y ≠ 0 := fun _ hy => (hUN' hy).2.2.1
  have hfac : ∀ y ∈ U, f y = (∏ i, q i y ^ a i) * v y :=
    fun _ hy => (hUN' hy).2.2.2
  refine ⟨U, h0U, fun y hy => (hUN' hy).1, r, q, hq, a, v, V,
    hprime, hnot, hmult, hvU, hvne, hfac, ?_, hV⟩
  intro y
  rw [hfac y y.2, mul_eq_zero, or_iff_left (hvne y y.2), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    have hqi : q i y = 0 := eq_zero_of_pow_eq_zero hi
    refine ⟨i, ?_⟩
    rw [(hV i).1]
    exact hqi
  · rintro ⟨i, hi⟩
    rw [(hV i).1] at hi
    have hqi : q i y = 0 := hi
    exact ⟨i, Finset.mem_univ i, by rw [hqi, zero_pow (Nat.ne_zero_of_lt (hmult i).1)]⟩

#print axioms exists_original_common_open_prime_factorization

end SGPT.PSH
