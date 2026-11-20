import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGermFactoriality
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false

/-! # Actual elimination for an origin-primitive Weierstrass family

The original primitive germ family, a distinguished member, and actual
fraction-field algebra produce a nonzero base germ in the original ideal.
No near-centre primitive or projection/current nullity premise is supplied.
-/

noncomputable section
open Filter Topology Polynomial
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveWeierstrassElimination
open HolGerm OkaGermRelations ActualHolomorphicGermFactoriality

/-- Origin primitivity and an actual distinguished member internally
produce a nonzero base germ in the original polynomial ideal. -/
theorem exists_nonzero_constant_mem_span {n N : ℕ}
    (P : Fin N → (HolGerm (EuclideanSpace ℂ (Fin n)))[X]) (k : Fin N)
    (hW : (P k).Monic)
    (hW0 : ∀ j < (P k).natDegree, HolGerm.eval ((P k).coeff j) = 0)
    (hprimitive : ∀ q : HolGerm (EuclideanSpace ℂ (Fin n) × ℂ),
      (∀ i, q ∣ shiftEval 0 (P i)) → IsUnit q) :
    ∃ r : HolGerm (EuclideanSpace ℂ (Fin n)), r ≠ 0 ∧
      C r ∈ Ideal.span (Set.range P) := by
  classical
  let R := HolGerm (EuclideanSpace ℂ (Fin n))
  let K := FractionRing R
  let : UniqueFactorizationMonoid R := uniqueFactorizationMonoid_holGerm_euclidean n
  let f : R →+* K := algebraMap R K
  let I : Ideal K[X] := Ideal.span (Set.range (fun i => (P i).map f))
  let a : K[X] := Submodule.IsPrincipal.generator I
  have ha (i : Fin N) : a ∣ (P i).map f :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span ⟨i, rfl⟩)
  have hau : IsUnit a := by
    by_contra hna
    obtain ⟨p, hpm, hpi, hpa⟩ := Polynomial.exists_monic_irreducible_factor a hna
    have hpW := hpa.trans (ha k)
    obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hW hpW
    rw [hpm.leadingCoeff, C_1, mul_one] at hQ
    have hQm : Q.Monic := monic_of_injective (IsFractionRing.injective R K)
      (by rwa [hQ])
    have hQi (i : Fin N) : Q ∣ P i :=
      hQm.isPrimitive.dvd_of_fraction_map_dvd_fraction_map
        (by rw [hQ]; exact hpa.trans (ha i))
    have hqu : IsUnit (shiftEval 0 Q) := hprimitive _ fun i => by
      obtain ⟨A, hA⟩ := hQi i
      exact ⟨shiftEval 0 A, by rw [hA, map_mul]⟩
    have hunit : IsUnit Q :=
      isUnit_of_dvd_distinguished_of_isUnit_shiftEval hW hW0 (hQi k) hqu
    exact hpi.not_isUnit (hQ ▸ hunit.map (mapRingHom f))
  have hItop : I = ⊤ :=
    I.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem I) hau
  let J : Ideal R[X] := Ideal.span (Set.range P)
  let : Algebra R[X] K[X] := Polynomial.algebra R K
  let : IsLocalization ((nonZeroDivisors R).map C) K[X] :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  have hmap : J.map (algebraMap R[X] K[X]) = I := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hone : algebraMap R[X] K[X] 1 ∈ J.map (algebraMap R[X] K[X]) := by
    rw [hmap, hItop]
    trivial
  obtain ⟨m, hm, hJ⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((nonZeroDivisors R).map C) K[X] J 1).mp hone
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hm
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, by simpa only [mul_one] using hJ⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveWeierstrassElimination
