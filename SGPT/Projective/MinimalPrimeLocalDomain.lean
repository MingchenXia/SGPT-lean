import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Genuine original minimal primes become comaximal from actual local domains;
no component/cycle/intersection certificate. Blueprint: minimal-prime-local-domain.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set
variable {R : Type*} [CommRing R]

/-- An actual minimal prime under the SAME local domain prime equals the
kernel of the actual original localization map. -/
theorem minimalPrime_eq_localization_kernel
    (p m : Ideal R) (hp : p ∈ minimalPrimes R) (hm : m.IsPrime) (hpm : p ≤ m)
    [IsDomain (Localization.AtPrime m)] :
    p = RingHom.ker (algebraMap R (Localization.AtPrime m)) := by
  let : m.IsPrime := hm
  have hdisjoint : Disjoint (m.primeCompl : Set R) (p : Set R) := by
    apply Set.disjoint_left.mpr
    intro x hxm hxp
    exact hxm (hpm hxp)
  have hcontract := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl
    (Localization.AtPrime m) hp.isPrime hdisjoint
  have hmap : p.map (algebraMap R (Localization.AtPrime m)) ∈
      ((⊥ : Ideal R).map (algebraMap R (Localization.AtPrime m))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map m.primeCompl (Localization.AtPrime m)]
    change Ideal.under R (p.map (algebraMap R (Localization.AtPrime m))) ∈ minimalPrimes R
    rw [hcontract]
    exact hp
  rw [Ideal.map_bot] at hmap
  change p.map (algebraMap R (Localization.AtPrime m)) ∈ minimalPrimes (Localization.AtPrime m) at hmap
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hmap
  calc
    p = Ideal.under R (p.map (algebraMap R (Localization.AtPrime m))) := hcontract.symm
    _ = Ideal.under R (⊥ : Ideal (Localization.AtPrime m)) := congrArg (Ideal.under R) hmap
    _ = _ := rfl

/-- True original maximal-local-domain geometry makes DISTINCT original minimal primes comaximal. -/
theorem distinct_minimalPrimes_sup_eq_top
    (hlocal : ∀ (m : Ideal R) (hm : m.IsMaximal), letI := hm.isPrime; IsDomain (Localization.AtPrime m))
    (p q : Ideal R) (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R) (hpq : p ≠ q) :
    p ⊔ q = ⊤ := by
  by_contra hproper
  obtain ⟨m, hm, hsum⟩ := Ideal.exists_le_maximal (p ⊔ q) hproper
  let : m.IsPrime := hm.isPrime
  let := hlocal m hm
  have hpm := minimalPrime_eq_localization_kernel p m hp hm.isPrime (le_sup_left.trans hsum)
  have hqm := minimalPrime_eq_localization_kernel q m hq hm.isPrime (le_sup_right.trans hsum)
  exact hpq (hpm.trans hqm.symm)

/-- ALL actual original affine irreducible components are pairwise disjoint,
from actual original maximal-local domains; no component choice or certificate. -/
theorem primeSpectrum_irreducibleComponents_pairwiseDisjoint
    (hlocal : ∀ (m : Ideal R) (hm : m.IsMaximal), letI := hm.isPrime; IsDomain (Localization.AtPrime m)) :
    (irreducibleComponents (PrimeSpectrum R)).Pairwise Disjoint := by
  intro C hC D hD hCD
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hC hD
  obtain ⟨p, hp, rfl⟩ := hC
  obtain ⟨q, hq, rfl⟩ := hD
  have hpq : p ≠ q := by
    intro h
    exact hCD (congrArg (fun I : Ideal R => PrimeSpectrum.zeroLocus (I : Set R)) h)
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  have hpX : p ≤ x.asIdeal := hxp
  have hqX : q ≤ x.asIdeal := hxq
  have hsum : p ⊔ q ≤ x.asIdeal := sup_le hpX hqX
  rw [distinct_minimalPrimes_sup_eq_top hlocal p q hp hq hpq] at hsum
  exact x.isPrime.ne_top (top_unique hsum)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
