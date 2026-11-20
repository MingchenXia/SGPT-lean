import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Local factorization of locally principal ideals along prime divisors

Step (b) of the reduction of the Hodge-type inequality ([BHJ17, Lemma 6.14], blueprint
`claude-bj-hodge.tex`) splits a vertical Cartier divisor on a regular model along the components
of a strict normal crossings divisor. Its commutative-algebra core is proved here, for a Noetherian
domain `A` (the ring of an affine open), a prime `p` (a point) and a localization `R = A_p` (its
local ring):

* `exists_eq_prod_pow_mul`: in a Noetherian domain, a nonzero element factors as
  `∏ z_j ^ a_j * h` with no `z_j` dividing `h` (Krull's intersection theorem);
* `map_eq_prod_pow_of_supp`: if `J A_p = (g)` with `g ≠ 0`, the primes `P_j ≤ p` have principal
  nonzero localizations `P_j A_p = (z_j)`, and every prime `q ≤ p` containing `J` contains some
  `P_j` ("the support of `J` lies in the union of the components"), then
  `J A_p = ∏ (P_j A_p) ^ a_j` (Krull's principal ideal theorem forces the cofactor to be a unit);
* `exponent_eq_of_map_eq_prod_pow`: the exponent `a_j` is the order of `J` at `P_j`, i.e. it is
  read off in the localization `A_{P_j}` (so it does not depend on the point `p`).

No unique factorization in the regular local rings is used.
-/

set_option autoImplicit false

namespace SGPT.NAPotential.BJHodge

section domain

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- In a Noetherian domain, a nonzero element is `z ^ n * h` with `z ∤ h`, for any nonunit `z`
(Krull's intersection theorem). -/
theorem exists_eq_pow_mul_not_dvd {z g : R} (hz : ¬IsUnit z) (hg : g ≠ 0) :
    ∃ (n : ℕ) (h : R), g = z ^ n * h ∧ ¬ z ∣ h := by
  classical
  have hex : ∃ n, ¬ z ^ n ∣ g := by
    by_contra hall
    push Not at hall
    apply hg
    have htop : Ideal.span {z} ≠ ⊤ := fun h => hz (Ideal.span_singleton_eq_top.mp h)
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {z}) htop
    have hmem : g ∈ ⨅ i : ℕ, Ideal.span {z} ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hall i
    rw [h0] at hmem
    exact (Submodule.mem_bot R).mp hmem
  have hn : ¬ z ^ Nat.find hex ∣ g := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hn
    rw [h0, pow_zero]
    exact one_dvd g
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdvd : z ^ m ∣ g := not_not.mp (Nat.find_min hex (show m < Nat.find hex by omega))
  obtain ⟨h, rfl⟩ := hdvd
  refine ⟨m, h, rfl, fun hzh => hn ?_⟩
  rw [hm, pow_succ]
  exact mul_dvd_mul_left _ hzh

/-- In a Noetherian domain, a nonzero element factors as `(∏ j ∈ S, z_j ^ a_j) * h` with no
`z_j` (`j ∈ S`) dividing `h`. -/
theorem exists_eq_prod_pow_mul {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ι → R)
    (hz : ∀ j ∈ S, ¬IsUnit (z j)) {g : R} (hg : g ≠ 0) :
    ∃ (a : ι → ℕ) (h : R), g = (∏ j ∈ S, z j ^ a j) * h ∧ ∀ j ∈ S, ¬ z j ∣ h := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, g, by simp, by simp⟩
  | insert i S hi ih =>
    obtain ⟨a, h', hg', hh'⟩ := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    have h'0 : h' ≠ 0 := by
      rintro rfl
      exact hg (by rw [hg', mul_zero])
    obtain ⟨n, h, rfl, hzh⟩ :=
      exists_eq_pow_mul_not_dvd (hz i (Finset.mem_insert_self i S)) h'0
    refine ⟨Function.update a i n, h, ?_, ?_⟩
    · rw [Finset.prod_insert hi, Function.update_self,
        Finset.prod_congr rfl (fun j hj => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]), hg']
      ring
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hzh
      · exact fun hd => hh' j hj (hd.trans (dvd_mul_left h _))

end domain

section localization

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

omit [IsDomain A] [IsNoetherianRing A] in
/-- A prime `P ≤ p` stays prime in the localization at `p`. -/
theorem isPrime_map_of_le (p : Ideal A) [p.IsPrime] (R : Type*) [CommRing R] [Algebra A R]
    [IsLocalization.AtPrime R p] (P : Ideal A) [P.IsPrime] (hP : P ≤ p) :
    (P.map (algebraMap A R)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl R P inferInstance
    (Set.disjoint_left.mpr fun _ hx hxP => hx (hP hxP))

/-- **Local factorization along components.** Let `R = A_p`. If `J A_p = (g)` with `g ≠ 0`, the
primes `P_j ≤ p` (`j ∈ S`) have `P_j A_p = (z_j)` with `z_j ≠ 0`, and every prime `q ≤ p` containing
`J` contains some `P_j`, then `J A_p = ∏_{j ∈ S} (P_j A_p) ^ a_j` for some exponents `a_j`. -/
theorem map_eq_prod_pow_of_supp (p : Ideal A) [p.IsPrime] (R : Type*) [CommRing R] [Algebra A R]
    [IsLocalization.AtPrime R p] {ι : Type*} (S : Finset ι) (P : ι → Ideal A)
    (hPprime : ∀ j ∈ S, (P j).IsPrime) (hPp : ∀ j ∈ S, P j ≤ p)
    (z : ι → R) (hz : ∀ j ∈ S, (P j).map (algebraMap A R) = Ideal.span {z j})
    (hz0 : ∀ j ∈ S, z j ≠ 0)
    (J : Ideal A) {g : R} (hg : J.map (algebraMap A R) = Ideal.span {g}) (hg0 : g ≠ 0)
    (hsupp : ∀ q : Ideal A, q.IsPrime → q ≤ p → J ≤ q → ∃ j ∈ S, P j ≤ q) :
    ∃ a : ι → ℕ, J.map (algebraMap A R) = ∏ j ∈ S, ((P j).map (algebraMap A R)) ^ a j := by
  classical
  have : IsDomain R := IsLocalization.isDomain_of_atPrime R p
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  -- the local equations generate prime ideals
  have hzprime : ∀ j ∈ S, (Ideal.span {z j}).IsPrime := by
    intro j hj
    have := hPprime j hj
    rw [← hz j hj]
    exact isPrime_map_of_le p R (P j) (hPp j hj)
  have hzu : ∀ j ∈ S, ¬IsUnit (z j) := fun j hj hu =>
    (hzprime j hj).ne_top (Ideal.span_singleton_eq_top.mpr hu)
  obtain ⟨a, h, hgh, hndvd⟩ := exists_eq_prod_pow_mul S z hzu hg0
  -- the cofactor is a unit (Krull's principal ideal theorem)
  have hhu : IsUnit h := by
    by_contra hhu
    have hspan : Ideal.span {h} ≠ ⊤ := fun ht => hhu (Ideal.span_singleton_eq_top.mp ht)
    obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes hspan
    have hQprime : Q.IsPrime := hQ.1.1
    have hhQ : Ideal.span {h} ≤ Q := hQ.1.2
    have : (Ideal.span {h}).IsPrincipal := ⟨⟨h, rfl⟩⟩
    have hht : Q.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {h}) Q hQ
    let Q' := Q.comap (algebraMap A R)
    obtain ⟨hQ'prime, hQ'disj⟩ :=
      (IsLocalization.isPrime_iff_isPrime_disjoint p.primeCompl R Q).mp hQprime
    have hQ'p : Q' ≤ p := by
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.mp hQ'disj (show x ∈ p.primeCompl from hxp) hx
    have hJQ : J ≤ Q' := by
      intro x hx
      change algebraMap A R x ∈ Q
      have hmem : algebraMap A R x ∈ J.map (algebraMap A R) := Ideal.mem_map_of_mem _ hx
      rw [hg, Ideal.mem_span_singleton] at hmem
      apply hhQ
      rw [Ideal.mem_span_singleton]
      exact (show h ∣ g from ⟨_, hgh.trans (mul_comm _ _)⟩).trans hmem
    obtain ⟨j, hj, hPQ⟩ := hsupp Q' hQ'prime hQ'p hJQ
    have hzQ : Ideal.span {z j} ≤ Q := by
      rw [← hz j hj]
      exact Ideal.map_le_iff_le_comap.mpr hPQ
    have := hzprime j hj
    have hz1 : 1 ≤ (Ideal.span {z j}).height := by
      rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot,
        Ideal.span_singleton_eq_bot]
      exact hz0 j hj
    have heq : Ideal.span {z j} = Q := Ideal.eq_of_le_of_height_le (Ideal.span {z j}) hzQ (hht.trans hz1)
    apply hndvd j hj
    rw [← Ideal.mem_span_singleton, heq]
    exact hhQ (Ideal.mem_span_singleton_self h)
  refine ⟨a, ?_⟩
  rw [hg, hgh, Ideal.span_singleton_mul_right_unit hhu, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [hz j hj, Ideal.span_singleton_pow]

omit [IsNoetherianRing A] in
/-- **The exponents are orders at the components.** In the situation of
`map_eq_prod_pow_of_supp`, let `P = P_j` (`j ∈ S`), with `P_i ⊄ P` for the other `i ∈ S`, and let
`B = A_P`. If `J A_P = (P A_P) ^ d` and `P A_P = (w)` with `w ≠ 0`, then `a_j = d`. -/
theorem exponent_eq_of_map_eq_prod_pow (p P : Ideal A) [p.IsPrime] [P.IsPrime] (hPp : P ≤ p)
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p]
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B P]
    {ι : Type*} (S : Finset ι) (Q : ι → Ideal A) (j : ι) (hj : j ∈ S) (hQj : Q j = P)
    (hinc : ∀ i ∈ S, i ≠ j → ¬ Q i ≤ P)
    (J : Ideal A) (a : ι → ℕ)
    (ha : J.map (algebraMap A R) = ∏ i ∈ S, ((Q i).map (algebraMap A R)) ^ a i)
    (d : ℕ) (hd : J.map (algebraMap A B) = (P.map (algebraMap A B)) ^ d)
    (w : B) (hw : P.map (algebraMap A B) = Ideal.span {w}) (hw0 : w ≠ 0) :
    a j = d := by
  classical
  have : IsDomain B := IsLocalization.isDomain_of_atPrime B P
  have hle : p.primeCompl ≤ P.primeCompl.comap (RingHom.id A) := fun x hx hxP => hx (hPp hxP)
  let φ : R →+* B := IsLocalization.map (M := p.primeCompl) (S := R) B (RingHom.id A) hle
  have hφ : φ.comp (algebraMap A R) = algebraMap A B := by
    rw [IsLocalization.map_comp]
    rfl
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A R)).map φ = I.map (algebraMap A B) := by
    intro I
    rw [Ideal.map_map, hφ]
  have htop : ∀ i ∈ S, i ≠ j → (Q i).map (algebraMap A B) = ⊤ := by
    intro i hi hne
    obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp (hinc i hi hne)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxQ)
      (IsLocalization.map_units B (⟨x, hxP⟩ : P.primeCompl))
  have hJB : J.map (algebraMap A B) = (P.map (algebraMap A B)) ^ a j := by
    rw [← hmap, ha]
    change Ideal.mapHom φ (∏ i ∈ S, ((Q i).map (algebraMap A R)) ^ a i) = _
    rw [map_prod]
    simp only [map_pow, Ideal.mapHom_apply, hmap]
    rw [Finset.prod_eq_single_of_mem j hj (fun i hi hne => by rw [htop i hi hne, Ideal.top_pow, Ideal.one_eq_top]),
      hQj]
  have hwu : ¬IsUnit w := by
    intro hu
    have hprime := isPrime_map_of_le P B P le_rfl
    exact hprime.ne_top (by rw [hw]; exact Ideal.span_singleton_eq_top.mpr hu)
  rw [hd, hw, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at hJB
  exact le_antisymm ((pow_dvd_pow_iff hw0 hwu).mp hJB.symm.dvd)
    ((pow_dvd_pow_iff hw0 hwu).mp hJB.dvd)

end localization

end SGPT.NAPotential.BJHodge
