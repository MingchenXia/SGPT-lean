import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import SGPT.Unibranch.GAGA2Normalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Zariski's realization of a divisorial valuation: the commutative algebra

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`, the cited
[CFKLRS17, Theorem 2.9]. Its proof starts from the first coordinate `ν₁` of a valuation
`ν : ℂ(X)^× → ℤⁿ_lex` of maximal rational rank: `ν₁` is a discrete valuation whose residue field
has transcendence degree `n - 1` (lane OF4:
`SGPT.Okounkov.OF4.exists_residue_independent_prefixOne`,
`not_residue_independent_prefixOne`), i.e. a *divisorial* valuation, and Zariski's theorem
realizes it as the order of vanishing `ord_E` along a prime divisor `E` of a normal model.

This file proves the commutative algebra of Zariski's argument on an affine chart.

* `exists_algebraicIndependent_option_of_lt` (**transcendence degree drops along primes**): if
  `p ⊊ q` are primes of a `k`-algebra `A` and `a₁, …, a_r ∈ A` have algebraically independent
  images in `A ⧸ q`, then some `x ∈ A` makes `a₁, …, a_r, x` independent modulo `p`. (Proof: else
  an element `t ∈ q ∖ p` is algebraic over `k[a]` modulo `p`, so the ideal `q / p` meets
  `k[a] ⊆ A ⧸ p` nontrivially, contradicting the independence modulo `q`.)
* `eq_bot_or_eq_of_le_of_residue_independent`: if `trdeg_k A ≤ m + 1` and `A ⧸ q` contains `m`
  independent elements, every prime `p ⊆ q` is `⊥` or `q`: `q` has height `≤ 1`.
* `isDiscreteValuationRing_localization`: for `A` moreover Noetherian and integrally closed and
  `q ≠ 0`, `A_q` is a discrete valuation ring.
* `nonneg_iff_exists_mul_mem` (**Zariski's realization on an affine chart**): if a valuation `v`
  of `K = Frac A` is nonnegative on `A`, `q = {a ∈ A : v(a) > 0}` and `A_q` is a valuation ring,
  then `{x ∈ K : v(x) ≥ 0} = A_q`: the valuation ring of `v` is the local ring of the prime divisor
  `V(q)` of `Spec A`.
* `nonneg_of_isIntegral`: valuation rings are integrally closed (to pass from a finitely generated
  algebra to its normalization).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open IsLocalRing

section Transcendence

variable {k : Type*} [Field k]

/-- **Transcendence degree drops along a strict inclusion of primes.** If `p < q` are primes of a
`k`-algebra `A` and the images of `a : ι → A` in `A ⧸ q` are algebraically independent, there is
`x ∈ A` such that the images of `x, a` in `A ⧸ p` are algebraically independent. -/
theorem exists_algebraicIndependent_option_of_lt {A : Type*} [CommRing A] [Algebra k A]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (hpq : p < q) {ι : Type*} (a : ι → A)
    (ha : AlgebraicIndependent k (Ideal.Quotient.mk q ∘ a)) :
    ∃ x : A, AlgebraicIndependent k (Ideal.Quotient.mk p ∘ fun o : Option ι => o.elim x a) := by
  classical
  let φ : A ⧸ p →ₐ[k] A ⧸ q := Ideal.Quotient.factorₐ k hpq.le
  have ha' : AlgebraicIndependent k (Ideal.Quotient.mk p ∘ a) :=
    AlgebraicIndependent.of_comp φ ha
  obtain ⟨t, htq, htp⟩ := SetLike.exists_of_lt hpq
  by_contra hcon
  have h1 := not_exists.mp hcon t
  have heq : (Ideal.Quotient.mk p ∘ fun o : Option ι => o.elim t a) =
      fun o : Option ι => o.elim (Ideal.Quotient.mk p t) (Ideal.Quotient.mk p ∘ a) := by
    funext o
    cases o <;> rfl
  rw [heq, ha'.option_iff_transcendental] at h1
  have halg : IsAlgebraic (Algebra.adjoin k (Set.range (Ideal.Quotient.mk p ∘ a)))
      (Ideal.Quotient.mk p t) := not_not.mp h1
  have hne : Ideal.Quotient.mk p t ≠ 0 := by
    rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : Ideal.Quotient.mk p t ∈ q.map (Ideal.Quotient.mk p) := Ideal.mem_map_of_mem _ htq
  have hcomap := Ideal.comap_ne_bot_of_algebraic_mem hne hmem halg
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  have hrmem : (r : A ⧸ p) ∈ (MvPolynomial.aeval (R := k) (Ideal.Quotient.mk p ∘ a)).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨P, hP⟩ := hrmem
  have hPr : MvPolynomial.aeval (Ideal.Quotient.mk p ∘ a) P = (r : A ⧸ p) := hP
  have hcomp : MvPolynomial.aeval (Ideal.Quotient.mk p ∘ a) P =
      Ideal.Quotient.mk p (MvPolynomial.aeval a P) := by
    have h := MvPolynomial.comp_aeval_apply (R := k) (f := a) (Ideal.Quotient.mkₐ k p) P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    exact h.symm
  have hrq : (r : A ⧸ p) ∈ q.map (Ideal.Quotient.mk p) := hr
  rw [← hPr, hcomp, Ideal.mem_quotient_iff_mem hpq.le] at hrq
  have hzero : MvPolynomial.aeval (Ideal.Quotient.mk q ∘ a) P = 0 := by
    have h := MvPolynomial.comp_aeval_apply (R := k) (f := a) (Ideal.Quotient.mkₐ k q) P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [show (Ideal.Quotient.mk q ∘ a) = fun i => Ideal.Quotient.mk q (a i) from rfl, ← h,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hrq
  have hP0 : P = 0 := (injective_iff_map_eq_zero _).mp ha P hzero
  apply hr0
  apply Subtype.ext
  rw [← hPr, hP0, map_zero]
  rfl

/-- **Height at most one.** If `A` is a domain over `k` of transcendence degree `≤ m + 1` (no
`m + 2` algebraically independent elements) and `A ⧸ q` contains `m` algebraically independent
elements, then every prime `p ⊆ q` is `⊥` or `q`. -/
theorem eq_bot_or_eq_of_le_of_residue_independent {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] {m : ℕ} (htr : ∀ z : Fin (m + 2) → A, ¬ AlgebraicIndependent k z)
    {q : Ideal A} [q.IsPrime] (y : Fin m → A)
    (hy : AlgebraicIndependent k (Ideal.Quotient.mk q ∘ y))
    (p : Ideal A) [p.IsPrime] (hpq : p ≤ q) : p = ⊥ ∨ p = q := by
  by_contra h
  push Not at h
  obtain ⟨hp0, hpq'⟩ := h
  have hlt : p < q := lt_of_le_of_ne hpq hpq'
  obtain ⟨x, hx⟩ := exists_algebraicIndependent_option_of_lt hlt y hy
  have hbot : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  obtain ⟨z, hz⟩ := exists_algebraicIndependent_option_of_lt hbot _ hx
  have hz' : AlgebraicIndependent k
      (fun o : Option (Option (Fin m)) => o.elim z (fun o' : Option (Fin m) => o'.elim x y)) :=
    AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ k ⊥) hz
  let e : Fin (m + 2) ≃ Option (Option (Fin m)) :=
    (finSuccEquiv (m + 1)).trans (Equiv.optionCongr (finSuccEquiv m))
  exact htr _ (hz'.comp e e.injective)

end Transcendence

section DVR

/-- **The local ring of a height-one prime of a normal Noetherian domain is a DVR.** Here the
height-one condition is: every prime `p ⊆ q` is `⊥` or `q`. -/
theorem isDiscreteValuationRing_localization {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥)
    (hheight : ∀ p : Ideal A, p.IsPrime → p ≤ q → p = ⊥ ∨ p = q) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  let R := Localization.AtPrime q
  have hM : q.primeCompl ≤ nonZeroDivisors A := Ideal.primeCompl_le_nonZeroDivisors q
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R q.primeCompl hM
  have hmax : (maximalIdeal R).comap (algebraMap A R) = q :=
    IsLocalization.AtPrime.under_maximalIdeal R q
  have hm : maximalIdeal R ≠ ⊥ := by
    intro h
    apply hq
    rw [← hmax, h, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsLocalization.injective R hM)]
  have hnf : ¬IsField R := fun hF => hm ((isField_iff_maximalIdeal_eq).mp hF)
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have key := (IsDiscreteValuationRing.TFAE R hnf).out 0 3
  refine key.mpr ⟨inferInstance, maximalIdeal R, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  obtain ⟨hP0, hPprime⟩ := hP
  have hPle : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hPprime.ne_top
  have hcomap_le : P.comap (algebraMap A R) ≤ q :=
    le_of_le_of_eq (Ideal.comap_mono hPle) hmax
  have hPeq : P = (P.comap (algebraMap A R)).map (algebraMap A R) :=
    (IsLocalization.map_under q.primeCompl R P).symm
  rcases hheight _ (Ideal.IsPrime.comap _) hcomap_le with h | h
  · exact absurd (by rw [hPeq, h, Ideal.map_bot]) hP0
  · rw [hPeq, h, IsLocalization.AtPrime.map_eq_maximalIdeal]

end DVR

section ValuationRingComparison

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- **Zariski's realization on an affine chart.** Let `v` be a valuation of `K = Frac A`,
nonnegative on `A`, let `q = {a ∈ A : v(a) > 0}` and assume `A_q` is a valuation ring (e.g. a
DVR). Then the valuation ring of `v` is `A_q`: `v(x) ≥ 0` iff `x s ∈ A` for some `s ∈ A ∖ q`. -/
theorem nonneg_iff_exists_mul_mem (v : AddValuation K Γ₀)
    (hA : ∀ a : A, 0 ≤ v (algebraMap A K a)) (q : Ideal A) [q.IsPrime]
    (hq : ∀ a : A, a ∈ q ↔ 0 < v (algebraMap A K a))
    [ValuationRing (Localization.AtPrime q)] (x : K) :
    0 ≤ v x ↔ ∃ a s : A, s ∉ q ∧ x * algebraMap A K s = algebraMap A K a := by
  have hzero : ∀ s : A, s ∉ q → v (algebraMap A K s) = 0 := by
    intro s hs
    refine le_antisymm ?_ (hA s)
    by_contra h
    exact hs ((hq s).mpr (lt_of_not_ge h))
  constructor
  swap
  · rintro ⟨a, s, hs, h⟩
    have h' := congrArg v h
    rw [v.map_mul, hzero s hs, add_zero] at h'
    rw [h']
    exact hA a
  intro hx
  let R := Localization.AtPrime q
  have hM : q.primeCompl ≤ nonZeroDivisors A := Ideal.primeCompl_le_nonZeroDivisors q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  have hinjR : Function.Injective (algebraMap A R) := IsLocalization.injective R hM
  rcases ValuationRing.dvd_total (algebraMap A R b) (algebraMap A R a) with hba | hab
  · -- `b ∣ a` in `A_q`: `a s = b c`, so `x s = c`
    obtain ⟨w, hw⟩ := hba
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl w
    have hcs : algebraMap A R (a * s) = algebraMap A R (b * c) := by
      rw [map_mul, hw, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    have hA' : a * s = b * c := hinjR hcs
    refine ⟨c, s, s.2, ?_⟩
    rw [div_mul_eq_mul_div, ← map_mul, hA', map_mul, mul_div_cancel_left₀ _ hbK]
  · -- `a ∣ b` in `A_q`: `b s = a c`, so `x c = s`; `c ∈ q` would give `v(x) < 0`
    obtain ⟨w, hw⟩ := hab
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl w
    have hcs : algebraMap A R (b * s) = algebraMap A R (a * c) := by
      rw [map_mul, hw, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    have hA' : b * s = a * c := hinjR hcs
    have hxc : algebraMap A K a / algebraMap A K b * algebraMap A K c = algebraMap A K s := by
      rw [div_mul_eq_mul_div, ← map_mul, ← hA', map_mul, mul_div_cancel_left₀ _ hbK]
    by_cases hc : c ∈ q
    · exfalso
      have h' := congrArg v hxc
      rw [v.map_mul, hzero s s.2] at h'
      have hpos := (hq c).mp hc
      have hle : v (algebraMap A K c) ≤
          v (algebraMap A K a / algebraMap A K b) + v (algebraMap A K c) :=
        le_add_of_nonneg_left hx
      rw [h'] at hle
      exact lt_irrefl _ (lt_of_lt_of_le hpos hle)
    · exact ⟨s, c, hc, hxc⟩

end ValuationRingComparison

section Integral

variable {K : Type*} [Field K] {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- **Valuation rings are integrally closed**: an element integral over a ring on which `v ≥ 0`
has `v ≥ 0`. -/
theorem nonneg_of_isIntegral {R : Type*} [CommRing R] [Algebra R K]
    (v : AddValuation K (WithTop G)) (hR : ∀ r : R, 0 ≤ v (algebraMap R K r)) {x : K}
    (hx : IsIntegral R x) : 0 ≤ v x := by
  by_contra hneg
  push Not at hneg
  obtain ⟨p, hm, hp⟩ := hx
  have hxtop : v x ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hneg le_top)
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp hxtop
  have hg0 : g < 0 := by
    rw [← hg] at hneg
    exact WithTop.coe_lt_coe.mp hneg
  by_cases hn : p.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have h1 : c = 1 := by simpa using hm.leadingCoeff
    simp [h1] at hp
  set d := p.natDegree with hd
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul,
    add_eq_zero_iff_eq_neg] at hp
  have hval := congrArg v hp
  rw [AddValuation.map_neg, AddValuation.map_pow, ← hg] at hval
  have hlt : ((d • g : G) : WithTop G) < v (∑ i ∈ Finset.range d,
      algebraMap R K (p.coeff i) * x ^ i) := by
    refine v.map_lt_sum (WithTop.coe_ne_top) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [v.map_mul, AddValuation.map_pow, ← hg]
    refine lt_of_lt_of_le ?_ (le_add_of_nonneg_left (hR _))
    rw [← WithTop.coe_nsmul]
    refine WithTop.coe_lt_coe.mpr ?_
    have hdi : d = i + (d - i) := by omega
    rw [hdi, add_nsmul]
    refine add_lt_of_neg_right _ ?_
    exact nsmul_neg hg0 (by omega)
  rw [hval, ← WithTop.coe_nsmul] at hlt
  exact lt_irrefl _ hlt

end Integral

section Model

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]
  [Nontrivial Γ₀]

omit [Field K] in
/-- In a nontrivial linearly ordered monoid with top, `0 < ⊤`. -/
theorem zero_lt_top_of_nontrivial : (0 : Γ₀) < ⊤ := by
  refine lt_of_le_of_ne le_top fun h => ?_
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ₀
  apply hab
  calc a = a + 0 := (add_zero a).symm
    _ = a + ⊤ := by rw [h]
    _ = ⊤ := add_top a
    _ = b + ⊤ := (add_top b).symm
    _ = b + 0 := by rw [h]
    _ = b := add_zero b

/-- The centre `{a ∈ A : v(a) > 0}` of a valuation `v` of `K` nonnegative on `A`. -/
def centerIdeal {A : Type*} [CommRing A] [Algebra A K] (v : AddValuation K Γ₀)
    (hA : ∀ a : A, 0 ≤ v (algebraMap A K a)) : Ideal A where
  carrier := {a | 0 < v (algebraMap A K a)}
  zero_mem' := by
    change 0 < v (algebraMap A K 0)
    rw [map_zero, v.map_zero]
    exact zero_lt_top_of_nontrivial
  add_mem' {a b} ha hb := by
    change 0 < v (algebraMap A K (a + b))
    rw [map_add]
    exact lt_of_lt_of_le (lt_min ha hb) (v.map_add _ _)
  smul_mem' c a ha := by
    change 0 < v (algebraMap A K (c * a))
    rw [map_mul, v.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (hA c))

theorem mem_centerIdeal {A : Type*} [CommRing A] [Algebra A K] (v : AddValuation K Γ₀)
    (hA : ∀ a : A, 0 ≤ v (algebraMap A K a)) (a : A) :
    a ∈ centerIdeal v hA ↔ 0 < v (algebraMap A K a) := Iff.rfl

theorem centerIdeal_isPrime {A : Type*} [CommRing A] [Algebra A K] (v : AddValuation K Γ₀)
    (hA : ∀ a : A, 0 ≤ v (algebraMap A K a)) : (centerIdeal v hA).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : A) ∈ centerIdeal v hA := by rw [h]; trivial
    rw [mem_centerIdeal, map_one, v.map_one] at h1
    exact lt_irrefl _ h1
  · rw [mem_centerIdeal, map_mul, v.map_mul] at hab
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    rw [mem_centerIdeal, not_lt] at ha hb
    have ha0 : v (algebraMap A K a) = 0 := le_antisymm ha (hA a)
    have hb0 : v (algebraMap A K b) = 0 := le_antisymm hb (hA b)
    rw [ha0, hb0, add_zero] at hab
    exact lt_irrefl _ hab

end Model

end SGPT.Okounkov.OF6
