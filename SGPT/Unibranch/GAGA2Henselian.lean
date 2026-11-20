import SGPT.Unibranch.ReducedComplexSpaces
import SGPT.Foundations.Analysis.Pending.GermMinimalPolynomial
import Mathlib.RingTheory.Henselian

/-!
# Distinguished factorizations and Henselian analytic local rings

A local ring `R` has *distinguished factorizations* if every monic `P ∈ R[T]` factors as
`P = W Q`, where `W` is monic with all non-leading coefficients in the maximal ideal (a
distinguished, or Weierstrass, polynomial: it reduces to `T^{deg W}` over the residue field)
and `Q` has a unit constant term. Over the residue field this lifts the factorization
`P̄ = T^a Q̄` with `Q̄(0) ≠ 0`, i.e. the root `0` of `P̄` with its full multiplicity.

* `HasDistinguishedFactorization.henselianLocalRing`: such a ring is Henselian (Mathlib's
  `HenselianLocalRing`, simple roots lift).
* `HasDistinguishedFactorization.of_surjective`: the property passes to every local
  quotient, in particular along ring isomorphisms.
* `HasDistinguishedFactorization.isLocalRing_of_isIntegral`: every domain integral over `R`
  is local. (`e` integral with `e ∈ 𝔫₁`, `1 - e ∈ 𝔫₂`: from `P(e) = 0`, `P = W Q`, either
  `Q(e) = 0`, which puts the unit `Q(0)` into `𝔫₁`, or `W(e) = 0`, which puts the unit `W(1)`
  into `𝔫₂`.)
* `HasDistinguishedFactorization.sourceUnibranchReducedRing_iff`: hence a local ring with
  distinguished factorizations is unibranch (in the sense of `def:unibranch:L21`) iff it is a
  domain: the integral closure of a domain in its fraction field is integral over it.
* `hasDistinguishedFactorization_holGerm`: the ring `𝒪_{E,0}` of holomorphic germs has
  distinguished factorizations; this is the Weierstrass preparation theorem for monic
  polynomials (`GermMinimalPolynomial.exists_eq_isWeierstrass_mul`). In particular `𝒪_{E,0}`
  is a Henselian local ring.

These are the Henselian inputs of `prop:unibranch_gaga` (Appendix B of the book): a reduced
analytic local ring is unibranch iff it is a domain (local irreducibility, cf. the book's
remark that in [CAS] unibranchness is called local irreducibility).

Blueprint: `claude-serre-gaga.tex`.
-/

set_option autoImplicit false

open Polynomial IsLocalRing

namespace SGPT.Unibranch

noncomputable section

/-- **Distinguished factorizations.** Every monic polynomial over the local ring `R` is a
monic polynomial whose non-leading coefficients lie in the maximal ideal (a distinguished
polynomial) times a polynomial with unit constant coefficient. -/
def HasDistinguishedFactorization (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ P : R[X], P.Monic → ∃ W Q : R[X], W.Monic ∧
    (∀ j < W.natDegree, W.coeff j ∈ maximalIdeal R) ∧ P = W * Q ∧ IsUnit (Q.coeff 0)

namespace HasDistinguishedFactorization

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A local ring with distinguished factorizations is Henselian: a simple root `a₀` of
`f` modulo the maximal ideal lifts to a root. The distinguished factor of `f(T + a₀)` has
degree one. -/
theorem henselianLocalRing (h : HasDistinguishedFactorization R) : HenselianLocalRing R where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    set g := f.comp (X + C a₀) with hg
    obtain ⟨W, Q, hWm, hWc, hgWQ, hQ⟩ := h g (hf.comp_X_add_C a₀)
    have hg0 : g.eval 0 = f.eval a₀ := by simp [g, eval_comp]
    have hg'0 : g.derivative.eval 0 = f.derivative.eval a₀ := by
      simp [g, derivative_comp, eval_comp]
    have hd : W.natDegree = 1 := by
      rcases Nat.lt_trichotomy W.natDegree 1 with hlt | heq | hgt
      · exfalso
        have hW1 : W = 1 := hWm.natDegree_eq_zero.mp (by omega)
        have h0 : g.eval 0 = Q.coeff 0 := by
          rw [hgWQ, hW1, one_mul, coeff_zero_eq_eval_zero]
        rw [hg0] at h0
        exact (mem_maximalIdeal _).mp h₁ (h0 ▸ hQ)
      · exact heq
      · exfalso
        have hder : g.derivative.eval 0 =
            W.coeff 1 * Q.coeff 0 + W.coeff 0 * Q.derivative.eval 0 := by
          rw [hgWQ, derivative_mul, eval_add, eval_mul, eval_mul, ← coeff_zero_eq_eval_zero,
            ← coeff_zero_eq_eval_zero W, ← coeff_zero_eq_eval_zero Q, coeff_derivative]
          simp
        have hmem : g.derivative.eval 0 ∈ maximalIdeal R := by
          rw [hder]
          exact add_mem (Ideal.mul_mem_right _ _ (hWc 1 hgt))
            (Ideal.mul_mem_right _ _ (hWc 0 (by omega)))
        rw [hg'0] at hmem
        exact (mem_maximalIdeal _).mp hmem h₂
    have hW : W = X + C (W.coeff 0) := hWm.eq_X_add_C hd
    refine ⟨a₀ - W.coeff 0, ?_, ?_⟩
    · have hroot : g.eval (-W.coeff 0) = 0 := by
        rw [hgWQ, eval_mul, hW]
        simp
      have : g.eval (-W.coeff 0) = f.eval (a₀ - W.coeff 0) := by
        simp only [g, eval_comp, eval_add, eval_X, eval_C]
        ring_nf
      rw [IsRoot, ← this, hroot]
    · have : a₀ - W.coeff 0 - a₀ = -W.coeff 0 := by ring
      rw [this]
      exact neg_mem (hWc 0 (by omega))

/-- A surjective ring map from a local ring onto a nontrivial ring maps the maximal ideal
into the nonunits. -/
theorem map_mem_maximalIdeal_of_surjective {S : Type*} [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) {r : R} (hr : r ∈ maximalIdeal R) :
    f r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  obtain ⟨s, hs⟩ := hf ↑u⁻¹
  have h1 : IsUnit (1 - r * s) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hr)
  have h0 : f (1 - r * s) = 0 := by
    rw [map_sub, map_one, map_mul, ← hu, hs, Units.mul_inv, sub_self]
  have := h1.map f
  rw [h0] at this
  exact not_isUnit_zero this

/-- Distinguished factorizations pass to local quotients (surjective images). -/
theorem of_surjective (h : HasDistinguishedFactorization R) {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f) :
    HasDistinguishedFactorization S := by
  intro P hP
  obtain ⟨P', hP'map, -, hP'm⟩ :=
    lifts_and_degree_eq_and_monic ((mem_lifts P).mpr (map_surjective f hf P)) hP
  obtain ⟨W, Q, hWm, hWc, hPWQ, hQ⟩ := h P' hP'm
  refine ⟨W.map f, Q.map f, hWm.map f, fun j hj => ?_, ?_, ?_⟩
  · rw [hWm.natDegree_map f] at hj
    rw [coeff_map]
    exact map_mem_maximalIdeal_of_surjective f hf (hWc j hj)
  · rw [← hP'map, hPWQ, Polynomial.map_mul]
  · rw [coeff_map]
    exact hQ.map f

/-- Distinguished factorizations are invariant under ring isomorphisms. -/
theorem of_ringEquiv (h : HasDistinguishedFactorization R) {S : Type*} [CommRing S]
    [IsLocalRing S] (e : R ≃+* S) : HasDistinguishedFactorization S :=
  h.of_surjective e.toRingHom e.surjective

/-- **Integral elements of a domain.** If `R` has distinguished factorizations and `e` is an
element of a domain `S` integral over `R`, then `e` or `1 - e` is a unit of `S`. -/
theorem isUnit_or_isUnit_one_sub (h : HasDistinguishedFactorization R) {S : Type*}
    [CommRing S] [IsDomain S] [Algebra R S] {e : S} (he : IsIntegral R e) :
    IsUnit e ∨ IsUnit (1 - e) := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨n₁, hn₁, hen₁⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hne.1)
  obtain ⟨n₂, hn₂, hen₂⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hne.2)
  obtain ⟨P, hPm, hPe⟩ := he
  obtain ⟨W, Q, hWm, hWc, hPWQ, hQ⟩ := h P hPm
  have hprod : aeval e W * aeval e Q = 0 := by
    rw [← map_mul, ← hPWQ, aeval_def]
    exact hPe
  rcases mul_eq_zero.mp hprod with hW | hQ0
  · -- `W(1)` is a unit, but `W(1) ≡ W(e) = 0` modulo `1 - e ∈ 𝔫₂`.
    have hunitR : IsUnit (W.eval 1) := by
      by_contra hnu
      have hsum : W.eval 1 = 1 + ∑ i ∈ Finset.range W.natDegree, W.coeff i := by
        rw [eval_eq_sum_range, Finset.sum_range_succ, hWm.coeff_natDegree]
        simp only [one_pow, mul_one]
        ring
      have hmem : ∑ i ∈ Finset.range W.natDegree, W.coeff i ∈ maximalIdeal R :=
        Ideal.sum_mem _ fun i hi => hWc i (Finset.mem_range.mp hi)
      have h1 : (1 : R) ∈ maximalIdeal R := by
        have := sub_mem ((mem_maximalIdeal _).mpr hnu) hmem
        rwa [hsum, add_sub_cancel_right] at this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have h1 : aeval (1 : S) W = algebraMap R S (W.eval 1) := by
      rw [← map_one (algebraMap R S), aeval_algebraMap_apply, coe_aeval_eq_eval]
    have hdvd : (e - 1) ∣ aeval e W - aeval 1 W := by
      simp only [aeval_def, eval₂_eq_eval_map]
      exact sub_dvd_eval_sub _ _ _
    have hmem : aeval (1 : S) W ∈ n₂ := by
      obtain ⟨c, hc⟩ := hdvd
      have hdiff : aeval e W - aeval 1 W ∈ n₂ := by
        rw [hc]
        apply Ideal.mul_mem_right
        have : e - 1 = -(1 - e) := by ring
        rw [this]
        exact n₂.neg_mem hen₂
      rw [hW, zero_sub] at hdiff
      simpa using n₂.neg_mem hdiff
    rw [h1] at hmem
    exact hn₂.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hunitR.map _))
  · -- `Q(0)` is a unit, but `Q(0) ≡ Q(e) = 0` modulo `e ∈ 𝔫₁`.
    have hdecomp : aeval e Q = algebraMap R S (Q.coeff 0) + e * aeval e Q.divX := by
      conv_lhs => rw [← X_mul_divX_add Q]
      rw [map_add, map_mul, aeval_X, aeval_C]
      ring
    have hmem : algebraMap R S (Q.coeff 0) ∈ n₁ := by
      have : algebraMap R S (Q.coeff 0) = -(e * aeval e Q.divX) := by
        rw [hQ0] at hdecomp
        linear_combination -hdecomp
      rw [this]
      exact n₁.neg_mem (Ideal.mul_mem_right _ _ hen₁)
    exact hn₁.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hQ.map _))

/-- Every domain integral over a local ring with distinguished factorizations is local. -/
theorem isLocalRing_of_isIntegral (h : HasDistinguishedFactorization R) {S : Type*}
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] : IsLocalRing S :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun e =>
    h.isUnit_or_isUnit_one_sub (Algebra.IsIntegral.isIntegral e)

/-- **Unibranch iff domain.** For a local ring with distinguished factorizations, the
unibranch condition of `def:unibranch:L21` (a domain whose integral closure in its fraction
field is local) is equivalent to being a domain. -/
theorem sourceUnibranchReducedRing_iff (h : HasDistinguishedFactorization R) :
    SourceUnibranchReducedRing R ↔ IsDomain R := by
  refine ⟨fun hR => hR.1, fun hD => ⟨hD, ?_⟩⟩
  exact h.isLocalRing_of_isIntegral (S := integralClosure R (FractionRing R))

end HasDistinguishedFactorization

/-! ### Holomorphic germs -/

section HolGerm

open SGPT.Foundations.Analysis.Pending

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Weierstrass preparation for monic polynomials.** The ring `𝒪_{E,0}` of holomorphic
germs has distinguished factorizations. -/
theorem hasDistinguishedFactorization_holGerm : HasDistinguishedFactorization (HolGerm E) := by
  intro P hP
  obtain ⟨W, Q, hWm, hW0, -, hPWQ, hQ⟩ := GermMinimalPolynomial.exists_eq_isWeierstrass_mul hP
  exact ⟨W, Q, hWm, fun j hj => (HolGerm.mem_maximalIdeal_iff _).mpr (hW0 j hj), hPWQ,
    (HolGerm.isUnit_iff_eval_ne_zero _).mpr hQ⟩

/-- **The analytic local ring `𝒪_{E,0}` is Henselian.** -/
instance henselianLocalRing_holGerm : HenselianLocalRing (HolGerm E) :=
  (hasDistinguishedFactorization_holGerm E).henselianLocalRing

/-- Every local quotient of `𝒪_{E,0}` has distinguished factorizations. -/
theorem hasDistinguishedFactorization_holGerm_quotient (J : Ideal (HolGerm E))
    [IsLocalRing (HolGerm E ⧸ J)] : HasDistinguishedFactorization (HolGerm E ⧸ J) :=
  (hasDistinguishedFactorization_holGerm E).of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective

/-- A reduced quotient `𝒪_{E,0}/J` (with `J` radical and proper) is unibranch iff `J` is
prime, i.e. iff the corresponding analytic germ is irreducible. -/
theorem sourceUnibranchReducedRing_holGerm_quotient_iff (J : Ideal (HolGerm E))
    [IsLocalRing (HolGerm E ⧸ J)] :
    SourceUnibranchReducedRing (HolGerm E ⧸ J) ↔ J.IsPrime := by
  rw [(hasDistinguishedFactorization_holGerm_quotient E J).sourceUnibranchReducedRing_iff,
    Ideal.Quotient.isDomain_iff_prime]

end HolGerm

end

end SGPT.Unibranch
