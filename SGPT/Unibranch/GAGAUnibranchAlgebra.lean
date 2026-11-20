import SGPT.Unibranch.ReducedComplexSpaces
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties

/-!
# Unibranch local rings: flat descent and passage from closed points

This file supplies the commutative algebra used for `prop:unibranch_gaga`
(Appendix B of the book).

* `SourceUnibranchLocalRing R` is the unibranch notion of the Stacks project,
  Tag 0BPZ: the reduction `R_red` is a domain and the integral closure of
  `R_red` in its fraction field is local. On reduced rings it is the existing
  `SourceUnibranchReducedRing` used by `def:unibranch:L21`.
* `isUnit_integralClosure_iff`: an integral element `z` is a unit of the
  integral closure iff it is a root of a polynomial with unit constant term.
* `sourceUnibranchReducedRing_of_flat` (flat descent): if `A → B` is a flat
  local homomorphism of local rings, `A` is reduced and `B` is unibranch, then
  `A` is unibranch. The proof uses the equational criterion of flatness on
  the homogenised equation of an integral element.
* `sourceUnibranchReducedRing_localization_of_maximal`: in a Jacobson ring,
  unibranchness of all localizations at maximal ideals implies it at all primes;
  `schemeIsUnibranch_of_closedPoints` is the scheme form (Stacks 0BQ2), for reduced
  schemes with Jacobson underlying space, e.g. reduced schemes of finite type over `ℂ`.
  The book's proof of `prop:unibranch_gaga` only treats closed points; this supplies
  the passage to all scheme points.

Blueprint: `claude-gaga2.tex`.
-/

set_option autoImplicit false

open Polynomial

namespace SGPT.Unibranch

noncomputable section

/-! ### The Stacks notion of a unibranch local ring -/

/-- Stacks Tag 0BPZ: the reduction is a domain whose integral closure in its fraction
field is local. This is the algebraic notion used in `prop:unibranch_gaga`. -/
def SourceUnibranchLocalRing (R : Type*) [CommRing R] : Prop :=
  SourceUnibranchReducedRing (R ⧸ nilradical R)

/-- On reduced rings the Stacks notion is the reduced-ring notion of `def:unibranch:L21`. -/
theorem sourceUnibranchLocalRing_iff_of_isReduced (R : Type*) [CommRing R] [IsReduced R] :
    SourceUnibranchLocalRing R ↔ SourceUnibranchReducedRing R :=
  sourceUnibranchReducedRing_iff_of_ringEquiv
    ((Ideal.quotEquivOfEq ((nilradical_eq_zero R).trans Ideal.zero_eq_bot)).trans
      (RingEquiv.quotientBot R))

private theorem nilradical_eq_map_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : nilradical S = Ideal.map (e : R →+* S) (nilradical R) := by
  rw [Ideal.map_comap_of_equiv]
  ext x
  simp only [Ideal.mem_comap, mem_nilradical]
  exact (IsNilpotent.map_iff e.symm.injective).symm

/-- Ring isomorphisms preserve and reflect the Stacks notion. -/
theorem sourceUnibranchLocalRing_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : SourceUnibranchLocalRing R ↔ SourceUnibranchLocalRing S :=
  sourceUnibranchReducedRing_iff_of_ringEquiv
    (Ideal.quotientEquiv _ _ e (nilradical_eq_map_of_ringEquiv e))

/-! ### Units of an integral closure -/

/-- An element of the integral closure is a unit there iff it is a root of a polynomial
whose constant coefficient is a unit. -/
theorem isUnit_integralClosure_iff {R F : Type*} [CommRing R] [CommRing F] [Algebra R F]
    (z : integralClosure R F) :
    IsUnit z ↔ ∃ Q : R[X], aeval (z : F) Q = 0 ∧ IsUnit (Q.coeff 0) := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨P, hPm, hP⟩ := (↑u⁻¹ : integralClosure R F).property
    have hmul : ((↑u : integralClosure R F) : F) * ((↑u⁻¹ : integralClosure R F) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    let : Invertible ((↑u⁻¹ : integralClosure R F) : F) :=
      ⟨((↑u : integralClosure R F) : F), hmul, by rw [mul_comm]; exact hmul⟩
    refine ⟨P.reverse, ?_, ?_⟩
    · have h : eval₂ (algebraMap R F) (⅟((↑u⁻¹ : integralClosure R F) : F)) P.reverse = 0 :=
        (eval₂_reverse_eq_zero_iff (algebraMap R F) _ P).mpr hP
      rw [aeval_def]
      exact h
    · rw [coeff_zero_reverse, hPm.leadingCoeff]
      exact isUnit_one
  · rintro ⟨Q, hQ, hu⟩
    have hz : z * aeval z Q.divX + algebraMap R _ (Q.coeff 0) = 0 := by
      apply Subtype.val_injective
      have h := congrArg (aeval (z : F)) (X_mul_divX_add Q)
      rw [hQ, map_add, map_mul, aeval_X, aeval_C] at h
      rw [Subalgebra.coe_add, Subalgebra.coe_mul, aeval_subalgebra_coe, Subalgebra.coe_algebraMap,
        Subalgebra.coe_zero]
      exact h
    have hunit : IsUnit (z * aeval z Q.divX) := by
      rw [eq_neg_of_add_eq_zero_left hz]
      exact (hu.map (algebraMap R _)).neg
    exact isUnit_of_mul_isUnit_left hunit

/-- Locality of an integral closure, expressed through polynomial equations only. -/
theorem isLocalRing_integralClosure_iff {R F : Type*} [CommRing R] [CommRing F] [Algebra R F]
    [Nontrivial F] :
    IsLocalRing (integralClosure R F) ↔ ∀ z : F, IsIntegral R z →
      (∃ Q : R[X], aeval z Q = 0 ∧ IsUnit (Q.coeff 0)) ∨
        (∃ Q : R[X], aeval (1 - z) Q = 0 ∧ IsUnit (Q.coeff 0)) := by
  constructor
  · intro h z hz
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨z, hz⟩ : integralClosure R F) with h1 | h1
    · exact Or.inl ((isUnit_integralClosure_iff _).mp h1)
    · exact Or.inr ((isUnit_integralClosure_iff _).mp h1)
  · intro h
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
    rcases h z z.property with h1 | h1
    · exact Or.inl ((isUnit_integralClosure_iff _).mpr h1)
    · exact Or.inr ((isUnit_integralClosure_iff _).mpr (by simpa using h1))

/-! ### Flat descent -/

section FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-- Evaluation of a homogenised polynomial as an explicit finite sum. -/
private theorem eval_homogenize_eq_sum {R : Type*} [CommRing R] (P : R[X]) (D : ℕ)
    (v : Fin 2 → R) :
    MvPolynomial.eval v (P.homogenize D) =
      ∑ kl ∈ Finset.antidiagonal D, P.coeff kl.1 * v 0 ^ kl.1 * v 1 ^ kl.2 := by
  simp only [homogenize, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index]
  · ring
  all_goals simp [pow_add]

private theorem homogenize_pow {R : Type*} [CommRing R] (P : R[X]) (d N : ℕ)
    (hd : P.natDegree ≤ d) : (P ^ N).homogenize (d * N) = (P.homogenize d) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ, homogenize_mul _ _ ?_ hd, ih]
    exact natDegree_pow_le.trans (by rw [mul_comm]; exact Nat.mul_le_mul_right N hd)

/-- A flat local homomorphism into `B`, followed by the reduction of `B`, is injective on a
reduced local source. -/
theorem injective_algebraMap_quotient_nilradical [IsReduced A] :
    Function.Injective ((Ideal.Quotient.mk (nilradical B)).comp (algebraMap A B)) := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := FaithfulSMul.algebraMap_injective A B
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_nilradical] at ha
  obtain ⟨k, hk⟩ := ha
  rw [← map_pow] at hk
  exact IsNilpotent.eq_zero ⟨k, hinj (hk.trans (map_zero _).symm)⟩

/-- The key step of flat descent: if the image of `z` in the fraction field of `B_red` is a
root of a polynomial with unit constant term, then so is `z` itself over `A`. -/
theorem exists_unit_coeff_root_of_map [IsDomain A] [IsDomain (B ⧸ nilradical B)]
    (hinj : Function.Injective ((Ideal.Quotient.mk (nilradical B)).comp (algebraMap A B)))
    (z : FractionRing A) (Qbar : (B ⧸ nilradical B)[X])
    (hQ : aeval (IsFractionRing.map (K := FractionRing A)
      (L := FractionRing (B ⧸ nilradical B)) hinj z) Qbar = 0)
    (hu : IsUnit (Qbar.coeff 0)) :
    ∃ Q : A[X], aeval z Q = 0 ∧ IsUnit (Q.coeff 0) := by
  classical
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  obtain ⟨Q, rfl⟩ :=
    Polynomial.map_surjective (Ideal.Quotient.mk (nilradical B)) Ideal.Quotient.mk_surjective Qbar
  let K := FractionRing A
  let E := B ⧸ nilradical B
  let L := FractionRing E
  let π : B →+* E := Ideal.Quotient.mk (nilradical B)
  let ρ : B →+* L := (algebraMap E L).comp π
  have hQ0 : IsUnit (Q.coeff 0) := by
    have : IsLocalHom π := isLocalHom_of_le_jacobson_bot _ (Ideal.radical_le_jacobson (I := (⊥ : Ideal B)))
    rw [coeff_map] at hu
    exact isUnit_of_map_unit π _ hu
  let d := Q.natDegree
  let v : Fin 2 → B := ![algebraMap A B a, algebraMap A B s]
  let H := MvPolynomial.eval v (Q.homogenize d)
  -- the homogenised equation vanishes in the fraction field of `B_red`
  have hs : ρ (algebraMap A B s) ≠ 0 := by
    intro h0
    have h1 : ((Ideal.Quotient.mk (nilradical B)).comp (algebraMap A B)) (s : A) = 0 :=
      IsFractionRing.injective E L (h0.trans (map_zero _).symm)
    exact nonZeroDivisors.coe_ne_zero s (hinj (h1.trans (map_zero _).symm))
  have hρH : ρ H = 0 := by
    have h1 : ρ H = MvPolynomial.eval (ρ ∘ v) ((Q.map ρ).homogenize d) := by
      rw [homogenize_map, MvPolynomial.eval_map]
      simp only [H, MvPolynomial.eval]
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    rw [h1, eval_homogenize natDegree_map_le (ρ ∘ v) (by simpa [v] using hs)]
    have h2 : (ρ ∘ v) 0 / (ρ ∘ v) 1 = IsFractionRing.map (K := K) (L := L) hinj
        (IsLocalization.mk' K a s) := by
      rw [IsFractionRing.map, IsLocalization.map_mk', IsFractionRing.mk'_eq_div]
      rfl
    have h3 : (Q.map ρ).eval (IsFractionRing.map (K := K) (L := L) hinj
        (IsLocalization.mk' K a s)) = 0 := by
      rw [← hQ, aeval_def, eval_map, Polynomial.eval₂_map]
    rw [h2, h3, zero_mul]
  have hH : IsNilpotent H := by
    have h1 : π H = 0 := IsFractionRing.injective E L (hρH.trans (map_zero _).symm)
    exact mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)
  obtain ⟨N, hN⟩ := hH
  let P := Q ^ N
  let D := d * N
  have hP : MvPolynomial.eval v (P.homogenize D) = 0 := by
    rw [homogenize_pow Q d N le_rfl, map_pow, hN]
  rw [eval_homogenize_eq_sum] at hP
  -- the equational criterion of flatness
  have hrel : ∑ i : Finset.antidiagonal D,
      (a ^ (i : ℕ × ℕ).1 * (s : A) ^ (i : ℕ × ℕ).2) • P.coeff (i : ℕ × ℕ).1 = 0 := by
    rw [Finset.sum_coe_sort (Finset.antidiagonal D)
      (fun kl => (a ^ kl.1 * (s : A) ^ kl.2) • P.coeff kl.1), ← hP]
    refine Finset.sum_congr rfl fun kl _ => ?_
    simp only [v, Algebra.smul_def, map_mul, map_pow, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  obtain ⟨k, α, β, hx, hsum⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := B)
    (f := fun i : Finset.antidiagonal D => a ^ (i : ℕ × ℕ).1 * (s : A) ^ (i : ℕ × ℕ).2)
    (x := fun i : Finset.antidiagonal D => P.coeff (i : ℕ × ℕ).1) hrel
  let i₀ : Finset.antidiagonal D := ⟨(0, D), by simp⟩
  let R (j : Fin k) : A[X] := ∑ i : Finset.antidiagonal D, monomial (i : ℕ × ℕ).1 (α i j)
  have hzs : IsLocalization.mk' K a s * algebraMap A K s = algebraMap A K a :=
    IsLocalization.mk'_spec K a s
  have hRj (j : Fin k) : aeval (IsLocalization.mk' K a s) (R j) = 0 := by
    have hs0 : (algebraMap A K s) ^ D ≠ 0 :=
      pow_ne_zero _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2)
    apply mul_right_injective₀ hs0
    simp only [mul_zero]
    calc (algebraMap A K s) ^ D * aeval (IsLocalization.mk' K a s) (R j)
        = ∑ i : Finset.antidiagonal D,
            algebraMap A K (a ^ (i : ℕ × ℕ).1 * (s : A) ^ (i : ℕ × ℕ).2 * α i j) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [aeval_monomial]
          have hi : (i : ℕ × ℕ).1 + (i : ℕ × ℕ).2 = D := Finset.mem_antidiagonal.mp i.2
          have hpow : (algebraMap A K s) ^ D =
              (algebraMap A K s) ^ (i : ℕ × ℕ).1 * (algebraMap A K s) ^ (i : ℕ × ℕ).2 := by
            rw [← pow_add, hi]
          rw [hpow, map_mul, map_mul, map_pow, map_pow, ← hzs]
          ring
      _ = 0 := by rw [← map_sum, hsum j, map_zero]
  have hcoeff (j : Fin k) : (R j).coeff 0 = α i₀ j := by
    simp only [R, finsetSum_coeff, coeff_monomial]
    rw [Fintype.sum_eq_single i₀]
    · simp [i₀]
    · intro i hi
      rw [if_neg]
      intro h
      apply hi
      apply Subtype.ext
      have hmem : (i : ℕ × ℕ).1 + (i : ℕ × ℕ).2 = D := Finset.mem_antidiagonal.mp i.2
      ext
      · exact h
      · simp only [i₀]
        omega
  by_contra hcon
  push Not at hcon
  have hnon (j : Fin k) : α i₀ j ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← hcoeff]
    exact hcon _ (hRj j)
  have hmem : P.coeff 0 ∈ IsLocalRing.maximalIdeal B := by
    rw [show P.coeff 0 = ∑ j, α i₀ j • β j from hx i₀]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (map_nonunit (algebraMap A B) _ (hnon j))
  have hPunit : IsUnit (P.coeff 0) := by
    rw [show P.coeff 0 = (Q.coeff 0) ^ N by
      simp only [P, coeff_zero_eq_eval_zero, eval_pow]]
    exact hQ0.pow N
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hPunit

/-- **Flat descent of unibranchness.** If `A → B` is a flat local homomorphism of local
rings, `A` is reduced and `B` is unibranch (Stacks 0BPZ), then `A` is unibranch. -/
theorem sourceUnibranchReducedRing_of_flat [IsReduced A] (hB : SourceUnibranchLocalRing B) :
    SourceUnibranchReducedRing A := by
  obtain ⟨hdom, hloc⟩ := hB
  have hinj := injective_algebraMap_quotient_nilradical (A := A) (B := B)
  have hA : IsDomain A := hinj.isDomain _
  refine ⟨hA, ?_⟩
  rw [isLocalRing_integralClosure_iff] at hloc ⊢
  intro z hz
  set ψ := IsFractionRing.map (K := FractionRing A) (L := FractionRing (B ⧸ nilradical B)) hinj
  have hint : IsIntegral (B ⧸ nilradical B) (ψ z) := by
    refine hz.map_of_comp_eq ((Ideal.Quotient.mk (nilradical B)).comp (algebraMap A B)) ψ ?_
    ext a
    simp only [ψ, RingHom.comp_apply, IsFractionRing.map, IsLocalization.map_eq]
  rcases hloc (ψ z) hint with ⟨Q, hQ, hu⟩ | ⟨Q, hQ, hu⟩
  · exact Or.inl (exists_unit_coeff_root_of_map hinj z Q hQ hu)
  · exact Or.inr (exists_unit_coeff_root_of_map hinj (1 - z) Q (by rwa [map_sub, map_one]) hu)

/-- The Stacks form of flat descent. -/
theorem sourceUnibranchLocalRing_of_flat [IsReduced A] (hB : SourceUnibranchLocalRing B) :
    SourceUnibranchLocalRing A :=
  (sourceUnibranchLocalRing_iff_of_isReduced A).mpr (sourceUnibranchReducedRing_of_flat hB)

end FlatDescent

/-! ### From closed points to all points -/

section Jacobson

/-- Locality of an integral closure does not depend on the chosen fraction field. -/
theorem isLocalRing_integralClosure_of_algEquiv {R F₁ F₂ : Type*} [CommRing R] [CommRing F₁]
    [CommRing F₂] [Nontrivial F₁] [Nontrivial F₂] [Algebra R F₁] [Algebra R F₂]
    (e : F₁ ≃ₐ[R] F₂) (h : IsLocalRing (integralClosure R F₁)) :
    IsLocalRing (integralClosure R F₂) := by
  rw [isLocalRing_integralClosure_iff] at h ⊢
  intro z hz
  have hz' : IsIntegral R (e.symm z) := hz.map e.symm
  have he (Q : R[X]) (w : F₂) (hw : aeval (e.symm w) Q = 0) : aeval w Q = 0 := by
    have h1 : aeval ((e : F₁ →ₐ[R] F₂) (e.symm w)) Q = 0 := by
      rw [Polynomial.aeval_algHom_apply, hw, map_zero]
    simpa using h1
  rcases h (e.symm z) hz' with ⟨Q, hQ, hu⟩ | ⟨Q, hQ, hu⟩
  · exact Or.inl ⟨Q, he Q z hQ, hu⟩
  · refine Or.inr ⟨Q, he Q (1 - z) ?_, hu⟩
    rwa [map_sub, map_one]

/-- A localization of a domain which is nontrivial is a domain. -/
theorem isDomain_of_isLocalization_of_nontrivial {S T : Type*} [CommRing S] [CommRing T]
    [IsDomain S] [Algebra S T] (M : Submonoid S) [IsLocalization M T] [Nontrivial T] :
    IsDomain T := by
  refine IsLocalization.isDomain_of_le_nonZeroDivisors T (M := M) fun x hx => ?_
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  subst h0
  have h1 := IsLocalization.map_units T (⟨0, hx⟩ : M)
  rw [map_zero] at h1
  exact not_isUnit_zero h1

/-- The polynomial criterion of `isLocalRing_integralClosure_iff`, transported along `S → T`:
local normalization of a domain `S` controls every element of a common fraction field that
is integral over `S`. -/
theorem exists_unit_coeff_root_of_isLocalRing_integralClosure {S T F : Type*} [CommRing S]
    [IsDomain S] [CommRing T] [Field F] [Algebra S T] [Algebra T F] [Algebra S F]
    [IsScalarTower S T F] [IsFractionRing S F]
    (hS : IsLocalRing (integralClosure S (FractionRing S))) (z : F) (hz : IsIntegral S z) :
    (∃ Q : T[X], aeval z Q = 0 ∧ IsUnit (Q.coeff 0)) ∨
      (∃ Q : T[X], aeval (1 - z) Q = 0 ∧ IsUnit (Q.coeff 0)) := by
  have hF : IsLocalRing (integralClosure S F) :=
    isLocalRing_integralClosure_of_algEquiv
      (IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) F) hS
  rw [isLocalRing_integralClosure_iff] at hF
  rcases hF z hz with ⟨Q, hQ, hu⟩ | ⟨Q, hQ, hu⟩
  · refine Or.inl ⟨Q.map (algebraMap S T), ?_, ?_⟩
    · rw [aeval_map_algebraMap]
      exact hQ
    · rw [coeff_map]
      exact hu.map _
  · refine Or.inr ⟨Q.map (algebraMap S T), ?_, ?_⟩
    · rw [aeval_map_algebraMap]
      exact hQ
    · rw [coeff_map]
      exact hu.map _

variable {R : Type*} [CommRing R]

/-- For primes `p ≤ m`, the localization at `p` is a domain if the localization at `m` is. -/
private theorem isDomain_localization_of_le (p m : Ideal R) [p.IsPrime] [m.IsPrime] (hpm : p ≤ m)
    [IsDomain (Localization.AtPrime m)] : IsDomain (Localization.AtPrime p) := by
  have hle : m.primeCompl ≤ p.primeCompl := fun x hx hxp => hx (hpm hxp)
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl p.primeCompl hle
  have : IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsLocalization ((p.primeCompl).map (algebraMap R (Localization.AtPrime m)))
      (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  exact isDomain_of_isLocalization_of_nontrivial
    ((p.primeCompl).map (algebraMap R (Localization.AtPrime m)))

/-- For primes `p ≤ m` and `t ∉ m`, local normalization at `m` controls every `z` in the
fraction field at `p` with `t • z` integral over `R`. -/
private theorem exists_unit_coeff_root_of_le (p m : Ideal R) [p.IsPrime] [m.IsPrime]
    (hpm : p ≤ m) [IsDomain (Localization.AtPrime m)] [IsDomain (Localization.AtPrime p)]
    (hS : IsLocalRing (integralClosure (Localization.AtPrime m)
      (FractionRing (Localization.AtPrime m))))
    (z : FractionRing (Localization.AtPrime p)) (t : R) (ht : t ∉ m)
    (hz : IsIntegral R (t • z)) :
    (∃ Q : (Localization.AtPrime p)[X], aeval z Q = 0 ∧ IsUnit (Q.coeff 0)) ∨
      (∃ Q : (Localization.AtPrime p)[X], aeval (1 - z) Q = 0 ∧ IsUnit (Q.coeff 0)) := by
  let S := Localization.AtPrime m
  let T := Localization.AtPrime p
  let FT := FractionRing T
  let F := FractionRing S
  have hle : m.primeCompl ≤ p.primeCompl := fun x hx hxp => hx (hpm hxp)
  let : Algebra S T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ m.primeCompl p.primeCompl hle
  have : IsScalarTower R S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  let M' := (p.primeCompl).map (algebraMap R S)
  have : IsLocalization M' T := IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have hM' : M' ≤ nonZeroDivisors S := by
    intro x hx
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    subst h0
    have h1 := IsLocalization.map_units T (⟨0, hx⟩ : M')
    rw [map_zero] at h1
    exact not_isUnit_zero h1
  let : Algebra T F := IsLocalization.localizationAlgebraOfSubmonoidLe T F M' (nonZeroDivisors S) hM'
  have : IsScalarTower S T F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T F M' (nonZeroDivisors S) hM'
  have : IsFractionRing T F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M' T F
  let e : FT ≃ₐ[T] F := IsLocalization.algEquiv (nonZeroDivisors T) FT F
  have : IsScalarTower R S FT := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R T FT, IsScalarTower.algebraMap_apply R S T,
      ← IsScalarTower.algebraMap_apply S T FT]
  -- `z` is integral over the localization at `m`
  have hzS : IsIntegral S z := by
    have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S (⟨t, ht⟩ : m.primeCompl)
    have h1 : IsIntegral S (t • z) := hz.tower_top
    have h2 : IsIntegral S (algebraMap S FT ↑hu.unit⁻¹) := isIntegral_algebraMap
    have h3 : z = algebraMap S FT ↑hu.unit⁻¹ * (t • z) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S FT, ← mul_assoc, ← map_mul,
        IsUnit.val_inv_mul, map_one, one_mul]
    rw [h3]
    exact h2.mul h1
  have hzF : IsIntegral S (e z) := hzS.map (e.toAlgHom.restrictScalars S)
  have hback (w : FT) (Q : S[X]) (hQ : aeval (e w) Q = 0) :
      aeval w (Q.map (algebraMap S T)) = 0 := by
    apply e.injective
    have h1 : aeval (e w) (Q.map (algebraMap S T)) = 0 := by
      rw [aeval_map_algebraMap]
      exact hQ
    rw [map_zero, ← h1]
    exact (Polynomial.aeval_algHom_apply (e : FT →ₐ[T] F) w _).symm
  rw [isLocalRing_integralClosure_iff] at hS
  rcases hS (e z) hzF with ⟨Q, hQ, hu⟩ | ⟨Q, hQ, hu⟩
  · refine Or.inl ⟨Q.map (algebraMap S T), hback z Q hQ, ?_⟩
    rw [coeff_map]
    exact hu.map _
  · refine Or.inr ⟨Q.map (algebraMap S T), hback (1 - z) Q (by rwa [map_sub, map_one]), ?_⟩
    rw [coeff_map]
    exact hu.map _

/-- In a Jacobson ring, unibranchness of the localizations at all maximal ideals implies
unibranchness of the localizations at all prime ideals. -/
theorem sourceUnibranchReducedRing_localization_of_maximal [IsJacobsonRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], SourceUnibranchReducedRing (Localization.AtPrime m))
    (p : Ideal R) [hp : p.IsPrime] : SourceUnibranchReducedRing (Localization.AtPrime p) := by
  classical
  obtain ⟨m₀, hm₀, hpm₀⟩ := Ideal.exists_le_maximal p hp.ne_top
  have : m₀.IsMaximal := hm₀
  have : IsDomain (Localization.AtPrime m₀) := (h m₀).1
  have hT : IsDomain (Localization.AtPrime p) := isDomain_localization_of_le p m₀ hpm₀
  refine ⟨hT, ?_⟩
  rw [isLocalRing_integralClosure_iff]
  intro z hz
  obtain ⟨⟨t, htp⟩, htz⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl z hz
  -- the Jacobson property gives a maximal ideal above `p` avoiding `t`
  have hjac : p.jacobson = p := IsJacobsonRing.out ‹_› hp.isRadical
  obtain ⟨m, hm, hpm, htm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ p ≤ m ∧ t ∉ m := by
    by_contra hcon
    push Not at hcon
    apply htp
    rw [← hjac]
    change t ∈ sInf {J : Ideal R | p ≤ J ∧ J.IsMaximal}
    rw [Ideal.mem_sInf]
    rintro J ⟨hpJ, hJ⟩
    exact hcon J hJ hpJ
  have : m.IsMaximal := hm
  obtain ⟨hdom, hloc⟩ := h m
  exact exists_unit_coeff_root_of_le p m hpm hloc z t htm htz

/-- The Stacks form of `sourceUnibranchReducedRing_localization_of_maximal` for reduced rings. -/
theorem sourceUnibranchLocalRing_localization_of_maximal [IsJacobsonRing R] [IsReduced R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], SourceUnibranchLocalRing (Localization.AtPrime m))
    (p : Ideal R) [p.IsPrime] : SourceUnibranchLocalRing (Localization.AtPrime p) := by
  rw [sourceUnibranchLocalRing_iff_of_isReduced]
  exact sourceUnibranchReducedRing_localization_of_maximal
    (fun m _ => (sourceUnibranchLocalRing_iff_of_isReduced _).mp (h m)) p

end Jacobson

/-! ### Unibranch schemes -/

section Scheme

open AlgebraicGeometry CategoryTheory Topology

/-- Stacks Tag 0BQ2: a scheme is unibranch at `x` if its local ring at `x` is unibranch. -/
def SchemeIsUnibranchAt (X : Scheme) (x : X) : Prop :=
  SourceUnibranchLocalRing (X.presheaf.stalk x)

/-- Stacks Tag 0BQ2: a scheme is unibranch if it is unibranch at every point. This is the
algebraic notion of `prop:unibranch_gaga`. -/
def SchemeIsUnibranch (X : Scheme) : Prop :=
  ∀ x : X, SchemeIsUnibranchAt X x

/-- Open immersions preserve and reflect unibranchness at a point. -/
theorem schemeIsUnibranchAt_iff_of_isOpenImmersion {U X : Scheme} (φ : U ⟶ X)
    [IsOpenImmersion φ] (u : U) : SchemeIsUnibranchAt X (φ u) ↔ SchemeIsUnibranchAt U u :=
  sourceUnibranchLocalRing_iff_of_ringEquiv (asIso (φ.stalkMap u)).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- At a point of an affine scheme, unibranchness is that of the localization. -/
theorem schemeIsUnibranchAt_spec_iff (R : CommRingCat) (x : PrimeSpectrum R) :
    SchemeIsUnibranchAt (Spec R) x ↔ SourceUnibranchLocalRing (Localization.AtPrime x.asIdeal) :=
  (sourceUnibranchLocalRing_iff_of_ringEquiv (StructureSheaf.stalkIso R x).toRingEquiv).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- On a reduced Jacobson scheme (for instance a reduced scheme locally of finite type over
`ℂ`), unibranchness at all closed points implies unibranchness at every point. -/
theorem schemeIsUnibranch_of_closedPoints (X : Scheme) [JacobsonSpace X]
    [AlgebraicGeometry.IsReduced X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → SchemeIsUnibranchAt X x) : SchemeIsUnibranch X := by
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  let φ := hV'.fromSpec
  have hx : x ∈ Set.range φ := by rw [IsAffineOpen.range_fromSpec]; exact hxV
  obtain ⟨y, rfl⟩ := hx
  have : JacobsonSpace (Spec Γ(X, V)) := JacobsonSpace.of_isOpenEmbedding φ.isOpenEmbedding
  have : IsJacobsonRing Γ(X, V) := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr this
  have hred (q : PrimeSpectrum Γ(X, V)) : IsReduced (Localization.AtPrime q.asIdeal) := by
    let e := (StructureSheaf.stalkIso Γ(X, V) q).toRingEquiv.trans
      (asIso (φ.stalkMap q)).commRingCatIsoToRingEquiv.symm
    exact isReduced_of_injective e.toRingHom e.injective
  rw [schemeIsUnibranchAt_iff_of_isOpenImmersion, schemeIsUnibranchAt_spec_iff,
    sourceUnibranchLocalRing_iff_of_isReduced]
  refine sourceUnibranchReducedRing_localization_of_maximal (fun m _ => ?_) y.asIdeal
  let z : PrimeSpectrum Γ(X, V) := ⟨m, inferInstance⟩
  have hz : IsClosed ({z} : Set (PrimeSpectrum Γ(X, V))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mpr inferInstance
  have hφz : IsClosed ({φ z} : Set X) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    rw [← Set.image_singleton]
    exact hz.isLocallyClosed.image φ.isOpenEmbedding.isInducing
      φ.isOpenEmbedding.isOpen_range.isLocallyClosed
  have h1 := (schemeIsUnibranchAt_iff_of_isOpenImmersion φ z).mp (h _ hφz)
  rw [schemeIsUnibranchAt_spec_iff] at h1
  exact (sourceUnibranchLocalRing_iff_of_isReduced _).mp h1

end Scheme

end

end SGPT.Unibranch
