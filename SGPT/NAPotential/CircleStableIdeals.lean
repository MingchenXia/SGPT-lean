import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-! # Circle-stable ideals of `R[t]`

Source `lma:istab` of `chapter_NApotential.tex`.  Let `R` be a commutative `ℂ`-algebra of finite
type and `I` an ideal of `R[t]`.  If `a^* I ⊆ I` for every `a ∈ S^1`, where
`a^* f(t) = f(a t)`, then `I` is stable under the whole `ℂ^*`-action, and there are ideals
`I_0 ⊆ I_1 ⊆ ⋯ ⊆ I_m` of `R` with `I = I_0 + I_1 t + ⋯ + I_m (t^m)`, i.e. a polynomial
`∑ a_k t^k` lies in `I` if and only if `a_k ∈ I_{min(k,m)}` for all `k`.

The proof is the book's: by discrete Fourier inversion over the `N`-th roots of unity (the
Lagrange interpolation of the book), every homogeneous component of an element of `I` lies in
`I`; the ideals `I_k = {a : a t^k ∈ I}` increase and stabilise because `R` is noetherian.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The action `a^* : f(t) ↦ f(a t)` of `a ∈ ℂ` on `R[t]`. -/
def polyScale (a : ℂ) : R[X] →ₐ[R] R[X] := aeval (C (algebraMap ℂ R a) * X)

theorem polyScale_coeff (a : ℂ) (f : R[X]) (k : ℕ) :
    (polyScale a f).coeff k = algebraMap ℂ R a ^ k * f.coeff k := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial j b =>
    rw [polyScale, aeval_monomial, coeff_monomial, mul_pow, ← C_pow, ← mul_assoc,
      ← C_eq_algebraMap, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h1 h2 h2
    · subst h1; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp

/-- The ideal `I_k = {a ∈ R : a t^k ∈ I}`. -/
def coeffIdeal (I : Ideal R[X]) (k : ℕ) : Ideal R where
  carrier := {a | monomial k a ∈ I}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact I.add_mem ha hb
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at ha ⊢
    rw [← C_mul_monomial]
    exact I.mul_mem_left _ ha

omit [Algebra ℂ R] in
theorem mem_coeffIdeal (I : Ideal R[X]) (k : ℕ) (a : R) :
    a ∈ coeffIdeal I k ↔ monomial k a ∈ I := Iff.rfl

omit [Algebra ℂ R] in
theorem coeffIdeal_monotone (I : Ideal R[X]) : Monotone (coeffIdeal I) := by
  apply monotone_nat_of_le_succ
  intro k a ha
  rw [mem_coeffIdeal] at ha ⊢
  have h : monomial (k + 1) a = X * monomial k a := by
    rw [X_mul_monomial]
  rw [h]
  exact I.mul_mem_left _ ha

/-- The discrete Fourier inversion over the `N`-th roots of unity. -/
theorem sum_rootsOfUnity_pow_eq {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i k : ℕ} (hi : i < N) (hk : k < N) :
    ∑ j ∈ Finset.range N, ((ζ ^ j)⁻¹) ^ i * (ζ ^ j) ^ k = if k = i then (N : ℂ) else 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  let w := ζ ^ k * (ζ ^ i)⁻¹
  have hterm : ∀ j, ((ζ ^ j)⁻¹) ^ i * (ζ ^ j) ^ k = w ^ j := by
    intro j
    simp only [w, mul_pow, inv_pow, ← pow_mul]
    ring
  simp only [hterm]
  split_ifs with hki
  · subst hki
    have : w = 1 := by simp [w, hζ0]
    simp [this]
  · have hw1 : w ≠ 1 := by
      intro hw
      have hpow : ζ ^ k = ζ ^ i := by
        have := congrArg (· * ζ ^ i) hw
        simpa [w, mul_assoc, inv_mul_cancel₀ (pow_ne_zero i hζ0)] using this
      exact hki (hζ.pow_inj hk hi hpow)
    have hwN : w ^ N = 1 := by
      simp only [w, mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm k N, mul_comm i N, pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, inv_one,
        mul_one]
    rw [geom_sum_eq hw1, hwN, sub_self, zero_div]

/-- Every homogeneous component of an element of a circle-stable ideal lies in the ideal. -/
theorem monomial_coeff_mem (I : Ideal R[X])
    (hI : ∀ a : ℂ, ‖a‖ = 1 → ∀ f ∈ I, polyScale a f ∈ I) {f : R[X]} (hf : f ∈ I) (i : ℕ) :
    monomial i (f.coeff i) ∈ I := by
  classical
  let N := f.natDegree + i + 1
  have hN : 0 < N := Nat.succ_pos _
  have hiN : i < N := by omega
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hnorm : ∀ j : ℕ, ‖ζ ^ j‖ = 1 := fun j => by
    rw [norm_pow, hζ.norm'_eq_one hN.ne', one_pow]
  let g : R[X] := ∑ j ∈ Finset.range N,
    C (algebraMap ℂ R (((ζ ^ j)⁻¹) ^ i)) * polyScale (ζ ^ j) f
  have hg : g ∈ I := I.sum_mem fun j _ => I.mul_mem_left _ (hI _ (hnorm j) f hf)
  have hcoeff : g = C (algebraMap ℂ R (N : ℂ)) * monomial i (f.coeff i) := by
    ext k
    simp only [g, finsetSum_coeff, coeff_C_mul, polyScale_coeff, coeff_monomial]
    by_cases hk : k < N
    · have hsum : ∑ j ∈ Finset.range N,
          algebraMap ℂ R (((ζ ^ j)⁻¹) ^ i) * (algebraMap ℂ R (ζ ^ j) ^ k * f.coeff k) =
          algebraMap ℂ R (∑ j ∈ Finset.range N, ((ζ ^ j)⁻¹) ^ i * (ζ ^ j) ^ k) * f.coeff k := by
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul, map_pow]
        ring
      rw [hsum, sum_rootsOfUnity_pow_eq hN hζ hiN hk]
      split_ifs with h1 h2 h2
      · subst h1; rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    · have hf0 : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hne : i ≠ k := by omega
      simp [hf0, hne]
  have hNunit : IsUnit (algebraMap ℂ R (N : ℂ)) :=
    (IsUnit.mk0 (N : ℂ) (by exact_mod_cast hN.ne')).map (algebraMap ℂ R)
  obtain ⟨u, hu⟩ := hNunit
  have hmem : C (↑u⁻¹ : R) * g ∈ I := I.mul_mem_left _ hg
  rw [hcoeff, ← mul_assoc, ← C_mul, ← hu, Units.inv_mul, C_1, one_mul] at hmem
  exact hmem

/-- Source `lma:istab`.  For a commutative `ℂ`-algebra `R` of finite type and an ideal `I` of
`R[t]` stable under `a^*` for all `a ∈ S^1`: `I` is stable under `a^*` for all `a ∈ ℂ^*`, and
there are `m` and ideals `I_0 ⊆ I_1 ⊆ ⋯` of `R`, constant from `m` on, with
`I = I_0 + I_1 t + ⋯ + I_m (t^m)`. -/
theorem ideal_circleStable [Algebra.FiniteType ℂ R] (I : Ideal R[X])
    (hI : ∀ a : ℂ, ‖a‖ = 1 → ∀ f ∈ I, polyScale a f ∈ I) :
    (∀ a : ℂ, a ≠ 0 → ∀ f ∈ I, polyScale a f ∈ I) ∧
      ∃ (m : ℕ) (J : ℕ → Ideal R), Monotone J ∧ (∀ k, m ≤ k → J k = J m) ∧
        ∀ f : R[X], f ∈ I ↔ ∀ k, f.coeff k ∈ J (min k m) := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  have hstab := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr inferInstance
    ⟨coeffIdeal I, coeffIdeal_monotone I⟩
  obtain ⟨m, hm⟩ := hstab
  have hJ : ∀ k, m ≤ k → coeffIdeal I k = coeffIdeal I m := fun k hk => (hm k hk).symm
  have hchar : ∀ f : R[X], f ∈ I ↔ ∀ k, f.coeff k ∈ coeffIdeal I (min k m) := by
    intro f
    constructor
    · intro hf k
      have h := monomial_coeff_mem I hI hf k
      rcases le_total k m with hkm | hkm
      · rw [min_eq_left hkm]
        exact h
      · rw [min_eq_right hkm, ← hJ k hkm]
        exact h
    · intro h
      rw [f.as_sum_support]
      exact I.sum_mem fun k _ => coeffIdeal_monotone I (min_le_left k m) (h k)
  refine ⟨?_, m, coeffIdeal I, coeffIdeal_monotone I, hJ, hchar⟩
  intro a _ f hf
  rw [hchar] at hf ⊢
  intro k
  rw [polyScale_coeff]
  exact (coeffIdeal I (min k m)).mul_mem_left _ (hf k)

end SGPT.NAPotential

end
