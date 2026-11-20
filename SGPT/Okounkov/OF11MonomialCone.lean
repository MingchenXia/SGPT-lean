import SGPT.Okounkov.ValCurrLexEquivalence
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Monomial valuations of maximal rank on a normal crossings chart

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.*

This file contains the combinatorial heart of the existence part of [CFKLRS17, Thm 2.9] in the
form used by lane OF11: **no toric (Perron) transformations are needed once `n` functions of values
`e₁, …, eₙ` are monomials in normal crossings coordinates at the centre.**

Let `ν` be a valuation with values in `ℤⁿ_lex` centred on a local ring `R` (`ν ≥ 0` on `R`,
`ν > 0` on the maximal ideal), let `z₁, …, zₙ ∈ 𝔪_R` with finite values `cⱼ = ν(zⱼ) > 0`, and let
`u₁, …, uₙ ∈ R` with `ν(u_k) = e_k` be monomials in the `zⱼ` up to units:
`u_k = ε_k ∏ⱼ zⱼ^{a_{kj}}` (`a_{kj} ∈ ℕ`). Then `e_k = ∑ⱼ a_{kj} cⱼ`, so every `e_k` lies in the
cone spanned by the lexicographically positive vectors `cⱼ`, and this forces:

* the leading indices of the `cⱼ` (position of the first nonzero coordinate) are pairwise
  distinct, i.e. form a permutation `σ`;
* the matrix with rows `c_{σ(1)}, …, c_{σ(n)}` is **unit upper triangular** (`G = I + N`).

Main results:

* `exists_perm_isUnitUpperTriangular_of_cone`: the combinatorial statement for integer vectors.
* `exists_perm_isUnitUpperTriangular_of_monomial`: the valuation-theoretic statement: there is a
  permutation `σ` with `(ν(z_{σ(i)}))ᵢ` unit upper triangular.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF11

open SGPT.Okounkov.ValCurr

/-! ### Lexicographically positive vectors and their leading index -/

section Lead

variable {n : ℕ}

/-- `0 < x` in `ℤⁿ_lex` iff some coordinate is positive and all earlier ones vanish. -/
theorem lex_pos_iff (x : Fin n → ℤ) :
    (0 : Lex (Fin n → ℤ)) < toLex x ↔ ∃ i, (∀ j < i, x j = 0) ∧ 0 < x i := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    exact ⟨i, fun j hj => (hi j hj).symm, hlt⟩
  · rintro ⟨i, hi, hlt⟩
    exact ⟨i, fun j hj => (hi j hj).symm, hlt⟩

/-- The leading index of a lexicographically positive vector is unique. -/
theorem lead_unique {x : Fin n → ℤ} {i i' : Fin n} (hi : ∀ j < i, x j = 0) (hpos : 0 < x i)
    (hi' : ∀ j < i', x j = 0) (hpos' : 0 < x i') : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd (hi' i h) hpos.ne'
  · exact h
  · exact absurd (hi i' h) hpos'.ne'

end Lead

/-! ### The cone lemma -/

section Cone

variable {n : ℕ}

/-- **The cone lemma.** Let `c₁, …, cₙ ∈ ℤⁿ` be lexicographically positive and suppose every
standard basis vector `e_i` is a combination `∑ⱼ a_{ij} cⱼ` with natural coefficients. Then some
reordering `(c_{σ(i)})ᵢ` of the `cⱼ` is a unit upper triangular matrix. -/
theorem exists_perm_isUnitUpperTriangular_of_cone (c : Fin n → Fin n → ℤ)
    (hpos : ∀ j, (0 : Lex (Fin n → ℤ)) < toLex (c j)) (a : Fin n → Fin n → ℕ)
    (hsum : ∀ i l, ∑ j, (a i j : ℤ) * c j l = if l = i then 1 else 0) :
    ∃ σ : Equiv.Perm (Fin n), IsUnitUpperTriangular (fun i => c (σ i)) := by
  classical
  have hlead : ∀ j, ∃ i, (∀ l < i, c j l = 0) ∧ 0 < c j i := fun j => (lex_pos_iff _).mp (hpos j)
  choose lead hlead0 hleadpos using hlead
  -- coordinates before the leading index vanish; at and after it they are determined by it
  have hnonneg : ∀ j l, lead j ≥ l → 0 ≤ c j l := by
    intro j l hl
    rcases eq_or_lt_of_le hl with h | h
    · rw [h]; exact (hleadpos j).le
    · exact (hlead0 j l h).ge
  have hzero : ∀ j l, l < lead j → c j l = 0 := fun j l h => hlead0 j l h
  -- (1) every `j` with `a i j ≠ 0` has leading index `≥ i`
  have hge : ∀ i j, a i j ≠ 0 → i ≤ lead j := by
    intro i j hj
    by_contra hlt
    push Not at hlt
    -- a counterexample with minimal leading index
    let S : Finset (Fin n) := Finset.univ.filter fun j' => a i j' ≠ 0 ∧ lead j' < i
    have hS : S.Nonempty := ⟨j, by simp [S, hj, hlt]⟩
    obtain ⟨j₀, hj₀S, hj₀min⟩ := Finset.mem_image.mp ((S.image lead).min'_mem (hS.image lead))
    have hlmin : ∀ j' ∈ S, lead j₀ ≤ lead j' := by
      intro j' hj'
      rw [hj₀min]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem lead hj')
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj₀S
    have hli : lead j₀ ≠ i := hj₀S.2.ne
    have hcoord := hsum i (lead j₀)
    rw [if_neg hli] at hcoord
    -- all terms are nonnegative
    have hterm : ∀ j' ∈ Finset.univ, 0 ≤ (a i j' : ℤ) * c j' (lead j₀) := by
      intro j' _
      by_cases ha : a i j' = 0
      · simp [ha]
      · refine mul_nonneg (Int.natCast_nonneg _) (hnonneg j' _ ?_)
        by_contra hlt'
        push Not at hlt'
        have hmem : j' ∈ S := by simp [S, ha, lt_trans hlt' hj₀S.2]
        exact absurd (hlmin j' hmem) (not_le.mpr hlt')
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hcoord j₀ (Finset.mem_univ _)
    have hpos' : 0 < (a i j₀ : ℤ) * c j₀ (lead j₀) :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hj₀S.1) (hleadpos j₀)
    exact hpos'.ne' hall
  -- (2) the `i`-th coordinate: `1 = ∑ⱼ a_{ij} c_{j,i}`, only leading index `i` contributes
  have hcoordi : ∀ i, ∑ j, (a i j : ℤ) * c j i = 1 := by
    intro i
    rw [hsum i i, if_pos rfl]
  have hterm0 : ∀ i j, lead j ≠ i → (a i j : ℤ) * c j i = 0 := by
    intro i j hj
    by_cases ha : a i j = 0
    · simp [ha]
    · have := hzero j i (lt_of_le_of_ne (hge i j ha) (Ne.symm hj))
      simp [this]
  -- (3) `lead` is surjective, hence bijective
  have hsurj : Function.Surjective lead := by
    intro i
    by_contra hno
    push Not at hno
    have h0 : ∑ j, (a i j : ℤ) * c j i = 0 :=
      Finset.sum_eq_zero fun j _ => hterm0 i j (hno j)
    rw [hcoordi i] at h0
    exact one_ne_zero h0
  have hbij : Function.Bijective lead := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  let e := Equiv.ofBijective lead hbij
  refine ⟨e.symm, ?_, ?_⟩
  · intro i
    have hl : lead (e.symm i) = i := e.apply_symm_apply i
    -- `1 = a_{i,σ i} c_{σ i, i}`
    have h1 : (a i (e.symm i) : ℤ) * c (e.symm i) i = 1 := by
      rw [← hcoordi i]
      refine (Finset.sum_eq_single (e.symm i) (fun j _ hj => hterm0 i j ?_) (by simp)).symm
      intro hji
      apply hj
      rw [← e.symm_apply_apply j]
      exact congrArg e.symm hji
    have hpos' : 0 < c (e.symm i) i := by
      have := hleadpos (e.symm i)
      rwa [hl] at this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · omega
  · intro i l hli
    have hl : lead (e.symm i) = i := e.apply_symm_apply i
    exact hzero (e.symm i) l (by rw [hl]; exact hli)

end Cone

/-! ### Values of normal crossings coordinates -/

section Valuation

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

/-- The value of a finite product is the sum of the values. -/
theorem addValuation_prod (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) {ι : Type*}
    (s : Finset ι) (g : ι → K) : v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

/-- **Monomial coordinates.** Let `v` be a valuation of `K = Frac R` with values in `ℤⁿ_lex`,
`z₁, …, zₙ ∈ R` with values `v(zⱼ) = cⱼ` finite and positive, and `u₁, …, uₙ ∈ R` with
`v(u_k) = e_k`, each a monomial `u_k = ε_k ∏ⱼ zⱼ^{a_{kj}}` in the `zⱼ` times an element `ε_k`
of value `0` (a unit of `R` when `v` is centred on `R`). Then some reordering of the value vectors
`(v(z_{σ(i)}))ᵢ` is a unit upper triangular matrix. -/
theorem exists_perm_isUnitUpperTriangular_of_monomial
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) (z u ε : Fin n → R)
    (c : Fin n → Fin n → ℤ)
    (hz : ∀ j, v (algebraMap R K (z j)) = ((toLex (c j) : Lex _) : WithTop _))
    (hzpos : ∀ j, (0 : Lex (Fin n → ℤ)) < toLex (c j))
    (hε : ∀ k, v (algebraMap R K (ε k)) = 0) (a : Fin n → Fin n → ℕ)
    (hu : ∀ k, u k = ε k * ∏ j, z j ^ a k j)
    (hvu : ∀ k, v (algebraMap R K (u k)) =
      ((toLex (Pi.single k (1 : ℤ)) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) :
    ∃ σ : Equiv.Perm (Fin n), IsUnitUpperTriangular (fun i => c (σ i)) := by
  classical
  refine exists_perm_isUnitUpperTriangular_of_cone c hzpos a ?_
  intro i l
  have h := hvu i
  rw [hu i, map_mul, AddValuation.map_mul, hε i, zero_add, map_prod, addValuation_prod] at h
  simp only [map_pow, AddValuation.map_pow, hz] at h
  -- the sum of coerced terms is the coercion of the sum
  have hcoe : (∑ j, (a i j) • ((toLex (c j) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) =
      ((∑ j, (a i j) • toLex (c j) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
    rw [WithTop.coe_sum]
    simp only [WithTop.coe_nsmul]
  rw [hcoe] at h
  have h' := congrArg (fun x : Lex (Fin n → ℤ) => ofLex x l) (WithTop.coe_injective h)
  have hsumapp : ofLex (∑ j, (a i j) • toLex (c j) : Lex (Fin n → ℤ)) l =
      ∑ j, (a i j : ℤ) * c j l := by
    change (∑ j, (a i j) • (c j) : Fin n → ℤ) l = _
    rw [Finset.sum_apply]
    simp
  rw [hsumapp] at h'
  rw [h']
  change (Pi.single i (1 : ℤ) : Fin n → ℤ) l = _
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]

end Valuation

end SGPT.Okounkov.OF11
