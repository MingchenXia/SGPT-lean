import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension
import SGPT.Okounkov.ValuationCoarseningCenters

/-!
# Abhyankar's inequality for valuations of `ℂ(X)` with values in `ℤᵐ_lex`

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`: *"maximal-rank valuations of
`ℂ(X)` are closely related to flag valuations. More precisely, if a valuation has value group
identified with `ℤⁿ_lex` and maximal rational rank `n`, then [CFKLRS17, Thm 2.9] shows that it is
equivalent to [...] a valuation induced by an admissible flag on a modification of `X`."*

This file proves the valuation-theoretic input of the remark and of the first step of the proof of
[CFKLRS17, Thm 2.9]: Abhyankar's inequality in the form needed here.

## Abstract part (a field `K` over a field `k`, a valuation `v` trivial on `k^×`)

* `val_aeval_eq_weight`, `algebraicIndependent_of_injective_weight` (**value-group half of
  Abhyankar's inequality**): elements `x_i` whose values `g_i` are `ℤ`-independent (more precisely:
  `d ↦ ∑ d_i g_i` is injective on `ℕ^{(ι)}`) are algebraically independent; in fact the value of a
  nonzero polynomial `P(x)` is the value `∑ d_i g_i` of one of the monomials of `P`.
* `algebraicIndependent_sumElim_of_residues` (**Abhyankar's inequality**): elements `y_j` whose
  residues are algebraically independent (`v(Q(y)) = 0` for every nonzero polynomial `Q`) together
  with the `x_i` are algebraically independent over `k`. Hence (rational rank of `v`) +
  (transcendence degree of the residue field) `≤ trdeg_k K`.

## Valuations of `ℂ(X)` with values in `ℤᵐ_lex`

`X` is an integral scheme smooth of relative dimension `n` over `ℂ` (so `trdeg_ℂ ℂ(X) = n`).

* every valuation with values in `ℤᵐ_lex` is trivial on `ℂ^×`
  (`SGPT.Okounkov.AlgebraicValuation.valuation_algebraMap_eq_zero`).
* `le_of_surjective` (**maximality of the rank `n`**): a surjective valuation
  `ℂ(X)^× → ℤᵐ_lex` has `m ≤ n`; `card_le_of_injective_weight`: more generally every family of
  values with `ℤ`-independent values has at most `n` members (rational rank `≤ n = dim X`).
* `exists_val_sub_const_pos` (**the residue field is `ℂ`**): for a surjective
  `ν : ℂ(X)^× → ℤⁿ_lex` (maximal rank) and `y` with `ν(y) ≥ 0` there is `c ∈ ℂ` with
  `ν(y - c) > 0`.
* `exists_residue_independent_prefixOne`, `not_residue_independent_prefixOne` (**the first
  coordinate is a divisorial valuation**): the coarsening `ν₁ = pr₁ ∘ ν` (value group `ℤ`) has a
  residue field of transcendence degree exactly `n - 1`: there are `n - 1` elements with
  `ν₁ = 0` whose residues are algebraically independent over `ℂ`, and no `n` such elements.
  (This is the first step of the proof of [CFKLRS17, Thm 2.9]; the next step, Zariski's
  realization of the divisorial valuation `ν₁` as `ord_E` of a prime divisor on a birational model,
  is not formalized.)
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF4

open MvPolynomial

/-! ### Abstract Abhyankar inequality -/

section Abstract

variable {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ]

/-- The value of a finite product is the sum of the values. -/
theorem addValuation_finset_prod (v : AddValuation K (WithTop Γ)) {ι : Type*} (s : Finset ι)
    (f : ι → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

/-- The value of a multiset product is the sum of the values. -/
theorem addValuation_multiset_prod (v : AddValuation K (WithTop Γ)) (s : Multiset K) :
    v s.prod = (s.map v).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      AddValuation.map_mul, ih]

/-- The weight `∑ d_i g_i` of an exponent vector `d`. -/
def weight {ι : Type*} (g : ι → Γ) (d : ι →₀ ℕ) : Γ :=
  d.sum fun i e => e • g i

/-- **The value of `P(x)`.** If the values `g_i = v(x_i)` have injective weights and `v` is
trivial on the nonzero scalars, then for every nonzero polynomial `P` the value `v(P(x))` is the
weight of one of the monomials of `P` (the one of least weight). -/
theorem val_aeval_eq_weight {R : Type*} [CommRing R] [Algebra R K]
    (v : AddValuation K (WithTop Γ)) (hR : ∀ r : R, r ≠ 0 → v (algebraMap R K r) = 0)
    {ι : Type*} (x : ι → K) (g : ι → Γ) (hx : ∀ i, v (x i) = g i)
    (hg : Function.Injective (weight g)) {p : MvPolynomial ι R} (hp : p ≠ 0) :
    ∃ d ∈ p.support, v (aeval x p) = ((weight g d : Γ) : WithTop Γ) ∧
      ∀ d' ∈ p.support, weight g d ≤ weight g d' := by
  classical
  have hterm : ∀ d ∈ p.support,
      v (algebraMap R K (p.coeff d) * ∏ i ∈ d.support, x i ^ d i) =
        ((weight g d : Γ) : WithTop Γ) := by
    intro d hd
    rw [AddValuation.map_mul, hR _ (mem_support_iff.mp hd), zero_add, addValuation_finset_prod]
    simp only [AddValuation.map_pow, hx]
    simp only [weight, Finsupp.sum, WithTop.coe_sum, WithTop.coe_nsmul]
  have hsupp : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hp
  obtain ⟨j, hj, hjmin⟩ := p.support.exists_min_image (weight g) hsupp
  refine ⟨j, hj, ?_, hjmin⟩
  have hsum : aeval x p =
      ∑ d ∈ p.support, algebraMap R K (p.coeff d) * ∏ i ∈ d.support, x i ^ d i := by
    rw [aeval_def, eval₂_eq]
  rw [hsum, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  have hlt : ((weight g j : Γ) : WithTop Γ) <
      v (∑ d ∈ p.support \ {j}, algebraMap R K (p.coeff d) * ∏ i ∈ d.support, x i ^ d i) := by
    apply AddValuation.map_lt_sum v WithTop.coe_ne_top
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
    rw [hterm d hd.1, WithTop.coe_lt_coe]
    exact lt_of_le_of_ne (hjmin d hd.1) (fun h => hd.2 (hg h).symm)
  rw [AddValuation.map_add_eq_of_lt_left v (by rw [hterm j hj]; exact hlt), hterm j hj]

/-- **Value-group half of Abhyankar's inequality.** Elements whose values have injective
weights (e.g. `ℤ`-linearly independent values) are algebraically independent over any ring on
whose nonzero elements `v` vanishes. -/
theorem algebraicIndependent_of_injective_weight {R : Type*} [CommRing R] [Algebra R K]
    (v : AddValuation K (WithTop Γ)) (hR : ∀ r : R, r ≠ 0 → v (algebraMap R K r) = 0)
    {ι : Type*} (x : ι → K) (g : ι → Γ) (hx : ∀ i, v (x i) = g i)
    (hg : Function.Injective (weight g)) : AlgebraicIndependent R x := by
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hne
  obtain ⟨d, -, hd, -⟩ := val_aeval_eq_weight v hR x g hx hg hne
  rw [hp, AddValuation.map_zero] at hd
  exact WithTop.coe_ne_top hd.symm

/-- **Abhyankar's inequality.** If the values of the `x_i` have injective weights and the
residues of the `y_j` are algebraically independent over `k` (`v(Q(y)) = 0` for every nonzero
polynomial `Q`), then the `x_i` and the `y_j` together are algebraically independent over `k`. -/
theorem algebraicIndependent_sumElim_of_residues {k : Type*} [Field k] [Algebra k K]
    (v : AddValuation K (WithTop Γ)) {ι κ : Type*} (x : ι → K) (g : ι → Γ)
    (hx : ∀ i, v (x i) = g i) (hg : Function.Injective (weight g)) (y : κ → K)
    (hy : ∀ Q : MvPolynomial κ k, Q ≠ 0 → v (aeval y Q) = 0) :
    AlgebraicIndependent k (Sum.elim x y) := by
  rw [AlgebraicIndependent.sumElim_iff]
  have hyind : AlgebraicIndependent k y := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    by_contra hne
    have h := hy Q hne
    rw [hQ, AddValuation.map_zero] at h
    exact WithTop.top_ne_zero h
  refine ⟨hyind, ?_⟩
  apply algebraicIndependent_of_injective_weight v _ x g hx hg
  intro r hr
  have hmem : (r : K) ∈ (aeval y : MvPolynomial κ k →ₐ[k] K).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨Q, hQ⟩ := hmem
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    apply hr
    apply Subtype.ext
    simpa using hQ.symm
  change v (r : K) = 0
  rw [← hQ]
  exact hy Q hQ0

end Abstract

/-! ### Valuations with values in `ℤᵐ_lex` -/

section Lex

variable {K : Type*} [Field K] {m : ℕ}

/-- The weights of the standard basis vectors `e_i` of `ℤᵐ_lex` are the exponent vectors. -/
theorem ofLex_weight_single (d : Fin m →₀ ℕ) (j : Fin m) :
    ofLex (weight (fun i : Fin m => toLex (Pi.single i (1 : ℤ))) d) j = (d j : ℤ) := by
  classical
  change (∑ i ∈ d.support, d i • (Pi.single i (1 : ℤ) : Fin m → ℤ)) j = (d j : ℤ)
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h]
    rfl

/-- The standard basis of `ℤᵐ_lex` has injective weights. -/
theorem weight_single_injective :
    Function.Injective (weight (fun i : Fin m => toLex (Pi.single i (1 : ℤ)))) := by
  intro d d' h
  ext j
  have := congrArg (fun z : Lex (Fin m → ℤ) => ofLex z j) h
  simp only [ofLex_weight_single] at this
  exact_mod_cast this

end Lex

/-! ### Valuations of `ℂ(X)` -/

section FunctionField

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- **Rational rank `≤ dim X`.** For every valuation of `ℂ(X)` (trivial on `ℂ^×`) with values in a
linearly ordered group, a family of elements whose values have injective weights (e.g. are
`ℤ`-linearly independent) has at most `n = dim X` members. -/
theorem card_le_of_injective_weight {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : AddValuation X.functionField (WithTop Γ))
    (hC : ∀ c : ℂ, c ≠ 0 →
      v (@algebraMap ℂ X.functionField _ _ (schemeFunctionFieldAlgebra f) c) = 0)
    {r : ℕ} (x : Fin r → X.functionField) (g : Fin r → Γ) (hx : ∀ i, v (x i) = g i)
    (hg : Function.Injective (weight g)) : r ≤ n := by
  let := schemeFunctionFieldAlgebra f
  have hind : AlgebraicIndependent ℂ x := algebraicIndependent_of_injective_weight v hC x g hx hg
  have h := hind.cardinalMk_le_trdeg
  rw [nativeSmoothFunctionField_trdeg f n, Cardinal.mk_fintype, Fintype.card_fin] at h
  exact_mod_cast h

/-- A surjective valuation `ℂ(X)^× → ℤᵐ_lex` has elements of value `e_i`. -/
theorem exists_val_eq_single {m : ℕ} (ν : AddValuation X.functionField (WithTop (Lex (Fin m → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ x : Fin m → X.functionField, ∀ i, ν (x i) = ((toLex (Pi.single i (1 : ℤ)) :
      Lex (Fin m → ℤ)) : WithTop (Lex (Fin m → ℤ))) :=
  ⟨fun i => (hν ((toLex (Pi.single i (1 : ℤ)) : Lex (Fin m → ℤ)) :
      WithTop (Lex (Fin m → ℤ)))).choose, fun _ => (hν _).choose_spec⟩

include f in
/-- **Maximality of the rank.** A surjective valuation `ν : ℂ(X)^× → ℤᵐ_lex` (rank and rational
rank `m`) has `m ≤ n = dim X`. -/
theorem le_of_surjective {m : ℕ} (ν : AddValuation X.functionField (WithTop (Lex (Fin m → ℤ))))
    (hν : Function.Surjective ν) : m ≤ n := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨x, hx⟩ := exists_val_eq_single ν hν
  exact card_le_of_injective_weight f n ν
    (fun c hc => AlgebraicValuation.valuation_algebraMap_eq_zero ν (algebraMap ℂ _) hc) x _ hx
    weight_single_injective

/-- **The residue field of a maximal-rank valuation is `ℂ`.** For a surjective
`ν : ℂ(X)^× → ℤⁿ_lex` (`n = dim X`) and every `y` with `ν(y) ≥ 0`, there is `c ∈ ℂ` with
`ν(y - c) > 0`. -/
theorem exists_val_sub_const_pos (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hν : Function.Surjective ν) (y : X.functionField) (hy : 0 ≤ ν y) :
    ∃ c : ℂ, 0 < ν (y - @algebraMap ℂ X.functionField _ _ (schemeFunctionFieldAlgebra f) c) := by
  let := schemeFunctionFieldAlgebra f
  by_contra hcon
  push Not at hcon
  have hzero : ∀ c : ℂ, ν (y - algebraMap ℂ X.functionField c) = 0 := by
    intro c
    refine le_antisymm (hcon c) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hy
    · have h1 := AddValuation.map_add ν y (-(algebraMap ℂ X.functionField c))
      rw [AddValuation.map_neg,
        AlgebraicValuation.valuation_algebraMap_eq_zero ν (algebraMap ℂ _) hc,
        ← sub_eq_add_neg] at h1
      exact le_trans (le_min hy le_rfl) h1
  -- every nonzero univariate polynomial has value `0` at `y`
  have hpoly : ∀ Q : Polynomial ℂ, Q ≠ 0 → ν (Polynomial.aeval y Q) = 0 := by
    intro Q hQ
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := Q))
    rw [← hfac, map_mul, Polynomial.aeval_C, AddValuation.map_mul,
      AlgebraicValuation.valuation_algebraMap_eq_zero ν (algebraMap ℂ _)
        (Polynomial.leadingCoeff_ne_zero.mpr hQ), zero_add,
      map_multiset_prod, addValuation_multiset_prod, Multiset.map_map, Multiset.map_map]
    refine Multiset.sum_eq_zero fun a ha => ?_
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp ha
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hzero c
  have hmv : ∀ Q : MvPolynomial Unit ℂ, Q ≠ 0 → ν (aeval (fun _ : Unit => y) Q) = 0 := by
    intro Q hQ
    have hQ' : MvPolynomial.uniqueAlgEquiv ℂ Unit Q ≠ 0 :=
      (map_ne_zero_iff _ (MvPolynomial.uniqueAlgEquiv ℂ Unit).injective).mpr hQ
    have heval : aeval (fun _ : Unit => y) Q =
        Polynomial.aeval y (MvPolynomial.uniqueAlgEquiv ℂ Unit Q) := by
      rw [aeval_def, Polynomial.aeval_def]
      exact (MvPolynomial.eval₂_uniqueAlgEquiv (a := fun _ : Unit => y)).symm
    rw [heval]
    exact hpoly _ hQ'
  obtain ⟨x, hx⟩ := exists_val_eq_single ν hν
  have hind := algebraicIndependent_sumElim_of_residues ν x _ hx weight_single_injective
    (fun _ : Unit => y) hmv
  have h := hind.cardinalMk_le_trdeg
  rw [nativeSmoothFunctionField_trdeg f n, Cardinal.mk_sum, Cardinal.mk_fintype,
    Cardinal.mk_fintype, Fintype.card_fin, Fintype.card_unit, Cardinal.lift_natCast,
    Cardinal.lift_natCast] at h
  norm_cast at h
  omega

/-! ### The first coordinate is a divisorial valuation -/

/-- The first coordinate `ν₁ = pr₁ ∘ ν` of a valuation with values in `ℤ^{m+1}_lex`. -/
abbrev prefixOne {m : ℕ} (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) :
    AddValuation X.functionField (WithTop (Lex (Fin 1 → ℤ))) :=
  ValCurr.prefixValuation (Nat.succ_le_succ (Nat.zero_le m)) ν

theorem prefixOne_coe {m : ℕ} (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (z : X.functionField) (a : Lex (Fin (m + 1) → ℤ)) (h : ν z = a) :
    prefixOne ν z = ((toLex fun _ : Fin 1 => ofLex a 0 : Lex (Fin 1 → ℤ)) :
      WithTop (Lex (Fin 1 → ℤ))) := by
  change ValCurr.prefixWithTopHom _ (ν z) = _
  rw [h]
  change ((ValCurr.prefixHom _ a : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) = _
  congr 1
  apply ofLex.injective
  funext i
  fin_cases i
  rfl

/-- **The residue field of `ν₁` has transcendence degree `≥ n - 1`.** For a surjective
`ν : ℂ(X)^× → ℤ^{m+1}_lex` there are `m` elements `y_j` (with `ν(y_j) = e_{j+1}`) of `ν₁`-value
`0` whose `ν₁`-residues are algebraically independent over `ℂ`: `ν₁(Q(y)) = 0` for every nonzero
polynomial `Q`. -/
theorem exists_residue_independent_prefixOne {m : ℕ}
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ y : Fin m → X.functionField, ∀ Q : MvPolynomial (Fin m) ℂ, Q ≠ 0 →
      prefixOne ν (@aeval ℂ X.functionField (Fin m) _ _ (schemeFunctionFieldAlgebra f) y Q) =
        0 := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨x, hx⟩ := exists_val_eq_single ν hν
  refine ⟨fun j => x j.succ, fun Q hQ => ?_⟩
  set g : Fin m → Lex (Fin (m + 1) → ℤ) := fun j => toLex (Pi.single j.succ (1 : ℤ)) with hgdef
  have hg : Function.Injective (weight g) := by
    intro d d' h
    ext j
    have hj : ∀ e : Fin m →₀ ℕ, ofLex (weight g e) j.succ = (e j : ℤ) := by
      intro e
      classical
      change (∑ i ∈ e.support, e i • (Pi.single i.succ (1 : ℤ) : Fin (m + 1) → ℤ)) j.succ = _
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, Fin.succ_inj, smul_ite, smul_zero, nsmul_eq_mul,
        mul_one]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Finsupp.notMem_support_iff.mp h]
        rfl
    have := congrArg (fun z : Lex (Fin (m + 1) → ℤ) => ofLex z j.succ) h
    simp only [hj] at this
    exact_mod_cast this
  obtain ⟨d, -, hd, -⟩ := val_aeval_eq_weight ν
    (fun c hc => AlgebraicValuation.valuation_algebraMap_eq_zero ν (algebraMap ℂ _) hc)
    (fun j => x j.succ) g (fun j => hx j.succ) hg hQ
  rw [prefixOne_coe ν _ _ hd]
  have h0 : ofLex (weight g d) 0 = 0 := by
    classical
    change (∑ i ∈ d.support, d i • (Pi.single i.succ (1 : ℤ) : Fin (m + 1) → ℤ)) 0 = 0
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [(Fin.succ_ne_zero i).symm]
  rw [h0]
  rfl

/-- **The residue field of `ν₁` has transcendence degree `≤ n - 1`.** For a surjective
`ν : ℂ(X)^× → ℤ^{m+1}_lex` with `m + 1 = n = dim X`, there are no `m + 1` elements whose
`ν₁`-residues are algebraically independent over `ℂ`. Together with
`exists_residue_independent_prefixOne`: `ν₁` is a discrete valuation of rank one (value group `ℤ`)
whose residue field has transcendence degree exactly `n - 1`, i.e. a divisorial valuation. -/
theorem not_residue_independent_prefixOne {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) (y : Fin (m + 1) → X.functionField) :
    ¬ ∀ Q : MvPolynomial (Fin (m + 1)) ℂ, Q ≠ 0 →
      prefixOne ν (@aeval ℂ X.functionField (Fin (m + 1)) _ _ (schemeFunctionFieldAlgebra f) y Q)
        = 0 := by
  let := schemeFunctionFieldAlgebra f
  intro hy
  obtain ⟨x, hx⟩ := exists_val_eq_single ν hν
  -- `x 0` has `ν₁`-value `1`
  have hx0 : prefixOne ν (x 0) =
      ((toLex (Pi.single (0 : Fin 1) (1 : ℤ)) : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
    rw [prefixOne_coe ν _ _ (hx 0)]
    congr 2
    funext i
    fin_cases i
    simp
  have hind := algebraicIndependent_sumElim_of_residues (prefixOne ν) (fun _ : Fin 1 => x 0)
    (fun i : Fin 1 => toLex (Pi.single i (1 : ℤ)))
    (fun i => by fin_cases i; exact hx0) weight_single_injective y hy
  have h := hind.cardinalMk_le_trdeg
  rw [nativeSmoothFunctionField_trdeg f (m + 1), Cardinal.mk_sum, Cardinal.mk_fintype,
    Cardinal.mk_fintype, Fintype.card_fin, Fintype.card_fin, Cardinal.lift_natCast,
    Cardinal.lift_natCast] at h
  norm_cast at h
  omega

end FunctionField

end SGPT.Okounkov.OF4
