import SGPT.Okounkov.AlgebraicValuationCenter
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# One-dimensional leaves of a valuation on a graded family of subspaces

Lane VAL-GEN, blueprint `claude-val-gen.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies* (`sec:PoB`): "Fix a rank `n` valuation
`ν : ℂ(X)^× → ℤⁿ` ... We shall frequently use the standard fact that such a full-rank valuation
has one-dimensional leaves: for every finite-dimensional subspace `V ⊂ ℂ(X)`,
`#ν(V^×) = dim V` [LM09, Lemma 1.3]."

This file contains the purely algebraic part, for an arbitrary field `K ⊇ ℂ` and an arbitrary
additive valuation `v : K → ℤⁿ_lex ∪ {∞}` (automatically trivial on `ℂ^×`).

* `card_valueSet_eq_finrank`: if every two nonzero vectors of a finite-dimensional subspace with
  the same value can be cancelled (`v(x + c y) > v(x)` for some `c ∈ ℂ^×`), then the number of
  values `#v(V^×)` is `dim V` (the argument of `[LM09, Lemma 1.3]`; it is the same as the private
  lemma of `SGPT.Okounkov.NativeFlagGermFiniteLeaves`, restated here for arbitrary valuations).
* `valuation_aeval_eq_zero`: if `v(g - c) = 0` for every `c ∈ ℂ` (the residue of `g` is not a
  constant), then `v(p(g)) = 0` for every nonzero polynomial `p ∈ ℂ[T]` (`ℂ` is algebraically
  closed, so `p(g) = a ∏ (g - rᵢ)`).
* **`exists_leaf_cancel`** (the Abhyankar-type inequality behind one-dimensional leaves): let
  `(R_m)_m` be a graded family of finite-dimensional subspaces of `K` (`1 ∈ R_0`,
  `R_m R_k ⊆ R_{m+k}`) whose value sets grow like `mⁿ` (`#v(R_M^×) ≥ c₀ Mⁿ`, `c₀ > 0`) while
  `dim R_m = O(mⁿ)`. Then the leaves of `v` on every `R_k` are one-dimensional. Proof: if
  `x, y ∈ R_k` have the same value and no cancellation, `g = x/y` has a nonconstant residue; for
  representatives `u_w` of the values `w` of `R_M`, the `(d+1)·#v(R_M^×)` products
  `u_w x^b y^{d-b}` (`0 ≤ b ≤ d`) are linearly independent in `R_{M+dk}` (group them by `w`:
  each group is `u_w y^d p_w(g)` of value `w + d v(y)`), against `dim R_{M+dk} = O(Mⁿ)`.
* `card_valueSet_eq_finrank_of_growth`: consequently `#v(V^×) = dim V` for every subspace
  `V ⊆ R_k`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.ValGen

open Set Filter Polynomial
open scoped BigOperators

/-! ### Values of a subspace -/

section LinearAlgebra

variable {C E W D : Type*} [Field C] [Field E] [Algebra C E]
  [AddCommGroup W] [Module C W]
  [LinearOrderedAddCommMonoidWithTop D]

omit [AddCommGroup W] [Module C W] in
theorem valuation_algebraMap_mul (v : AddValuation E D)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) (c : C) (hc : c ≠ 0) (s : E) :
    v (algebraMap C E c * s) = v s := by
  rw [v.map_mul, htrivial c hc, zero_add]

theorem valuation_smul_eq (v : AddValuation E D) (ι : W →ₗ[C] E)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (c : C) (hc : c ≠ 0) (s : W) : v (ι (c • s)) = v (ι s) := by
  rw [map_smul, Algebra.smul_def, valuation_algebraMap_mul v htrivial c hc]

omit [Algebra C E] [AddCommGroup W] [Module C W] in
/-- If one term has a value strictly smaller than all the others, the sum has that value. -/
theorem valuation_sum_eq_of_unique_min {I : Type*} [DecidableEq I]
    (v : AddValuation E D) (s : Finset I) (f : I → E) {i : I}
    (hi : i ∈ s) (hfinite : v (f i) ≠ ⊤)
    (hmin : ∀ j ∈ s, j ≠ i → v (f i) < v (f j)) :
    v (∑ j ∈ s, f j) = v (f i) := by
  have hrest : v (f i) < v (∑ j ∈ s.erase i, f j) := by
    apply v.map_lt_sum' (lt_top_iff_ne_top.mpr hfinite)
    intro j hj
    exact hmin j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1
  rw [← Finset.sum_erase_add s f hi, add_comm]
  exact v.map_add_eq_of_lt_left hrest

/-- Vectors with pairwise distinct values are linearly independent. -/
theorem linearIndependent_of_injective_valuation [Nontrivial D] {I : Type*}
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (u : I → W) (hu : ∀ i, u i ≠ 0)
    (hvalue : Function.Injective (fun i => v (ι (u i)))) : LinearIndependent C u := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter (fun j => g j ≠ 0)
  have hti : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image t (fun j => v (ι (u j))) ⟨i, hti⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsumt : ∑ l ∈ t, g l • u l = 0 := by
    change ∑ l ∈ s.filter (fun l => g l ≠ 0), g l • u l = 0
    rw [Finset.sum_filter]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro l _hl
    split_ifs with h
    · rfl
    · simp only [not_not] at h
      simp [h]
  have hjfinite : v (ι (g j • u j)) ≠ ⊤ := by
    rw [valuation_smul_eq v ι htrivial _ hgj]
    rw [v.ne_top_iff]
    intro hz
    exact hu j (hι (hz.trans (map_zero _).symm))
  have hsmall : ∀ l ∈ t, l ≠ j → v (ι (g j • u j)) < v (ι (g l • u l)) := by
    intro l hl hlj
    have hgl : g l ≠ 0 := (Finset.mem_filter.mp hl).2
    rw [valuation_smul_eq v ι htrivial _ hgj, valuation_smul_eq v ι htrivial _ hgl]
    exact lt_of_le_of_ne (hjmin l hl) (fun heq => hlj (hvalue heq.symm))
  have hval := valuation_sum_eq_of_unique_min v t (fun l => ι (g l • u l)) hj hjfinite hsmall
  rw [← map_sum, hsumt, map_zero, v.map_zero] at hval
  exact hjfinite hval.symm

/-- The values `v(ι(s))`, `s ≠ 0`, of a linear map into the valued field. -/
def valueSet (v : AddValuation E D) (ι : W →ₗ[C] E) : Set D :=
  {a | ∃ s : W, s ≠ 0 ∧ v (ι s) = a}

/-- A representative of a value. -/
def valueRepresentative (v : AddValuation E D) (ι : W →ₗ[C] E)
    (a : valueSet v ι) : W := Classical.choose a.property

theorem valueRepresentative_spec (v : AddValuation E D) (ι : W →ₗ[C] E)
    (a : valueSet v ι) :
    valueRepresentative v ι a ≠ 0 ∧ v (ι (valueRepresentative v ι a)) = a.1 :=
  Classical.choose_spec a.property

theorem linearIndependent_valueRepresentative [Nontrivial D] (v : AddValuation E D) (ι : W →ₗ[C] E)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) :
    LinearIndependent C (valueRepresentative v ι) := by
  apply linearIndependent_of_injective_valuation v ι hι htrivial
  · intro a
    exact (valueRepresentative_spec v ι a).1
  · intro a b hab
    change v (ι (valueRepresentative v ι a)) = v (ι (valueRepresentative v ι b)) at hab
    rw [(valueRepresentative_spec v ι a).2, (valueRepresentative_spec v ι b).2] at hab
    exact Subtype.ext hab

/-- In finite dimension there are finitely many values. -/
theorem valueSet_finite [Nontrivial D] [FiniteDimensional C W]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) :
    (valueSet v ι).Finite := by
  let : Finite (valueSet v ι) := (linearIndependent_valueRepresentative v ι hι htrivial).finite
  exact Set.finite_def.mpr ⟨Fintype.ofFinite (valueSet v ι)⟩

/-- `#v(V^×) ≤ dim V`. -/
theorem card_valueSet_le_finrank [Nontrivial D] [FiniteDimensional C W]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) :
    Nat.card (valueSet v ι) ≤ Module.finrank C W := by
  classical
  let : Fintype (valueSet v ι) := (valueSet_finite v ι hι htrivial).fintype
  rw [Nat.card_eq_fintype_card]
  exact (linearIndependent_valueRepresentative v ι hι htrivial).fintype_card_le_finrank

theorem span_of_complete_values {I : Type*} [Fintype I]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (u : I → W) (hu : ∀ i, u i ≠ 0)
    (hcomplete : ∀ s : W, s ≠ 0 → ∃ i, v (ι s) = v (ι (u i)))
    (hcancel : ∀ s t : W, s ≠ 0 → t ≠ 0 → v (ι s) = v (ι t) →
      ∃ c : C, c ≠ 0 ∧ v (ι s) < v (ι (s + c • t))) :
    Submodule.span C (Set.range u) = ⊤ := by
  classical
  let S := Submodule.span C (Set.range u)
  let upper (s : W) := Finset.univ.filter (fun i => v (ι s) < v (ι (u i)))
  let count (s : W) := (upper s).card
  have hmem : ∀ N : ℕ, ∀ s : W, count s = N → s ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro s hN
        by_cases hs : s = 0
        · simpa only [hs] using S.zero_mem
        obtain ⟨i, hi⟩ := hcomplete s hs
        obtain ⟨c, _hc, hinc⟩ := hcancel s (u i) hs (hu i) hi
        let t := s + c • u i
        have hui : u i ∈ S := Submodule.subset_span (Set.mem_range_self i)
        have ht : t ∈ S := by
          by_cases htzero : t = 0
          · simpa only [htzero] using S.zero_mem
          obtain ⟨j, hj⟩ := hcomplete t htzero
          have hsub : upper t ⊆ upper s := by
            intro k hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              hinc.trans (Finset.mem_filter.mp hk).2⟩
          have hne : upper t ≠ upper s := by
            intro heq
            have hjmem : j ∈ upper s :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc.trans_eq hj⟩
            have hjt : j ∈ upper t := heq.symm ▸ hjmem
            have hbad := (Finset.mem_filter.mp hjt).2
            exact (lt_irrefl _) (hbad.trans_eq hj.symm)
          have hlt : count t < N :=
            (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)).trans_eq hN
          exact ih (count t) hlt t rfl
        have hsub := S.sub_mem ht (S.smul_mem c hui)
        simpa only [t, add_sub_cancel_right] using hsub
  apply top_unique
  intro s _hs
  exact hmem (count s) s rfl

/-- **`#v(V^×) = dim V` under cancellation** (`[LM09, Lemma 1.3]`). -/
theorem card_valueSet_eq_finrank [Nontrivial D] [FiniteDimensional C W]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (hcancel : ∀ s t : W, s ≠ 0 → t ≠ 0 → v (ι s) = v (ι t) →
      ∃ c : C, c ≠ 0 ∧ v (ι s) < v (ι (s + c • t))) :
    Nat.card (valueSet v ι) = Module.finrank C W := by
  classical
  let : Fintype (valueSet v ι) := (valueSet_finite v ι hι htrivial).fintype
  have hcomplete : ∀ s : W, s ≠ 0 → ∃ a : valueSet v ι,
      v (ι s) = v (ι (valueRepresentative v ι a)) := by
    intro s hs
    let a : valueSet v ι := ⟨v (ι s), s, hs, rfl⟩
    exact ⟨a, (valueRepresentative_spec v ι a).2.symm⟩
  have hspan := span_of_complete_values v ι (valueRepresentative v ι)
    (fun a => (valueRepresentative_spec v ι a).1) hcomplete hcancel
  let b := Module.Basis.mk (linearIndependent_valueRepresentative v ι hι htrivial) hspan.ge
  simpa only [Nat.card_eq_fintype_card] using (Module.finrank_eq_card_basis b).symm

end LinearAlgebra

/-! ### `ℤⁿ_lex`-valued valuations of fields containing `ℂ` -/

section Leaves

variable {n : ℕ} {K : Type*} [Field K] [Algebra ℂ K]
  (v : AddValuation K (WithTop (Lex (Fin n → ℤ))))

/-- A `ℤⁿ_lex`-valued valuation is trivial on `ℂ^×`. -/
theorem valuation_algebraMap_complex {c : ℂ} (hc : c ≠ 0) : v (algebraMap ℂ K c) = 0 :=
  SGPT.Okounkov.AlgebraicValuation.valuation_algebraMap_eq_zero v (algebraMap ℂ K) hc

omit [Algebra ℂ K] in
theorem valuation_multiset_prod_eq_zero (m : Multiset K) (h : ∀ x ∈ m, v x = 0) :
    v m.prod = 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, v.map_mul, h a (Multiset.mem_cons_self a m),
      ih fun x hx => h x (Multiset.mem_cons_of_mem hx), add_zero]

/-- **Residually transcendental elements**: if `v(g - c) = 0` for every `c ∈ ℂ`, then
`v(p(g)) = 0` for every nonzero `p ∈ ℂ[T]`. -/
theorem valuation_aeval_eq_zero {g : K} (hg : ∀ c : ℂ, v (g - algebraMap ℂ K c) = 0)
    {p : ℂ[X]} (hp : p ≠ 0) : v (aeval g p) = 0 := by
  have hroots : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [← hfac, map_mul, aeval_C, map_multiset_prod, Multiset.map_map, v.map_mul,
    valuation_algebraMap_complex v (leadingCoeff_ne_zero.mpr hp), zero_add]
  apply valuation_multiset_prod_eq_zero
  intro x hx
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hx
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
  exact hg r

/-- `v(∑_b c_b g^b) = 0` for a residually transcendental `g` and coefficients not all zero. -/
theorem valuation_sum_mul_pow_eq_zero {g : K} (hg : ∀ c : ℂ, v (g - algebraMap ℂ K c) = 0)
    {d : ℕ} (c : Fin (d + 1) → ℂ) (hc : ∃ b, c b ≠ 0) :
    v (∑ b : Fin (d + 1), algebraMap ℂ K (c b) * g ^ (b : ℕ)) = 0 := by
  classical
  let p : ℂ[X] := ∑ b : Fin (d + 1), C (c b) * X ^ (b : ℕ)
  have hp : p ≠ 0 := by
    obtain ⟨b₀, hb₀⟩ := hc
    intro h0
    have hcoeff : p.coeff (b₀ : ℕ) = c b₀ := by
      simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    rw [h0, coeff_zero] at hcoeff
    exact hb₀ hcoeff.symm
  have heval : aeval g p = ∑ b : Fin (d + 1), algebraMap ℂ K (c b) * g ^ (b : ℕ) := by
    simp only [p, map_sum, map_mul, aeval_C, map_pow, aeval_X]
  rw [← heval]
  exact valuation_aeval_eq_zero v hg hp

/-- If two vectors of the same value admit no cancellation, the residue of their quotient is not
a constant. -/
theorem valuation_div_sub_eq_zero {x y : K} (hy : y ≠ 0) (hxy : v x = v y)
    (hcon : ∀ c : ℂ, c ≠ 0 → ¬ v x < v (x + algebraMap ℂ K c * y)) (c : ℂ) :
    v (x * y⁻¹ - algebraMap ℂ K c) = 0 := by
  have hx : v (x + algebraMap ℂ K (-c) * y) = v x := by
    by_cases hc : c = 0
    · simp [hc]
    · refine le_antisymm (not_lt.mp (hcon (-c) (neg_ne_zero.mpr hc))) ?_
      refine le_trans ?_ (v.map_add _ _)
      rw [valuation_algebraMap_mul v (fun c hc => valuation_algebraMap_complex v hc) (-c)
        (neg_ne_zero.mpr hc), ← hxy, min_self]
  have heq : x * y⁻¹ - algebraMap ℂ K c = (x + algebraMap ℂ K (-c) * y) * y⁻¹ := by
    rw [add_mul, mul_assoc (algebraMap ℂ K (-c)) y, mul_inv_cancel₀ hy, mul_one, map_neg]
    ring
  rw [heq, v.map_mul, hx, hxy, ← v.map_mul, mul_inv_cancel₀ hy, v.map_one]

variable {v}

/-- Powers in a graded family. -/
theorem pow_mem_of_graded {R : ℕ → Submodule ℂ K} (hone : (1 : K) ∈ R 0)
    (hmul : ∀ {m k : ℕ} {x y : K}, x ∈ R m → y ∈ R k → x * y ∈ R (m + k))
    {k : ℕ} {x : K} (hx : x ∈ R k) (b : ℕ) : x ^ b ∈ R (b * k) := by
  induction b with
  | zero => simpa using hone
  | succ b ih =>
    have h := hmul ih hx
    rw [show b * k + k = (b + 1) * k by ring] at h
    rwa [pow_succ]

/-- **The product family is linearly independent.** For representatives `u_w ∈ R_M` of the values
`w` of `R_M` and `x, y ∈ R_k` of equal value without cancellation, the elements
`u_w x^b y^{d-b}` (`0 ≤ b ≤ d`) are linearly independent, so
`(d + 1) #v(R_M^×) ≤ dim R_{M + dk}`. -/
theorem succ_mul_card_valueSet_le_finrank {R : ℕ → Submodule ℂ K}
    (hfin : ∀ m, FiniteDimensional ℂ (R m)) (hone : (1 : K) ∈ R 0)
    (hmul : ∀ {m k : ℕ} {x y : K}, x ∈ R m → y ∈ R k → x * y ∈ R (m + k))
    {k : ℕ} {x y : K} (hx : x ∈ R k) (hy : y ∈ R k) (hy0 : y ≠ 0) (hxy : v x = v y)
    (hcon : ∀ c : ℂ, c ≠ 0 → ¬ v x < v (x + algebraMap ℂ K c * y)) (M d : ℕ) :
    (d + 1) * Nat.card (valueSet v (R M).subtype) ≤ Module.finrank ℂ (R (M + d * k)) := by
  classical
  have htrivial : ∀ c : ℂ, c ≠ 0 → v (algebraMap ℂ K c) = 0 :=
    fun c hc => valuation_algebraMap_complex v hc
  have hfinM := hfin M
  have hfinN := hfin (M + d * k)
  let : Fintype (valueSet v (R M).subtype) :=
    (valueSet_finite v (R M).subtype Subtype.val_injective htrivial).fintype
  let g : K := x * y⁻¹
  have hgy : g * y = x := by simp only [g, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
  have hg : ∀ c : ℂ, v (g - algebraMap ℂ K c) = 0 :=
    valuation_div_sub_eq_zero v hy0 hxy hcon
  let u : valueSet v (R M).subtype → K :=
    fun w => ((valueRepresentative v (R M).subtype w : R M) : K)
  have hu : ∀ w : valueSet v (R M).subtype, u w ∈ R M :=
    fun w => (valueRepresentative v (R M).subtype w).2
  have huv : ∀ w : valueSet v (R M).subtype, v (u w) = w.1 :=
    fun w => (valueRepresentative_spec v _ w).2
  have hu0 : ∀ w : valueSet v (R M).subtype, u w ≠ 0 := by
    intro w h
    apply (valueRepresentative_spec v _ w).1
    exact Subtype.ext h
  have hmemF : ∀ (w : valueSet v (R M).subtype) (b : Fin (d + 1)),
      u w * x ^ (b : ℕ) * y ^ (d - b) ∈ R (M + d * k) := by
    intro w b
    have hb : (b : ℕ) ≤ d := Nat.lt_succ_iff.mp b.2
    have h := hmul (hmul (hu w) (pow_mem_of_graded hone hmul hx b)) (pow_mem_of_graded hone hmul hy
      (d - b))
    rwa [show M + (b : ℕ) * k + (d - b) * k = M + d * k by
      rw [add_assoc, ← add_mul, Nat.add_sub_cancel' hb]] at h
  let F : valueSet v (R M).subtype × Fin (d + 1) → R (M + d * k) := fun i => ⟨_, hmemF i.1 i.2⟩
  have hFeq : ∀ (w : valueSet v (R M).subtype) (b : Fin (d + 1)),
      (F (w, b) : K) = (u w * y ^ d) * g ^ (b : ℕ) := by
    intro w b
    have hb : (b : ℕ) ≤ d := Nat.lt_succ_iff.mp b.2
    change u w * x ^ (b : ℕ) * y ^ (d - b) = _
    rw [← hgy, mul_pow, mul_assoc, mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
    ring
  have hlin : LinearIndependent ℂ F := by
    rw [Fintype.linearIndependent_iff]
    intro a hsum
    by_contra hne
    push Not at hne
    obtain ⟨⟨w₀, b₀⟩, hab₀⟩ := hne
    have hsumK : ∑ i, a i • (F i : K) = 0 := by
      have h := congrArg Subtype.val hsum
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using h
    let q : valueSet v (R M).subtype → K := fun w => ∑ b : Fin (d + 1), algebraMap ℂ K (a (w, b)) * g ^ (b : ℕ)
    have hsplit : ∑ i, a i • (F i : K) = ∑ w, (u w * y ^ d) * q w := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro w _
      simp only [q, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hFeq, Algebra.smul_def]
      ring
    let T : Finset (valueSet v (R M).subtype) := Finset.univ.filter (fun w => ∃ b, a (w, b) ≠ 0)
    have hw₀ : w₀ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, b₀, hab₀⟩
    have hqT : ∀ w ∈ T, v (q w) = 0 := by
      intro w hw
      exact valuation_sum_mul_pow_eq_zero v hg (fun b => a (w, b)) (Finset.mem_filter.mp hw).2
    have hqnT : ∀ w ∉ T, q w = 0 := by
      intro w hw
      have hz : ∀ b, a (w, b) = 0 := by
        intro b
        by_contra h
        exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, h⟩)
      simp [q, hz]
    have hsumT : ∑ w, (u w * y ^ d) * q w = ∑ w ∈ T, (u w * y ^ d) * q w := by
      rw [← Finset.sum_subset (Finset.subset_univ T)]
      intro w _ hw
      rw [hqnT w hw, mul_zero]
    have hyd : v (y ^ d) ≠ ⊤ := (v.ne_top_iff).mpr (pow_ne_zero d hy0)
    have hval : ∀ w ∈ T, v ((u w * y ^ d) * q w) = w.1 + v (y ^ d) := by
      intro w hw
      rw [v.map_mul, v.map_mul, hqT w hw, add_zero, huv]
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image T (fun w : valueSet v (R M).subtype => w.1) ⟨w₀, hw₀⟩
    have hjfin : v ((u j * y ^ d) * q j) ≠ ⊤ := by
      rw [hval j hj]
      refine WithTop.add_ne_top.mpr ⟨?_, hyd⟩
      rw [← huv j]
      exact (v.ne_top_iff).mpr (hu0 j)
    have hjlt : ∀ l ∈ T, l ≠ j → v ((u j * y ^ d) * q j) < v ((u l * y ^ d) * q l) := by
      intro l hl hlj
      rw [hval j hj, hval l hl]
      refine WithTop.add_lt_add_right hyd (lt_of_le_of_ne (hjmin l hl) ?_)
      intro h
      exact hlj (Subtype.ext h.symm)
    have hv := valuation_sum_eq_of_unique_min v T (fun w => (u w * y ^ d) * q w) hj hjfin hjlt
    rw [← hsumT, ← hsplit, hsumK, v.map_zero] at hv
    exact hjfin hv.symm
  have hcard := hlin.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at hcard
  rw [Nat.card_eq_fintype_card, mul_comm]
  exact hcard

/-- **One-dimensional leaves from polynomial growth** (the Abhyankar-type inequality behind
`[LM09, Lemma 1.3]`): for a graded family `R` of finite-dimensional subspaces whose value sets
grow at least like `c₀ Mⁿ` (`c₀ > 0`) and whose dimensions grow at most like `B mⁿ`, any two
nonzero `x, y ∈ R_k` of equal value can be cancelled: `v(x + c y) > v(x)` for some `c ∈ ℂ^×`. -/
theorem exists_leaf_cancel {R : ℕ → Submodule ℂ K}
    (hfin : ∀ m, FiniteDimensional ℂ (R m)) (hone : (1 : K) ∈ R 0)
    (hmul : ∀ {m k : ℕ} {x y : K}, x ∈ R m → y ∈ R k → x * y ∈ R (m + k))
    {c₀ B : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ᶠ M : ℕ in atTop, c₀ * (M : ℝ) ^ n ≤ Nat.card (valueSet v (R M).subtype))
    (hup : ∀ᶠ m : ℕ in atTop, (Module.finrank ℂ (R m) : ℝ) ≤ B * (m : ℝ) ^ n)
    {k : ℕ} {x y : K} (hx : x ∈ R k) (hy : y ∈ R k) (hy0 : y ≠ 0) (hxy : v x = v y) :
    ∃ c : ℂ, c ≠ 0 ∧ v x < v (x + algebraMap ℂ K c * y) := by
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ c : ℂ, c ≠ 0 → ¬ v x < v (x + algebraMap ℂ K c * y) :=
    fun c hc => not_lt.mpr (hcon c hc)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp hlow
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.mp hup
  -- `B ≥ 0`
  have hB : 0 ≤ B := by
    have h := hM₂ (M₂ + 1) (Nat.le_succ _)
    have hpos : (0 : ℝ) < ((M₂ + 1 : ℕ) : ℝ) ^ n := by positivity
    have h0 : (0 : ℝ) ≤ B * ((M₂ + 1 : ℕ) : ℝ) ^ n := (Nat.cast_nonneg _).trans h
    exact nonneg_of_mul_nonneg_left h0 hpos
  set d : ℕ := ⌈B * 2 ^ n / c₀⌉₊ with hd
  have hd' : B * 2 ^ n < ((d : ℝ) + 1) * c₀ := by
    have h1 : B * 2 ^ n / c₀ ≤ d := Nat.le_ceil _
    have h2 : B * 2 ^ n ≤ (d : ℝ) * c₀ := by rwa [div_le_iff₀ hc₀] at h1
    nlinarith
  set M : ℕ := max (max M₁ M₂) (d * k + 1) with hM
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : M₂ ≤ M + d * k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (Nat.le_add_right _ _)
  have hMdk : d * k + 1 ≤ M := le_max_right _ _
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := lt_of_lt_of_le (Nat.succ_pos _) hMdk
    exact_mod_cast this
  have hkey := succ_mul_card_valueSet_le_finrank hfin hone hmul hx hy hy0 hxy hcon' M d
  have hkeyR : ((d : ℝ) + 1) * (Nat.card (valueSet v (R M).subtype) : ℝ) ≤
      (Module.finrank ℂ (R (M + d * k)) : ℝ) := by exact_mod_cast hkey
  have hlowM := hM₁ M hM1
  have hupM := hM₂ (M + d * k) hM2
  have hle2 : ((M + d * k : ℕ) : ℝ) ^ n ≤ (2 * (M : ℝ)) ^ n := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    have : (M + d * k : ℕ) ≤ 2 * M := by omega
    exact_mod_cast this
  have hchain : ((d : ℝ) + 1) * (c₀ * (M : ℝ) ^ n) ≤ B * 2 ^ n * (M : ℝ) ^ n := by
    calc ((d : ℝ) + 1) * (c₀ * (M : ℝ) ^ n)
        ≤ ((d : ℝ) + 1) * (Nat.card (valueSet v (R M).subtype) : ℝ) := by gcongr
      _ ≤ (Module.finrank ℂ (R (M + d * k)) : ℝ) := hkeyR
      _ ≤ B * ((M + d * k : ℕ) : ℝ) ^ n := hupM
      _ ≤ B * (2 * (M : ℝ)) ^ n := by gcongr
      _ = B * 2 ^ n * (M : ℝ) ^ n := by rw [mul_pow, mul_assoc]
  have hMn : (0 : ℝ) < (M : ℝ) ^ n := by positivity
  have : ((d : ℝ) + 1) * c₀ * (M : ℝ) ^ n ≤ B * 2 ^ n * (M : ℝ) ^ n := by
    rw [mul_assoc]; exact hchain
  have := le_of_mul_le_mul_right this hMn
  linarith

/-- **`#v(V^×) = dim V` for every subspace of a graded family with polynomial growth**
(one-dimensional leaves, `[LM09, Lemma 1.3]`). -/
theorem card_valueSet_eq_finrank_of_growth {R : ℕ → Submodule ℂ K}
    (hfin : ∀ m, FiniteDimensional ℂ (R m)) (hone : (1 : K) ∈ R 0)
    (hmul : ∀ {m k : ℕ} {x y : K}, x ∈ R m → y ∈ R k → x * y ∈ R (m + k))
    {c₀ B : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ᶠ M : ℕ in atTop, c₀ * (M : ℝ) ^ n ≤ Nat.card (valueSet v (R M).subtype))
    (hup : ∀ᶠ m : ℕ in atTop, (Module.finrank ℂ (R m) : ℝ) ≤ B * (m : ℝ) ^ n)
    {k : ℕ} (V : Submodule ℂ K) (hV : V ≤ R k) :
    Nat.card (valueSet v V.subtype) = Module.finrank ℂ V := by
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hV
  apply card_valueSet_eq_finrank v V.subtype Subtype.val_injective
    (fun c hc => valuation_algebraMap_complex v hc)
  intro s t _hs ht hst
  obtain ⟨c, hc, hlt⟩ := exists_leaf_cancel hfin hone hmul hc₀ hlow hup (hV s.2) (hV t.2)
    (fun h => ht (Subtype.ext h)) hst
  refine ⟨c, hc, ?_⟩
  simpa only [Submodule.coe_subtype, Submodule.coe_add, Submodule.coe_smul,
    Algebra.smul_def] using hlt

end Leaves

end SGPT.Okounkov.ValGen
