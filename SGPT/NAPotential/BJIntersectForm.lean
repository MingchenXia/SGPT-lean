import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Symmetric multilinear forms on multisets (lane BJ-INTERSECT, pure algebra)

Intersection numbers of `ℚ`-line bundles, and the energy pairing of Boucksom–Jonsson
([BJ22, `defi:intpairing`]) built from them, are symmetric multilinear forms. As in
`SGPT.NAPotential.BJEnergy.EnergyPairing`, we record them as functions of the *multiset* of
their arguments that are linear in each argument (`MultisetForm`); symmetry is then built in.

Main results:

* `MultisetForm.exists_polynomial`: `c ↦ Φ(t + {c • xᵢ + yᵢ})` is a polynomial of degree at most
  `#{i}` whose top coefficient is `Φ(t + {xᵢ})`;
* `MultisetForm.extendRat`: a `ℤ`-valued form on an abelian group `A` extends (uniquely) to a
  `ℚ`-valued form on `ℚ ⊗[ℤ] A` (`extendRat_tmul`);
* `quadratic_nonpos_of_offDiag_nonneg`: Zariski's lemma — a symmetric matrix with nonnegative
  off-diagonal entries and a positive vector in its kernel is negative semidefinite;
  `MultisetForm.sq_nonpos_of_offDiag_nonneg` is its form version, the algebraic core of the
  Hodge-type inequality [BHJ17, Lemma 6.14] = [BJ22, `lem:Hodge`].

Blueprint: `claude-bj-intersect.tex`.
-/

set_option autoImplicit false

open Multiset Polynomial
open scoped TensorProduct

namespace SGPT.NAPotential.BJIntersect

/-- A symmetric multilinear form on an `R`-module `V`, as a function of the multiset of its
arguments which is `R`-linear in each argument. -/
structure MultisetForm (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- The value on a multiset of arguments. -/
  toFun : Multiset V → R
  map_add' : ∀ (x y : V) (s : Multiset V), toFun ((x + y) ::ₘ s) = toFun (x ::ₘ s) + toFun (y ::ₘ s)
  map_smul' : ∀ (c : R) (x : V) (s : Multiset V), toFun ((c • x) ::ₘ s) = c * toFun (x ::ₘ s)

/-- **Zariski's lemma.** A real symmetric matrix with nonnegative off-diagonal entries which
kills a vector with positive entries is negative semidefinite. -/
theorem quadratic_nonpos_of_offDiag_nonneg {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {ι : Type*} [Fintype ι] (M : ι → ι → K)
    (hM : ∀ i j, M i j = M j i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (b : ι → K)
    (hb : ∀ i, 0 < b i) (hMb : ∀ i, ∑ j, M i j * b j = 0) (x : ι → K) :
    ∑ i, ∑ j, M i j * x i * x j ≤ 0 := by
  classical
  set y : ι → K := fun i => x i / b i with hy
  have hxy : ∀ i, x i = b i * y i := fun i => by
    rw [hy]; field_simp [(hb i).ne']
  -- the identity `2 xᵀ M x = - ∑ M_ij b_i b_j (y_i - y_j)²`
  have hA : ∑ i, ∑ j, M i j * b i * b j * y i ^ 2 = 0 := by
    have : ∀ i, ∑ j, M i j * b i * b j * y i ^ 2 = b i * y i ^ 2 * ∑ j, M i j * b j := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp [this, hMb]
  have hB : ∑ i, ∑ j, M i j * b i * b j * y j ^ 2 = 0 := by
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, M i j * b i * b j * y j ^ 2 = b j * y j ^ 2 * ∑ i, M j i * b i := by
      intro j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hM i j]; ring
    simp [this, hMb]
  have hid : 2 * ∑ i, ∑ j, M i j * x i * x j =
      -∑ i, ∑ j, M i j * b i * b j * (y i - y j) ^ 2 := by
    have hexp : ∀ i j, M i j * b i * b j * (y i - y j) ^ 2 =
        M i j * b i * b j * y i ^ 2 + M i j * b i * b j * y j ^ 2 -
          2 * (M i j * x i * x j) := by
      intro i j; rw [hxy i, hxy j]; ring
    simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, ← Finset.mul_sum]
    ring
  have hnn : 0 ≤ ∑ i, ∑ j, M i j * b i * b j * (y i - y j) ^ 2 := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i j hij) (hb i).le) (hb j).le) (sq_nonneg _)
  nlinarith


namespace MultisetForm

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

instance : CoeFun (MultisetForm R V) (fun _ => Multiset V → R) := ⟨MultisetForm.toFun⟩

variable (Φ : MultisetForm R V)

@[simp] theorem toFun_eq_coe : Φ.toFun = ⇑Φ := rfl

theorem map_add (x y : V) (s : Multiset V) : Φ ((x + y) ::ₘ s) = Φ (x ::ₘ s) + Φ (y ::ₘ s) :=
  Φ.map_add' x y s

theorem map_smul (c : R) (x : V) (s : Multiset V) : Φ ((c • x) ::ₘ s) = c * Φ (x ::ₘ s) :=
  Φ.map_smul' c x s

@[simp] theorem map_zero_cons (s : Multiset V) : Φ ((0 : V) ::ₘ s) = 0 := by
  have h := Φ.map_smul 0 0 s
  rwa [zero_smul, zero_mul] at h

theorem map_neg (x : V) (s : Multiset V) : Φ ((-x) ::ₘ s) = -Φ (x ::ₘ s) := by
  have h := Φ.map_smul (-1) x s
  rwa [neg_one_smul, neg_one_mul] at h

theorem map_sub (x y : V) (s : Multiset V) : Φ ((x - y) ::ₘ s) = Φ (x ::ₘ s) - Φ (y ::ₘ s) := by
  rw [sub_eq_add_neg, Φ.map_add, Φ.map_neg, ← sub_eq_add_neg]

theorem map_sum {ι : Type*} (I : Finset ι) (x : ι → V) (s : Multiset V) :
    Φ ((∑ i ∈ I, x i) ::ₘ s) = ∑ i ∈ I, Φ (x i ::ₘ s) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ.map_add, ih]

theorem map_sum_smul {ι : Type*} (I : Finset ι) (c : ι → R) (x : ι → V) (s : Multiset V) :
    Φ ((∑ i ∈ I, c i • x i) ::ₘ s) = ∑ i ∈ I, c i * Φ (x i ::ₘ s) := by
  rw [Φ.map_sum]
  exact Finset.sum_congr rfl fun i _ => Φ.map_smul _ _ _

/-- Linearity in the second argument. -/
theorem map_add_snd (z x y : V) (s : Multiset V) :
    Φ (z ::ₘ (x + y) ::ₘ s) = Φ (z ::ₘ x ::ₘ s) + Φ (z ::ₘ y ::ₘ s) := by
  rw [cons_swap, Φ.map_add, cons_swap z x, cons_swap z y]

theorem map_sum_smul_snd {ι : Type*} (I : Finset ι) (z : V) (c : ι → R) (x : ι → V)
    (s : Multiset V) : Φ (z ::ₘ (∑ i ∈ I, c i • x i) ::ₘ s) = ∑ i ∈ I, c i * Φ (z ::ₘ x i ::ₘ s) := by
  rw [cons_swap, Φ.map_sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [cons_swap]

/-- `Φ` has degree `d`: it vanishes on multisets of cardinality different from `d`. -/
def HasDegree (d : ℕ) : Prop := ∀ s : Multiset V, card s ≠ d → Φ s = 0

/-- A function on multisets of elements of an abelian group which is additive in each argument
is a `ℤ`-valued multiset form. -/
def ofAdd {A : Type*} [AddCommGroup A] (f : Multiset A → ℤ)
    (hf : ∀ (x y : A) (s : Multiset A), f ((x + y) ::ₘ s) = f (x ::ₘ s) + f (y ::ₘ s)) :
    MultisetForm ℤ A where
  toFun := f
  map_add' := hf
  map_smul' c x s := by
    let g : A →+ ℤ := AddMonoidHom.mk' (fun y => f (y ::ₘ s)) fun y z => hf y z s
    change g (c • x) = c * g x
    rw [map_zsmul, smul_eq_mul]

@[simp] theorem ofAdd_apply {A : Type*} [AddCommGroup A] (f : Multiset A → ℤ)
    (hf : ∀ (x y : A) (s : Multiset A), f ((x + y) ::ₘ s) = f (x ::ₘ s) + f (y ::ₘ s))
    (s : Multiset A) : ofAdd f hf s = f s := rfl

/-- Scalars can be pulled out of a whole list of arguments. -/
theorem map_smul_list {ι : Type*} (c : ι → R) (v : ι → V) (l : List ι) (t : Multiset V) :
    Φ (t + ((l.map fun i => c i • v i : List V) : Multiset V)) =
      (l.map c).prod * Φ (t + ((l.map v : List V) : Multiset V)) := by
  induction l generalizing t with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Multiset.cons_coe, Multiset.add_cons, Φ.map_smul, ← Multiset.cons_add, ih,
      ← Multiset.cons_coe, Multiset.add_cons, ← Multiset.cons_add]
    ring

/-- Composition of a multiset form with a linear map. -/
def comp {W : Type*} [AddCommGroup W] [Module R W] (Ψ : MultisetForm R W) (f : V →ₗ[R] W) :
    MultisetForm R V where
  toFun s := Ψ (s.map f)
  map_add' x y s := by
    show Ψ (((x + y) ::ₘ s).map f) = Ψ ((x ::ₘ s).map f) + Ψ ((y ::ₘ s).map f)
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, f.map_add, Ψ.map_add]
  map_smul' c x s := by
    show Ψ (((c • x) ::ₘ s).map f) = c * Ψ ((x ::ₘ s).map f)
    rw [Multiset.map_cons, Multiset.map_cons, f.map_smul, Ψ.map_smul]

@[simp] theorem comp_apply {W : Type*} [AddCommGroup W] [Module R W] (Ψ : MultisetForm R W)
    (f : V →ₗ[R] W) (s : Multiset V) : Ψ.comp f s = Ψ (s.map f) := rfl

/-- The form with some arguments fixed: `s ↦ Φ(t + s)`. -/
def fix (t : Multiset V) : MultisetForm R V where
  toFun s := Φ (t + s)
  map_add' x y s := by simp only [Multiset.add_cons, Φ.map_add]
  map_smul' c x s := by simp only [Multiset.add_cons, Φ.map_smul]

@[simp] theorem fix_apply (t s : Multiset V) : Φ.fix t s = Φ (t + s) := rfl

/-! ### Polynomial expansion -/

/-- **Polynomial expansion.** For a multiset form `Φ`, a multiset `t` and a multiset of pairs
`(xᵢ, yᵢ)`, the function `c ↦ Φ(t + {c • xᵢ + yᵢ})` is a polynomial of degree at most the number
of pairs, whose coefficient in that degree is `Φ(t + {xᵢ})`. -/
theorem exists_polynomial (s : Multiset (V × V)) (t : Multiset V) :
    ∃ P : R[X], P.natDegree ≤ card s ∧ P.coeff (card s) = Φ (t + s.map Prod.fst) ∧
      ∀ c : R, P.eval c = Φ (t + s.map fun q => c • q.1 + q.2) := by
  induction s using Multiset.induction_on generalizing t with
  | empty =>
    refine ⟨C (Φ t), ?_, ?_, ?_⟩
    · simp
    · simp
    · intro c; simp
  | cons q s ih =>
    obtain ⟨P₁, hd₁, hc₁, he₁⟩ := ih (q.1 ::ₘ t)
    obtain ⟨P₂, hd₂, -, he₂⟩ := ih (q.2 ::ₘ t)
    refine ⟨X * P₁ + P₂, ?_, ?_, ?_⟩
    · rw [card_cons]
      refine (natDegree_add_le _ _).trans (max_le ?_ (hd₂.trans (Nat.le_succ _)))
      refine (natDegree_mul_le).trans ?_
      have : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
      omega
    · rw [card_cons, coeff_add, coeff_X_mul, hc₁,
        coeff_eq_zero_of_natDegree_lt (hd₂.trans_lt (Nat.lt_succ_self _)), add_zero,
        map_cons, add_cons, cons_add]
    · intro c
      rw [eval_add, eval_mul, eval_X, he₁, he₂, map_cons, add_cons, Φ.map_add, Φ.map_smul,
        cons_add, cons_add]

/-! ### Extension of scalars from `ℤ` to `ℚ` -/

section extend

variable {A : Type*} [AddCommGroup A]

/-- Every element of `ℚ ⊗[ℤ] A` is `N⁻¹ ⊗ a` for some nonzero integer `N`. -/
theorem exists_rep (x : ℚ ⊗[ℤ] A) : ∃ (N : ℤ) (a : A), N ≠ 0 ∧ (N : ℚ) • x = 1 ⊗ₜ a := by
  obtain ⟨⟨a, N⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1) x
  refine ⟨N, a, nonZeroDivisors.coe_ne_zero N, ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  exact h

/-- Two vectors with the same image in `ℚ ⊗[ℤ] A` differ by torsion. -/
theorem exists_smul_eq_of_tmul_eq {a b : A} (h : (1 : ℚ) ⊗ₜ[ℤ] a = 1 ⊗ₜ b) :
    ∃ c : ℤ, c ≠ 0 ∧ c • a = c • b := by
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ)
    (f := TensorProduct.mk ℤ ℚ A 1) h
  exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩

/-- A chosen denominator of an element of `ℚ ⊗[ℤ] A`. -/
noncomputable def den (x : ℚ ⊗[ℤ] A) : ℤ := (exists_rep x).choose

/-- A chosen numerator of an element of `ℚ ⊗[ℤ] A`. -/
noncomputable def num (x : ℚ ⊗[ℤ] A) : A := (exists_rep x).choose_spec.choose

theorem den_ne_zero (x : ℚ ⊗[ℤ] A) : den x ≠ 0 := (exists_rep x).choose_spec.choose_spec.1

theorem den_smul (x : ℚ ⊗[ℤ] A) : (den x : ℚ) • x = 1 ⊗ₜ num x :=
  (exists_rep x).choose_spec.choose_spec.2

variable (Φ : MultisetForm ℤ A)

theorem map_zsmul (n : ℤ) (a : A) (s : Multiset A) : Φ ((n • a) ::ₘ s) = n * Φ (a ::ₘ s) :=
  Φ.map_smul n a s

/-- Independence of the representative: if `N • x = 1 ⊗ a`, then `Φ(a, …) / N` agrees with
`Φ(num x, …) / den x`. -/
theorem den_mul_eq (x : ℚ ⊗[ℤ] A) (N : ℤ) (a : A)
    (hx : (N : ℚ) • x = 1 ⊗ₜ a) (s : Multiset A) :
    den x * Φ (a ::ₘ s) = N * Φ (num x ::ₘ s) := by
  have h : (1 : ℚ) ⊗ₜ[ℤ] (den x • a) = 1 ⊗ₜ (N • num x) := by
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hx, ← den_smul,
      ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, mul_comm]
  obtain ⟨c, hc, hca⟩ := exists_smul_eq_of_tmul_eq h
  have := congrArg (fun z => Φ (z ::ₘ s)) hca
  simp only [Φ.map_zsmul] at this
  have h2 := mul_left_cancel₀ hc this
  linarith [h2]

/-- Simultaneous replacement of representatives. -/
theorem div_prod_eq (s : Multiset ((ℚ ⊗[ℤ] A) × (ℤ × A)))
    (hs : ∀ q ∈ s, q.2.1 ≠ 0 ∧ (q.2.1 : ℚ) • q.1 = 1 ⊗ₜ q.2.2)
    (u : Multiset (ℚ ⊗[ℤ] A)) :
    (Φ (s.map (fun q => q.2.2) + u.map num) : ℚ) /
        ((s.map fun q => (q.2.1 : ℚ)).prod * (u.map fun x => (den x : ℚ)).prod) =
      (Φ ((s.map Prod.fst + u).map num) : ℚ) /
        ((s.map Prod.fst + u).map fun x => (den x : ℚ)).prod := by
  induction s using Multiset.induction_on generalizing u with
  | empty => simp
  | cons q s ih =>
    have hq := hs q (mem_cons_self _ _)
    have hs' : ∀ r ∈ s, r.2.1 ≠ 0 ∧ (r.2.1 : ℚ) • r.1 = 1 ⊗ₜ r.2.2 :=
      fun r hr => hs r (mem_cons_of_mem hr)
    have key := den_mul_eq Φ q.1 q.2.1 q.2.2 hq.2 (s.map (fun q => q.2.2) + u.map num)
    have hdq : (den q.1 : ℚ) ≠ 0 := by exact_mod_cast den_ne_zero q.1
    have hNq : (q.2.1 : ℚ) ≠ 0 := by exact_mod_cast hq.1
    have ih' := ih hs' (q.1 ::ₘ u)
    simp only [map_cons, prod_cons, cons_add, add_cons] at ih' ⊢
    rw [← ih']
    have key' : (Φ (q.2.2 ::ₘ (s.map (fun q => q.2.2) + u.map num)) : ℚ) / q.2.1 =
        (Φ (num q.1 ::ₘ (s.map (fun q => q.2.2) + u.map num)) : ℚ) / den q.1 := by
      rw [div_eq_div_iff hNq hdq]
      exact_mod_cast (by linarith [key] :
        Φ (q.2.2 ::ₘ (s.map (fun q => q.2.2) + u.map num)) * den q.1 =
          Φ (num q.1 ::ₘ (s.map (fun q => q.2.2) + u.map num)) * q.2.1)
    rw [mul_assoc, ← div_div, key', div_div]
    congr 1
    ring

/-- The `ℚ`-valued extension, on representatives. -/
noncomputable def extendRatFun (s : Multiset (ℚ ⊗[ℤ] A)) : ℚ :=
  (Φ (s.map num) : ℚ) / (s.map fun x => (den x : ℚ)).prod

/-- The extension can be computed with any representatives. -/
theorem extendRatFun_eq (s : Multiset ((ℚ ⊗[ℤ] A) × (ℤ × A)))
    (hs : ∀ q ∈ s, q.2.1 ≠ 0 ∧ (q.2.1 : ℚ) • q.1 = 1 ⊗ₜ q.2.2) :
    extendRatFun Φ (s.map Prod.fst) =
      (Φ (s.map fun q => q.2.2) : ℚ) / (s.map fun q => (q.2.1 : ℚ)).prod := by
  have h := div_prod_eq Φ s hs 0
  simp only [Multiset.map_zero, add_zero, prod_zero, mul_one] at h
  rw [h]
  rfl

/-- **Extension of scalars.** A `ℤ`-valued multiset form on an abelian group `A` extends to a
`ℚ`-valued multiset form on `ℚ ⊗[ℤ] A`. -/
noncomputable def extendRat : MultisetForm ℚ (ℚ ⊗[ℤ] A) where
  toFun := extendRatFun Φ
  map_add' x y s := by
    -- representatives of `x + y`, `x`, `y` and of the entries of `s`
    let r : Multiset ((ℚ ⊗[ℤ] A) × (ℤ × A)) := s.map fun z => (z, den z, num z)
    have hr : ∀ q ∈ r, q.2.1 ≠ 0 ∧ (q.2.1 : ℚ) • q.1 = 1 ⊗ₜ q.2.2 := by
      intro q hq
      obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hq
      exact ⟨den_ne_zero z, den_smul z⟩
    have hrs : r.map Prod.fst = s := by simp [r]
    have hxy : ((den x * den y : ℤ) : ℚ) • (x + y) =
        1 ⊗ₜ (den y • num x + den x • num y) := by
      rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        ← den_smul, ← den_smul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul, smul_add, Int.cast_mul]
      congr 1
      rw [mul_comm]
    have hdx := den_ne_zero x
    have hdy := den_ne_zero y
    have h1 := extendRatFun_eq Φ ((x + y, den x * den y, den y • num x + den x • num y) ::ₘ r)
      (by
        intro q hq
        rcases mem_cons.mp hq with rfl | hq
        · exact ⟨mul_ne_zero hdx hdy, hxy⟩
        · exact hr q hq)
    have h2 := extendRatFun_eq Φ ((x, den x, num x) ::ₘ r)
      (by
        intro q hq
        rcases mem_cons.mp hq with rfl | hq
        · exact ⟨hdx, den_smul x⟩
        · exact hr q hq)
    have h3 := extendRatFun_eq Φ ((y, den y, num y) ::ₘ r)
      (by
        intro q hq
        rcases mem_cons.mp hq with rfl | hq
        · exact ⟨hdy, den_smul y⟩
        · exact hr q hq)
    simp only [map_cons, hrs, prod_cons] at h1 h2 h3
    rw [h1, h2, h3, Φ.map_add, Φ.map_zsmul, Φ.map_zsmul]
    have hdxq : (den x : ℚ) ≠ 0 := by exact_mod_cast hdx
    have hdyq : (den y : ℚ) ≠ 0 := by exact_mod_cast hdy
    push_cast
    field_simp
  map_smul' c x s := by
    let r : Multiset ((ℚ ⊗[ℤ] A) × (ℤ × A)) := s.map fun z => (z, den z, num z)
    have hr : ∀ q ∈ r, q.2.1 ≠ 0 ∧ (q.2.1 : ℚ) • q.1 = 1 ⊗ₜ q.2.2 := by
      intro q hq
      obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hq
      exact ⟨den_ne_zero z, den_smul z⟩
    have hrs : r.map Prod.fst = s := by simp [r]
    have hdx := den_ne_zero x
    have hcd : (c.den : ℤ) ≠ 0 := by exact_mod_cast c.den_ne_zero
    have hcx : (((c.den : ℤ) * den x : ℤ) : ℚ) • (c • x) = 1 ⊗ₜ (c.num • num x) := by
      rw [TensorProduct.tmul_smul, ← den_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul,
        Int.cast_mul, mul_assoc, mul_comm (den x : ℚ), ← mul_assoc]
      congr 1
      rw [Int.cast_natCast, Rat.den_mul_eq_num]
    have h1 := extendRatFun_eq Φ ((c • x, c.den * den x, c.num • num x) ::ₘ r)
      (by
        intro q hq
        rcases mem_cons.mp hq with rfl | hq
        · exact ⟨mul_ne_zero hcd hdx, hcx⟩
        · exact hr q hq)
    have h2 := extendRatFun_eq Φ ((x, den x, num x) ::ₘ r)
      (by
        intro q hq
        rcases mem_cons.mp hq with rfl | hq
        · exact ⟨hdx, den_smul x⟩
        · exact hr q hq)
    simp only [map_cons, hrs, prod_cons] at h1 h2
    rw [h1, h2, Φ.map_zsmul]
    have hdxq : (den x : ℚ) ≠ 0 := by exact_mod_cast hdx
    have hcdq : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_ne_zero
    push_cast
    conv_rhs => rw [← Rat.num_div_den c]
    field_simp

/-- The extension agrees with `Φ` on integral classes. -/
theorem extendRat_tmul (s : Multiset A) :
    extendRat Φ (s.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) = Φ s := by
  have h := extendRatFun_eq Φ (s.map fun a => ((1 : ℚ) ⊗ₜ[ℤ] a, (1 : ℤ), a))
    (by
      intro q hq
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hq
      exact ⟨one_ne_zero, by simp⟩)
  simp only [Multiset.map_map, Function.comp_def, Int.cast_one, map_const', prod_replicate,
    one_pow, div_one, Multiset.map_id'] at h
  exact h

/-- Two `ℚ`-valued multiset forms on `ℚ ⊗[ℤ] A` that agree on integral classes agree. -/
theorem ext_tmul (Ψ₁ Ψ₂ : MultisetForm ℚ (ℚ ⊗[ℤ] A))
    (h : ∀ s : Multiset A, Ψ₁ (s.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) =
      Ψ₂ (s.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a)) (s : Multiset (ℚ ⊗[ℤ] A)) : Ψ₁ s = Ψ₂ s := by
  -- induction on `s`, keeping a multiset of integral classes in front
  suffices H : ∀ (s : Multiset (ℚ ⊗[ℤ] A)) (u : Multiset A),
      Ψ₁ ((u.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) + s) = Ψ₂ ((u.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) + s) by
    simpa using H s 0
  intro s
  induction s using Multiset.induction_on with
  | empty => intro u; simpa using h u
  | cons x s ih =>
    intro u
    have hx : x = (den x : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] num x) := by
      rw [← den_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast den_ne_zero x), one_smul]
    rw [Multiset.add_cons, hx, Ψ₁.map_smul, Ψ₂.map_smul, ← Multiset.cons_add]
    have := ih (num x ::ₘ u)
    rw [Multiset.map_cons] at this
    rw [this]

theorem extendRat_hasDegree {d : ℕ} (h : Φ.HasDegree d) : (extendRat Φ).HasDegree d := by
  intro s hs
  change (Φ (s.map num) : ℚ) / _ = 0
  rw [h (s.map num) (by rwa [card_map]), Int.cast_zero, zero_div]

end extend

/-! ### Zariski's lemma -/

/-- The form version of Zariski's lemma: if `Φ(eᵢ, eⱼ, t) ≥ 0` for `i ≠ j` and
`∑ⱼ bⱼ Φ(eᵢ, eⱼ, t) = 0` with all `bⱼ > 0`, then `Φ(D, D, t) ≤ 0` for every `D` in the span of the
`eᵢ`. -/
theorem sq_nonpos_of_offDiag_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W : Type*} [AddCommGroup W] [Module K W] (Φ : MultisetForm K W) {ι : Type*} [Fintype ι]
    (e : ι → W) (t : Multiset W) (b : ι → K) (hb : ∀ i, 0 < b i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Φ (e i ::ₘ e j ::ₘ t))
    (hker : ∀ i, Φ (e i ::ₘ (∑ j, b j • e j) ::ₘ t) = 0) (x : ι → K) :
    Φ ((∑ i, x i • e i) ::ₘ (∑ i, x i • e i) ::ₘ t) ≤ 0 := by
  have hexp : Φ ((∑ i, x i • e i) ::ₘ (∑ i, x i • e i) ::ₘ t) =
      ∑ i, ∑ j, Φ (e i ::ₘ e j ::ₘ t) * x i * x j := by
    rw [Φ.map_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.map_sum_smul_snd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  refine quadratic_nonpos_of_offDiag_nonneg (fun i j => Φ (e i ::ₘ e j ::ₘ t))
    (fun i j => by rw [cons_swap]) hoff b hb (fun i => ?_) x
  have h := hker i
  rw [Φ.map_sum_smul_snd] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by ring

end MultisetForm

end SGPT.NAPotential.BJIntersect
