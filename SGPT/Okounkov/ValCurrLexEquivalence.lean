import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Order.WellFounded

/-!
# Unitriangular matrices, `Aut(ℤⁿ_lex)` and equivalence of `ℤⁿ`-valued valuations

Source: chapter *The theory of Okounkov bodies*, subsection *The algebraic setting* of
*Flags and valuations*: the identification of `Aut(ℤⁿ_lex)` (row-vector convention) with the
matrices `I + U`, `U` strictly upper triangular with integral entries, stated just before
`rmk:Abhyankar`, and the footnote of `rmk:Abhyankar`: two valuations `ν, ν'` with values in
`ℤⁿ` are *equivalent* if `ν' = ν G` for a matrix `G` of the form `I + N`, `N` strictly upper
triangular with integral entries.

## Main definitions

* `IsUnitUpperTriangular G`: `G = I + N` with `N` strictly upper triangular
  (`G i i = 1`, `G i j = 0` for `j < i`).
* `unitriangularLexEquiv G hG : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)`, `x ↦ x G`.
* `LexEquivalent ν ν'`: the footnote's relation `∃ G = I + N, ν' = ν G` for maps into `ℤⁿ`;
  `AddValuation.lexMap` and `ValuationsLexEquivalent` for valuations with values in
  `ℤⁿ_lex ∪ {∞}`.

## Main results

* `IsUnitUpperTriangular.mul`, `.inv`, `det_eq_one`: the unitriangular matrices form a group.
* `strictMono_vecMul`: `x ↦ x G` is strictly increasing for the lexicographic order, so it is an
  ordered additive automorphism of `ℤⁿ_lex`.
* `exists_unitriangular_of_orderAddEquiv`: conversely every ordered additive automorphism
  `g` of `ℤⁿ_lex` is `x ↦ x G` for a unique-entry matrix `G = I + N` (the rows of `G` are the
  images of the unit vectors). Together: `Aut(ℤⁿ_lex) ≅ {I + N}`.
* `lexEquivalent_equivalence`, `valuationsLexEquivalent_equivalence`: the footnote's relation is
  an equivalence relation; `AddValuation.lexMap` shows that `ν G` is again a valuation.
* `lexEquivalent_iff_exists_orderAddEquiv`: `ν ∼ ν'` iff `ν' = g ∘ ν` for some
  `g ∈ Aut(ℤⁿ_lex)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.ValCurr

open Matrix Finset
open scoped Matrix

variable {n : ℕ}

/-! ### Unitriangular matrices -/

/-- `G = I + N` with `N` strictly upper triangular (integral entries). -/
def IsUnitUpperTriangular (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, G i i = 1) ∧ G.IsUpperTriangular

namespace IsUnitUpperTriangular

variable {G H : Matrix (Fin n) (Fin n) ℤ}

theorem diag (hG : IsUnitUpperTriangular G) (i : Fin n) : G i i = 1 := hG.1 i

theorem lower (hG : IsUnitUpperTriangular G) {i j : Fin n} (hij : j < i) : G i j = 0 :=
  hG.2 hij

theorem one : IsUnitUpperTriangular (1 : Matrix (Fin n) (Fin n) ℤ) :=
  ⟨fun i => by simp, blockTriangular_one⟩

/-- The `(i, j)` entry of `M G` for `G` upper triangular only involves the indices `k ≤ j`. -/
theorem mul_diag (hG : IsUnitUpperTriangular G) (hH : IsUnitUpperTriangular H) (i : Fin n) :
    (G * H) i i = 1 := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [hG.diag, hH.diag, one_mul]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hG.lower hlt, zero_mul]
    · rw [hH.lower hgt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mul (hG : IsUnitUpperTriangular G) (hH : IsUnitUpperTriangular H) :
    IsUnitUpperTriangular (G * H) :=
  ⟨mul_diag hG hH, hG.2.mul hH.2⟩

theorem det_eq_one (hG : IsUnitUpperTriangular G) : G.det = 1 := by
  rw [det_of_isUpperTriangular hG.2]
  exact Finset.prod_eq_one fun i _ => hG.diag i

theorem isUnit_det (hG : IsUnitUpperTriangular G) : IsUnit G.det := by
  rw [hG.det_eq_one]; exact isUnit_one

theorem mul_inv (hG : IsUnitUpperTriangular G) : G * G⁻¹ = 1 :=
  mul_nonsing_inv G hG.isUnit_det

theorem inv_mul (hG : IsUnitUpperTriangular G) : G⁻¹ * G = 1 :=
  nonsing_inv_mul G hG.isUnit_det

theorem inv (hG : IsUnitUpperTriangular G) : IsUnitUpperTriangular G⁻¹ := by
  let : Invertible G := invertibleOfIsUnitDet G hG.isUnit_det
  have hT : (G⁻¹).IsUpperTriangular := blockTriangular_inv_of_blockTriangular hG.2
  refine ⟨fun i => ?_, hT⟩
  have h := congrFun (congrFun hG.inv_mul i) i
  rw [mul_apply, Finset.sum_eq_single i] at h
  · rwa [hG.diag, mul_one, one_apply_eq] at h
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hT hlt, zero_mul]
    · rw [hG.lower hgt, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ i) h'

end IsUnitUpperTriangular

/-! ### The lexicographic order and `x ↦ x G` -/

section Lex

variable {G : Matrix (Fin n) (Fin n) ℤ}

/-- The lexicographic order on `ℤⁿ` (`Lex (Fin n → ℤ)`), unfolded. -/
theorem toLex_lt_toLex_iff {x y : Fin n → ℤ} :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

/-- For `G` upper triangular, `(x G)_j` only depends on `x_k`, `k ≤ j`. -/
theorem vecMul_apply_eq_of_eq_le (hG : IsUnitUpperTriangular G) {x y : Fin n → ℤ} {j : Fin n}
    (h : ∀ k, k ≤ j → x k = y k) : (x ᵥ* G) j = (y ᵥ* G) j := by
  simp only [vecMul, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases le_or_gt k j with hkj | hjk
  · rw [h k hkj]
  · rw [hG.lower hjk, mul_zero, mul_zero]

/-- For `G = I + N` and `x_k = y_k` for `k < i`: `(y G)_i - (x G)_i = y_i - x_i`. -/
theorem vecMul_sub_apply_of_eq_lt (hG : IsUnitUpperTriangular G) {x y : Fin n → ℤ} {i : Fin n}
    (h : ∀ k, k < i → x k = y k) : (y ᵥ* G) i - (x ᵥ* G) i = y i - x i := by
  simp only [vecMul, dotProduct]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [hG.diag, mul_one, mul_one]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [h k hlt, sub_self]
    · rw [hG.lower hgt, mul_zero, mul_zero, sub_self]
  · intro h'; exact absurd (Finset.mem_univ i) h'

/-- `x ↦ x G` is strictly increasing for the lexicographic order when `G = I + N`. -/
theorem strictMono_vecMul (hG : IsUnitUpperTriangular G) :
    StrictMono fun x : Lex (Fin n → ℤ) => toLex (ofLex x ᵥ* G) := by
  intro x y hxy
  obtain ⟨i, hlt, hi⟩ := (toLex_lt_toLex_iff (x := ofLex x) (y := ofLex y)).mp hxy
  refine (toLex_lt_toLex_iff).mpr ⟨i, fun j hj => ?_, ?_⟩
  · exact vecMul_apply_eq_of_eq_le hG fun k hk => hlt k (lt_of_le_of_lt hk hj)
  · have := vecMul_sub_apply_of_eq_lt hG (x := ofLex x) (y := ofLex y) hlt
    linarith

/-- **Unitriangular matrices give automorphisms of `ℤⁿ_lex`**: `x ↦ x G` for `G = I + N`. -/
def unitriangularLexEquiv (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ) where
  toFun x := toLex (ofLex x ᵥ* G)
  invFun x := toLex (ofLex x ᵥ* G⁻¹)
  left_inv x := by
    simp only [ofLex_toLex, vecMul_vecMul, hG.mul_inv, vecMul_one, toLex_ofLex]
  right_inv x := by
    simp only [ofLex_toLex, vecMul_vecMul, hG.inv_mul, vecMul_one, toLex_ofLex]
  map_add' x y := by
    simp only [ofLex_add, add_vecMul, toLex_add]
  map_le_map_iff' {x y} := (strictMono_vecMul hG).le_iff_le

@[simp] theorem unitriangularLexEquiv_apply (hG : IsUnitUpperTriangular G)
    (x : Lex (Fin n → ℤ)) : unitriangularLexEquiv G hG x = toLex (ofLex x ᵥ* G) := rfl

/-! ### Every automorphism of `ℤⁿ_lex` is unitriangular -/

/-- The leading index of a nonzero vector. -/
private theorem exists_lead {x : Fin n → ℤ} (hx : x ≠ 0) :
    ∃ i, (∀ j, j < i → x j = 0) ∧ x i ≠ 0 := by
  have hne : (Finset.univ.filter fun i => x i ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hx (funext fun i => by simpa using h (Finset.mem_univ i))
  refine ⟨(Finset.univ.filter fun i => x i ≠ 0).min' hne, fun j hj => ?_,
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
  by_contra hxj
  exact absurd (Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩)) (not_le.mpr hj)

/-- `x` is a positive vector with leading index `i`. -/
private def PosLead (x : Fin n → ℤ) (i : Fin n) : Prop := (∀ j, j < i → x j = 0) ∧ 0 < x i

private theorem posLead_iff_pos {x : Fin n → ℤ} :
    (0 : Lex (Fin n → ℤ)) < toLex x ↔ ∃ i, PosLead x i := by
  change toLex (0 : Fin n → ℤ) < toLex x ↔ _
  rw [toLex_lt_toLex_iff]
  constructor
  · rintro ⟨i, hi, hpos⟩; exact ⟨i, fun j hj => (hi j hj).symm, hpos⟩
  · rintro ⟨i, hi, hpos⟩; exact ⟨i, fun j hj => (hi j hj).symm, hpos⟩

private theorem posLead_unique {x : Fin n → ℤ} {i i' : Fin n} (h : PosLead x i)
    (h' : PosLead x i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (h'.1 i hlt) h.2.ne'
  · exact heq
  · exact absurd (h.1 i' hgt) h'.2.ne'

/-- If the leading index of the positive vector `y` is at most that of the positive vector `z`,
then some multiple `N y` is not below `z`. -/
private theorem exists_not_nsmul_lt {y z : Fin n → ℤ} {i j : Fin n} (hy : PosLead y i)
    (hz : PosLead z j) (hij : i ≤ j) : ∃ N : ℕ, ¬ toLex (N • y) < toLex z := by
  have hzi : 0 ≤ z i := by
    rcases hij.lt_or_eq with hlt | heq
    · rw [hz.1 i hlt]
    · rw [heq]; exact hz.2.le
  refine ⟨(z i).toNat + 1, fun h => ?_⟩
  have hN : (((z i).toNat + 1 : ℕ) : ℤ) = z i + 1 := by
    push_cast; rw [Int.toNat_of_nonneg hzi]
  have hbig : z i < (((z i).toNat + 1 : ℕ) : ℤ) * y i := by
    rw [hN]; nlinarith [hy.2]
  rw [toLex_lt_toLex_iff] at h
  obtain ⟨k, hk, hlt⟩ := h
  simp only [Pi.smul_apply, nsmul_eq_mul] at hk hlt
  rcases lt_trichotomy k i with hki | hki | hki
  · rw [hy.1 k hki, hz.1 k (lt_of_lt_of_le hki hij), mul_zero] at hlt
    exact lt_irrefl 0 hlt
  · subst hki; linarith
  · have := hk i hki; linarith

/-- `y ≪ z` (`N y < z` for every `N`) between positive vectors iff the leading index of `y` is
larger than that of `z`. -/
private theorem forall_nsmul_lt_iff {y z : Fin n → ℤ} {i j : Fin n} (hy : PosLead y i)
    (hz : PosLead z j) :
    (∀ N : ℕ, toLex (N • y) < toLex z) ↔ j < i := by
  constructor
  · intro h
    by_contra hji
    obtain ⟨N, hN⟩ := exists_not_nsmul_lt hy hz (not_lt.mp hji)
    exact hN (h N)
  · intro hji N
    rw [toLex_lt_toLex_iff]
    refine ⟨j, fun k hk => ?_, ?_⟩
    · simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hy.1 k (hk.trans hji), hz.1 k hk, mul_zero]
    · simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hy.1 j hji, mul_zero]; exact hz.2


/-- The ordered additive automorphism `g` of `ℤⁿ_lex`, read on plain vectors. -/
private def autVec (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) (x : Fin n → ℤ) : Fin n → ℤ :=
  ofLex (g (toLex x))

private theorem autVec_nsmul (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) (N : ℕ)
    (x : Fin n → ℤ) : autVec g (N • x) = N • autVec g x := by
  unfold autVec
  change ofLex (g (N • toLex x)) = _
  rw [map_nsmul]
  rfl

private theorem autVec_lt_iff (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) {x y : Fin n → ℤ} :
    toLex (autVec g x) < toLex (autVec g y) ↔ toLex x < toLex y := by
  unfold autVec
  simp only [toLex_ofLex]
  exact map_lt_map_iff g

private theorem exists_posLead_autVec (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    {x : Fin n → ℤ} {i : Fin n} (hx : PosLead x i) : ∃ i', PosLead (autVec g x) i' := by
  have hpos : (0 : Lex (Fin n → ℤ)) < toLex x := posLead_iff_pos.mpr ⟨i, hx⟩
  have h0 : autVec g 0 = 0 := by
    unfold autVec
    rw [toLex_zero, map_zero, ofLex_zero]
  have : toLex (autVec g 0) < toLex (autVec g x) := (autVec_lt_iff g).mpr hpos
  rw [h0] at this
  exact posLead_iff_pos.mp this

/-- `g` preserves the strict order of leading indices of positive vectors. -/
private theorem posLead_lt_iff (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    {x y : Fin n → ℤ} {i j i' j' : Fin n} (hx : PosLead x i) (hy : PosLead y j)
    (hgx : PosLead (autVec g x) i') (hgy : PosLead (autVec g y) j') : j < i ↔ j' < i' := by
  rw [← forall_nsmul_lt_iff hx hy, ← forall_nsmul_lt_iff hgx hgy]
  refine forall_congr' fun N => ?_
  rw [← autVec_nsmul, autVec_lt_iff]

/-- `g` maps positive vectors with equal leading index to positive vectors with equal leading
index. -/
private theorem posLead_eq_of_eq (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    {x y : Fin n → ℤ} {i i' j' : Fin n} (hx : PosLead x i) (hy : PosLead y i)
    (hgx : PosLead (autVec g x) i') (hgy : PosLead (autVec g y) j') : i' = j' := by
  have h1 := (posLead_lt_iff g hx hy hgx hgy).not
  have h2 := (posLead_lt_iff g hy hx hgy hgx).not
  simp only [lt_irrefl, not_false_eq_true, true_iff] at h1 h2
  exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)

private theorem posLead_single (i : Fin n) : PosLead (Pi.single i (1 : ℤ)) i :=
  ⟨fun j hj => by simp [hj.ne], by simp⟩

/-- The leading index of `g(eᵢ)`. -/
private def leadMap (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) (i : Fin n) : Fin n :=
  (exists_posLead_autVec g (posLead_single i)).choose

private theorem posLead_leadMap (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) (i : Fin n) :
    PosLead (autVec g (Pi.single i 1)) (leadMap g i) :=
  (exists_posLead_autVec g (posLead_single i)).choose_spec

/-- `g x` has leading index `leadMap g i` when `x` has leading index `i`. -/
private theorem posLead_autVec_leadMap (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    {x : Fin n → ℤ} {i : Fin n} (hx : PosLead x i) : PosLead (autVec g x) (leadMap g i) := by
  obtain ⟨i', hi'⟩ := exists_posLead_autVec g hx
  have := posLead_eq_of_eq g hx (posLead_single i) hi' (posLead_leadMap g i)
  rwa [← this]

private theorem strictMono_leadMap (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) :
    StrictMono (leadMap g) := fun i j hij =>
  (posLead_lt_iff g (posLead_single j) (posLead_single i) (posLead_leadMap g j)
    (posLead_leadMap g i)).mp hij

/-- **`g` preserves leading indices.** -/
private theorem leadMap_eq (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) (i : Fin n) :
    leadMap g i = i := by
  have h1 : i ≤ leadMap g i := (strictMono_leadMap g).le_apply
  have h2 : leadMap g i ≤ leadMap g.symm (leadMap g i) := (strictMono_leadMap g.symm).le_apply
  have hback : autVec g.symm (autVec g (Pi.single i 1)) = Pi.single i 1 := by
    unfold autVec
    simp
  have h3 := posLead_autVec_leadMap g.symm (posLead_leadMap g i)
  rw [hback] at h3
  have h4 : leadMap g.symm (leadMap g i) = i := posLead_unique h3 (posLead_single i)
  exact le_antisymm (h2.trans h4.le) h1

private theorem posLead_autVec (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    {x : Fin n → ℤ} {i : Fin n} (hx : PosLead x i) : PosLead (autVec g x) i := by
  have := posLead_autVec_leadMap g hx
  rwa [leadMap_eq] at this

/-- The matrix whose rows are the images `g(eᵢ)` of the unit vectors. -/
def orderAddEquivMatrix (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ofLex (g (toLex (Pi.single i 1))) j

/-- `g(x) = x G` for the matrix of the images of the unit vectors (`g` is `ℤ`-linear). -/
theorem orderAddEquiv_apply_eq_vecMul (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ))
    (x : Fin n → ℤ) : ofLex (g (toLex x)) = x ᵥ* orderAddEquivMatrix g := by
  let φ : (Fin n → ℤ) →+ (Fin n → ℤ) :=
    { toFun := fun y => ofLex (g (toLex y))
      map_zero' := by simp
      map_add' := fun y z => by simp [toLex_add, map_add] }
  have hφ : ∀ y, φ y = ofLex (g (toLex y)) := fun _ => rfl
  conv_lhs => rw [← hφ, ← Finset.univ_sum_single x]
  rw [map_sum]
  funext j
  simp only [vecMul, dotProduct, Finset.sum_apply, orderAddEquivMatrix]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : Pi.single i (x i) = (x i) • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsingle, map_zsmul, hφ]
  rfl

/-- **Every ordered additive automorphism of `ℤⁿ_lex` is unitriangular**: its matrix is
`I + N` with `N` strictly upper triangular. -/
theorem isUnitUpperTriangular_orderAddEquivMatrix (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) :
    IsUnitUpperTriangular (orderAddEquivMatrix g) := by
  have hrow : ∀ i, PosLead (orderAddEquivMatrix g i) i := fun i =>
    posLead_autVec g (posLead_single i)
  have hlow : (orderAddEquivMatrix g).IsUpperTriangular := fun i j hij => (hrow i).1 j hij
  refine ⟨fun i => ?_, hlow⟩
  -- `y = g⁻¹(eᵢ)` has leading index `i` and `y G = eᵢ`
  set y := ofLex (g.symm (toLex (Pi.single i (1 : ℤ)))) with hy
  have hyl : PosLead y i := posLead_autVec g.symm (posLead_single i)
  have hyG : y ᵥ* orderAddEquivMatrix g = Pi.single i 1 := by
    rw [← orderAddEquiv_apply_eq_vecMul, hy]
    simp
  have hsum := congrFun hyG i
  simp only [vecMul, dotProduct, Pi.single_eq_same] at hsum
  rw [Finset.sum_eq_single i] at hsum
  · have hGpos : 0 < orderAddEquivMatrix g i i := (hrow i).2
    exact Int.eq_one_of_mul_eq_one_left hGpos.le hsum
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hyl.1 k hlt, zero_mul]
    · rw [hlow hgt, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ i) h'

/-- **`Aut(ℤⁿ_lex)` is the group of unitriangular matrices** (row-vector convention): every
ordered additive automorphism of `ℤⁿ_lex` is `x ↦ x G` for some `G = I + N`, and conversely
(`unitriangularLexEquiv`). -/
theorem exists_unitriangular_of_orderAddEquiv (g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ)) :
    ∃ (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G),
      g = unitriangularLexEquiv G hG := by
  refine ⟨orderAddEquivMatrix g, isUnitUpperTriangular_orderAddEquivMatrix g, ?_⟩
  ext x
  rw [unitriangularLexEquiv_apply, ← orderAddEquiv_apply_eq_vecMul, toLex_ofLex]
  rfl

end Lex


/-! ### Equivalence of `ℤⁿ`-valued valuations (footnote of `rmk:Abhyankar`) -/

section Equivalence

variable {α : Type*}

/-- **Footnote of `rmk:Abhyankar`**: two maps `ν, ν'` with values in `ℤⁿ` (row vectors) are
*equivalent* if `ν' = ν G` for a matrix `G = I + N`, `N` strictly upper triangular with integral
entries. -/
def LexEquivalent (ν ν' : α → Fin n → ℤ) : Prop :=
  ∃ G : Matrix (Fin n) (Fin n) ℤ, IsUnitUpperTriangular G ∧ ∀ a, ν' a = ν a ᵥ* G

theorem LexEquivalent.refl (ν : α → Fin n → ℤ) : LexEquivalent ν ν :=
  ⟨1, IsUnitUpperTriangular.one, fun _ => (vecMul_one _).symm⟩

theorem LexEquivalent.symm {ν ν' : α → Fin n → ℤ} (h : LexEquivalent ν ν') :
    LexEquivalent ν' ν := by
  obtain ⟨G, hG, hν⟩ := h
  refine ⟨G⁻¹, hG.inv, fun a => ?_⟩
  rw [hν, vecMul_vecMul, hG.mul_inv, vecMul_one]

theorem LexEquivalent.trans {ν ν' ν'' : α → Fin n → ℤ} (h : LexEquivalent ν ν')
    (h' : LexEquivalent ν' ν'') : LexEquivalent ν ν'' := by
  obtain ⟨G, hG, hν⟩ := h
  obtain ⟨H, hH, hν'⟩ := h'
  refine ⟨G * H, hG.mul hH, fun a => ?_⟩
  rw [hν', hν, vecMul_vecMul]

/-- The relation of the footnote is an equivalence relation. -/
theorem lexEquivalent_equivalence : Equivalence (LexEquivalent (α := α) (n := n)) :=
  ⟨LexEquivalent.refl, LexEquivalent.symm, LexEquivalent.trans⟩

/-- `ν ∼ ν'` iff `ν' = g ∘ ν` for an automorphism `g ∈ Aut(ℤⁿ_lex)`. -/
theorem lexEquivalent_iff_exists_orderAddEquiv {ν ν' : α → Fin n → ℤ} :
    LexEquivalent ν ν' ↔
      ∃ g : Lex (Fin n → ℤ) ≃+o Lex (Fin n → ℤ), ∀ a, ν' a = ofLex (g (toLex (ν a))) := by
  constructor
  · rintro ⟨G, hG, hν⟩
    exact ⟨unitriangularLexEquiv G hG, fun a => by simp [hν]⟩
  · rintro ⟨g, hg⟩
    exact ⟨orderAddEquivMatrix g, isUnitUpperTriangular_orderAddEquivMatrix g, fun a => by
      rw [hg, orderAddEquiv_apply_eq_vecMul]⟩

/-! #### Valuations with values in `ℤⁿ_lex ∪ {∞}` -/

variable {R : Type*} [Ring R]

/-- The additive map `ℤⁿ_lex ∪ {∞} → ℤⁿ_lex ∪ {∞}`, `x ↦ x G`, `∞ ↦ ∞`. -/
def lexWithTopHom (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    WithTop (Lex (Fin n → ℤ)) →+ WithTop (Lex (Fin n → ℤ)) :=
  (unitriangularLexEquiv G hG).toAddMonoidHom.withTopMap

theorem lexWithTopHom_coe (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G)
    (x : Lex (Fin n → ℤ)) :
    lexWithTopHom G hG (x : WithTop (Lex (Fin n → ℤ))) = ((toLex (ofLex x ᵥ* G) : Lex _) :
      WithTop (Lex (Fin n → ℤ))) := rfl

theorem lexWithTopHom_top (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    lexWithTopHom G hG ⊤ = ⊤ := rfl

theorem monotone_lexWithTopHom (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    Monotone (lexWithTopHom G hG) := by
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe y =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd hxy (by simp)
    | coe x =>
      rw [lexWithTopHom_coe, lexWithTopHom_coe, WithTop.coe_le_coe]
      exact (strictMono_vecMul hG).monotone (WithTop.coe_le_coe.mp hxy)

/-- `ν G`: the valuation `ν` followed by the automorphism `x ↦ x G` of `ℤⁿ_lex` (again a
valuation, with values in `ℤⁿ_lex ∪ {∞}`). -/
def lexMapValuation (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) :
    AddValuation R (WithTop (Lex (Fin n → ℤ))) :=
  v.map (lexWithTopHom G hG) (lexWithTopHom_top G hG) (monotone_lexWithTopHom G hG)

theorem lexMapValuation_apply (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) (r : R) :
    lexMapValuation G hG v r = lexWithTopHom G hG (v r) := rfl

theorem lexWithTopHom_congr {G G' : Matrix (Fin n) (Fin n) ℤ} (h : G = G')
    (hG : IsUnitUpperTriangular G) (hG' : IsUnitUpperTriangular G')
    (x : WithTop (Lex (Fin n → ℤ))) : lexWithTopHom G hG x = lexWithTopHom G' hG' x := by
  subst h; rfl

theorem lexWithTopHom_one (x : WithTop (Lex (Fin n → ℤ))) :
    lexWithTopHom 1 IsUnitUpperTriangular.one x = x := by
  induction x using WithTop.recTopCoe with
  | top => rfl
  | coe x => rw [lexWithTopHom_coe, vecMul_one, toLex_ofLex]

theorem lexWithTopHom_mul {G H : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (hH : IsUnitUpperTriangular H) (x : WithTop (Lex (Fin n → ℤ))) :
    lexWithTopHom H hH (lexWithTopHom G hG x) = lexWithTopHom (G * H) (hG.mul hH) x := by
  induction x using WithTop.recTopCoe with
  | top => rfl
  | coe x => rw [lexWithTopHom_coe, lexWithTopHom_coe, lexWithTopHom_coe, ofLex_toLex,
      vecMul_vecMul]

/-- **Footnote of `rmk:Abhyankar`, for valuations**: `ν ∼ ν'` iff `ν' = ν G` for some
`G = I + N`. -/
def ValuationsLexEquivalent (v v' : AddValuation R (WithTop (Lex (Fin n → ℤ)))) : Prop :=
  ∃ (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G), v' = lexMapValuation G hG v

theorem valuationsLexEquivalent_equivalence :
    Equivalence (ValuationsLexEquivalent (R := R) (n := n)) := by
  refine ⟨fun v => ⟨1, IsUnitUpperTriangular.one, ?_⟩, ?_, ?_⟩
  · ext r
    rw [lexMapValuation_apply, lexWithTopHom_one]
  · rintro v v' ⟨G, hG, rfl⟩
    refine ⟨G⁻¹, hG.inv, ?_⟩
    ext r
    rw [lexMapValuation_apply, lexMapValuation_apply, lexWithTopHom_mul,
      lexWithTopHom_congr hG.mul_inv _ IsUnitUpperTriangular.one, lexWithTopHom_one]
  · rintro v v' v'' ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
    refine ⟨G * H, hG.mul hH, ?_⟩
    ext r
    rw [lexMapValuation_apply, lexMapValuation_apply, lexMapValuation_apply, lexWithTopHom_mul]

end Equivalence

end SGPT.Okounkov.ValCurr
