import SGPT.Okounkov.FlagValuationGenericCenters
import SGPT.Okounkov.ValuationCoarseningCenters
import SGPT.Okounkov.AlgebraicValuationSections

/-!
# `rmk:Abhyankar`: equivalent, but not necessarily equal

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Thm 2.9] shows that it is equivalent to, **but not necessarily equal to**, a valuation
induced by an admissible flag on a modification of `X`.*

This file proves the "not necessarily equal" clause in an abstract form.

Every valuation `μ` of `ℂ(X)` induced by a flag (on `X` or on any modification `π : X' → X`) has
the following property: at the image `c ∈ X` of the flag point, `μ` is **coordinatewise**
nonnegative on the local ring `𝒪_{X,c}`: for a function `g` regular at `c`, the pull-back `π^*g`
is regular at the flag point, and all the successive orders of vanishing `ν_i ≥ 0` defining
`μ(g) = (ν_1, …, ν_n)` are nonnegative (`IsCoordNonnegAt`). Equivalent valuations
`ν' = ν G`, `G = I + N`, only have the same *lexicographic* sign on `𝒪_{X,c}`.

* `exists_lexEquivalent_forall_not_isCoordNonnegAt`: on an integral scheme `X` proper over `ℂ`,
  for every surjective valuation `ν : ℂ(X)^× → ℤⁿ`, `n ≥ 2`, whose centre is a closed point,
  there is an elementary shear `G = I - M E₁₂` such that `ν G` (equivalent to `ν`, again surjective)
  is coordinatewise nonnegative on **no** local ring `𝒪_{X,c}`; hence `ν G` is not equal to any
  valuation which is coordinatewise nonnegative at some point
  (`exists_lexEquivalent_forall_ne_of_isCoordNonnegAt`).

The proof: write `e₁ = ν(a) - ν(b)` with `a, b ∈ 𝒪_{X,z}`, `z` the centre; then `ν(a)₁ ≥ 1`.
Choose `M > |ν(a)₂|`; then `(ν(a) G)₂ = ν(a)₂ - M ν(a)₁ < 0`. If `ν G` were coordinatewise
nonnegative on some `𝒪_{X,c}`, it would be lexicographically nonnegative there, so its centre `z`
(the centre of `ν G` is that of `ν`) would specialize to `c`; `z` being closed, `c = z`, which
contradicts `a ∈ 𝒪_{X,z}`.

In dimension `n ≤ 1` equivalence is equality (`eq_of_valuationsLexEquivalent_of_le_one`), so the
restriction `n ≥ 2` is sharp.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry Topology Matrix
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open scoped Matrix

/-! ### Elementary shears -/

section Shear

variable {n : ℕ}

/-- The elementary shear `I - M E_{ij}`. -/
def shearMatrix (i j : Fin n) (M : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  1 - Matrix.single i j M

/-- For `i < j` the shear `I - M E_{ij}` is unitriangular, i.e. `x ↦ x G` is an automorphism of
`ℤⁿ_lex`. -/
theorem isUnitUpperTriangular_shearMatrix {i j : Fin n} (hij : i < j) (M : ℤ) :
    IsUnitUpperTriangular (shearMatrix i j M) := by
  refine ⟨fun k => ?_, fun a b hab => ?_⟩
  · have hne : ¬(i = k ∧ j = k) := fun h => hij.ne (h.1.trans h.2.symm)
    simp only [shearMatrix, Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.single_apply_of_ne _ _ _ _ _ hne, sub_zero]
  · have hba : b < a := hab
    have hne : ¬(i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hba
    simp only [shearMatrix, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hba),
      Matrix.single_apply_of_ne _ _ _ _ _ hne, sub_zero]

/-- The `j`-th coordinate of `x (I - M E_{ij})` is `x_j - M x_i`. -/
theorem vecMul_shearMatrix_apply (x : Fin n → ℤ) (i j : Fin n) (M : ℤ) :
    (x ᵥ* shearMatrix i j M) j = x j - M * x i := by
  rw [shearMatrix, Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]
  congr 1
  simp only [Matrix.vecMul, dotProduct, Matrix.single_apply, and_true]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_comm]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- In dimension `n ≤ 1` the only unitriangular matrix is the identity. -/
theorem eq_one_of_isUnitUpperTriangular_of_le_one {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : IsUnitUpperTriangular G) (hn : n ≤ 1) : G = 1 := by
  ext i j
  have hij : i = j := Fin.ext (by omega)
  subst hij
  rw [hG.diag, Matrix.one_apply_eq]

/-- **Equivalence is equality in dimension `≤ 1`**: there `Aut(ℤⁿ_lex)` is trivial. -/
theorem eq_of_valuationsLexEquivalent_of_le_one {R : Type*} [Ring R]
    {v v' : AddValuation R (WithTop (Lex (Fin n → ℤ)))} (hn : n ≤ 1)
    (h : ValuationsLexEquivalent v v') : v = v' := by
  obtain ⟨G, hG, rfl⟩ := h
  ext r
  rw [lexMapValuation_apply, lexWithTopHom_congr (eq_one_of_isUnitUpperTriangular_of_le_one hG hn) hG
    IsUnitUpperTriangular.one, lexWithTopHom_one]

/-- `x ↦ x G` is surjective on `ℤⁿ_lex ∪ {∞}`. -/
theorem lexWithTopHom_surjective (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    Function.Surjective (lexWithTopHom G hG) := by
  intro y
  induction y using WithTop.recTopCoe with
  | top => exact ⟨⊤, rfl⟩
  | coe y =>
    refine ⟨((toLex (ofLex y ᵥ* G⁻¹) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))), ?_⟩
    rw [lexWithTopHom_coe, ofLex_toLex, Matrix.vecMul_vecMul, hG.inv_mul, Matrix.vecMul_one,
      toLex_ofLex]

/-- An equivalent valuation `ν G` of a surjective valuation is surjective (it has the same value
group `ℤⁿ`, hence the same maximal rational rank). -/
theorem lexMapValuation_surjective {R : Type*} [Ring R]
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G)
    {v : AddValuation R (WithTop (Lex (Fin n → ℤ)))} (hv : Function.Surjective v) :
    Function.Surjective (lexMapValuation G hG v) :=
  (lexWithTopHom_surjective G hG).comp hv

end Shear

/-! ### Coordinatewise nonnegativity -/

section Abstract

variable {X : Scheme.{0}} [IsIntegral X] {n : ℕ}

/-- `v` is **coordinatewise** nonnegative on the local ring `𝒪_{X,c}`: every function `g` regular
at `c` has a value `v(g) ∈ ℤⁿ` all of whose coordinates are `≥ 0` (or `v(g) = ∞`). Every flag
valuation `ν_{Y•}`, read on `X` through a modification `π`, has this property at `c = π(Y_n)`:
its coordinates are orders of vanishing of regular functions. -/
def IsCoordNonnegAt (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X) :
    Prop :=
  ∀ (g : X.presheaf.stalk c) (w : Lex (Fin n → ℤ)),
    v (algebraMap (X.presheaf.stalk c) X.functionField g) = (w : WithTop (Lex (Fin n → ℤ))) →
      ∀ i, 0 ≤ ofLex w i

/-- Coordinatewise nonnegativity implies (lexicographic) nonnegativity. -/
theorem IsCoordNonnegAt.isNonnegAt {v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))}
    {c : X} (h : IsCoordNonnegAt v c) : IsNonnegAt v c := by
  intro g
  by_cases htop : v (algebraMap (X.presheaf.stalk c) X.functionField g) = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hw]
  apply WithTop.coe_le_coe.mpr
  have hc := h g w hw.symm
  have h0 : (0 : Lex (Fin n → ℤ)) = toLex (0 : Fin n → ℤ) := rfl
  rw [h0, ← toLex_ofLex w]
  exact Pi.toLex_monotone (fun i => hc i)

private theorem prefixValuation_refl_eq {R : Type*} [Ring R]
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) :
    prefixValuation (Nat.le_refl n) v = v := by
  ext r
  change prefixWithTopHom (Nat.le_refl n) (v r) = v r
  induction v r using WithTop.recTopCoe with
  | top => rfl
  | coe x =>
    change (prefixHom (Nat.le_refl n) x : WithTop (Lex (Fin n → ℤ))) =
      (x : WithTop (Lex (Fin n → ℤ)))
    apply congrArg (fun z : Lex (Fin n → ℤ) => (z : WithTop (Lex (Fin n → ℤ))))
    apply ofLex.injective
    funext i
    rfl

/-- Equivalent valuations have the same centres. -/
theorem isValuationCenter_lexMapValuation_iff
    {v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))}
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) (c : X) :
    IsValuationCenter (lexMapValuation G hG v) c ↔ IsValuationCenter v c := by
  have h := isValuationCenter_prefix_iff_of_lexEquivalent (Nat.le_refl n)
    (⟨G, hG, rfl⟩ : ValuationsLexEquivalent v (lexMapValuation G hG v)) c
  rw [prefixValuation_refl_eq, prefixValuation_refl_eq] at h
  exact h.symm

variable (f : X ⟶ Spec (.of ℂ)) [IsProper f]

/-- Equivalent valuations have the same centre. -/
theorem valuationCenter_lexMapValuation
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    valuationCenter f (lexMapValuation G hG v) = valuationCenter f v := by
  have hc := (isValuationCenter_lexMapValuation_iff G hG _).mpr
    (isValuationCenter_valuationCenter f v)
  exact ((isValuationCenter_iff_eq f _ _).mp hc).symm

/-- A valuation which is (lexicographically) nonnegative on the local ring at a point `c` has its
centre equal to `c` as soon as its centre is a closed point. -/
theorem eq_valuationCenter_of_isNonnegAt
    {v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))}
    (hcl : IsClosed ({valuationCenter f v} : Set X)) {c : X} (hc : IsNonnegAt v c) :
    c = valuationCenter f v := by
  have hsp := valuationCenter_specializes_of_stalk_nonneg f v c hc
  have hmem : c ∈ closure ({valuationCenter f v} : Set X) := specializes_iff_mem_closure.mp hsp
  rw [hcl.closure_eq] at hmem
  exact hmem

/-- From a surjective valuation with centre `z`: an element `a ∈ 𝒪_{X,z}` whose value has first
coordinate `≥ 1`. -/
theorem exists_stalk_first_coordinate_pos {m : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) :
    ∃ (a : X.presheaf.stalk (valuationCenter f v)) (w : Lex (Fin (m + 1) → ℤ)),
      v (algebraMap _ X.functionField a) = (w : WithTop (Lex (Fin (m + 1) → ℤ))) ∧
        1 ≤ ofLex w 0 := by
  classical
  have hz := isValuationCenter_valuationCenter f v
  obtain ⟨q, hq⟩ := hv ((toLex (Pi.single (0 : Fin (m + 1)) (1 : ℤ)) : Lex (Fin (m + 1) → ℤ)) :
    WithTop (Lex (Fin (m + 1) → ℤ)))
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := X.presheaf.stalk (valuationCenter f v)) q
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨wb, hwb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hb0)
  have hwb0 : (0 : Lex (Fin (m + 1) → ℤ)) ≤ wb := by
    have := hz.1 b
    rw [← hwb] at this
    exact WithTop.coe_le_coe.mp this
  have hsplit : algebraMap _ X.functionField a =
      (algebraMap _ X.functionField a / algebraMap _ X.functionField b) *
        algebraMap _ X.functionField b := by
    rw [div_mul_cancel₀ _ hb0]
  refine ⟨a, toLex (Pi.single (0 : Fin (m + 1)) (1 : ℤ)) + wb, ?_, ?_⟩
  · rw [hsplit, v.map_mul, hq, ← hwb]
    rfl
  · have hfirst : 0 ≤ ofLex wb 0 := by
      rcases eq_or_lt_of_le hwb0 with heq | hlt
      · rw [← heq]
        rfl
      · obtain ⟨i, hbefore, hi⟩ := (toLex_lt_toLex_iff (x := (0 : Fin (m + 1) → ℤ))
          (y := ofLex wb)).mp hlt
        by_cases hi0 : i = 0
        · subst hi0
          exact le_of_lt hi
        · have h0i : (0 : Fin (m + 1)) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi0)
          rw [← hbefore 0 h0i]
          rfl
    change 1 ≤ (Pi.single (0 : Fin (m + 1)) (1 : ℤ) : Fin (m + 1) → ℤ) 0 + ofLex wb 0
    rw [Pi.single_eq_same]
    omega

/-- **`rmk:Abhyankar`, "not necessarily equal" (abstract form).** Let `X` be integral and proper
over `ℂ`, `n ≥ 2`, and `ν : ℂ(X)^× → ℤⁿ` a surjective valuation (value group `ℤⁿ_lex`, rational
rank `n`) whose centre is a closed point. Then there is `G = I + N` (an elementary shear) such
that the equivalent valuation `ν G` is coordinatewise nonnegative on **no** local ring `𝒪_{X,c}`.
-/
theorem exists_lexEquivalent_forall_not_isCoordNonnegAt {m : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ))))
    (hv : Function.Surjective v) (hcl : IsClosed ({valuationCenter f v} : Set X)) :
    ∃ (G : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ) (hG : IsUnitUpperTriangular G),
      ∀ c : X, ¬IsCoordNonnegAt (lexMapValuation G hG v) c := by
  obtain ⟨a, w, hw, hw0⟩ := exists_stalk_first_coordinate_pos f v hv
  have h01 : (0 : Fin (m + 2)) < 1 := Fin.zero_lt_one
  let M : ℤ := |ofLex w 1| + 1
  have hG := isUnitUpperTriangular_shearMatrix h01 M
  refine ⟨shearMatrix 0 1 M, hG, fun c hc => ?_⟩
  have hcen := valuationCenter_lexMapValuation f v (shearMatrix 0 1 M) hG
  have hcz : c = valuationCenter f v := by
    have h := eq_valuationCenter_of_isNonnegAt f (v := lexMapValuation _ hG v)
      (by rw [hcen]; exact hcl) hc.isNonnegAt
    rw [h, hcen]
  subst hcz
  have hval : lexMapValuation (shearMatrix 0 1 M) hG v
      (algebraMap _ X.functionField a) =
      ((toLex (ofLex w ᵥ* shearMatrix 0 1 M) : Lex (Fin (m + 2) → ℤ)) :
        WithTop (Lex (Fin (m + 2) → ℤ))) := by
    rw [lexMapValuation_apply, hw, lexWithTopHom_coe]
  have hneg := hc a _ hval 1
  rw [ofLex_toLex, vecMul_shearMatrix_apply] at hneg
  have hM : M * 1 ≤ M * ofLex w 0 :=
    mul_le_mul_of_nonneg_left hw0 (by positivity)
  have habs := le_abs_self (ofLex w 1)
  linarith

/-- Consequently `ν G` is different from every valuation which is coordinatewise nonnegative at
some point of `X` — in particular from every valuation induced by a flag on `X` or on a
modification of `X`. -/
theorem exists_lexEquivalent_forall_ne_of_isCoordNonnegAt {m : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ))))
    (hv : Function.Surjective v) (hcl : IsClosed ({valuationCenter f v} : Set X)) :
    ∃ v' : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ))),
      ValuationsLexEquivalent v v' ∧ Function.Surjective v' ∧
        ∀ (μ : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ)))) (c : X),
          IsCoordNonnegAt μ c → v' ≠ μ := by
  obtain ⟨G, hG, hnot⟩ := exists_lexEquivalent_forall_not_isCoordNonnegAt f v hv hcl
  refine ⟨lexMapValuation G hG v, ⟨G, hG, rfl⟩, lexMapValuation_surjective G hG hv, ?_⟩
  rintro μ c hμ rfl
  exact hnot c hμ

end Abstract

end SGPT.Okounkov.OF2
