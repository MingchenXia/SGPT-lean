import SGPT.Okounkov.ValCurrLexEquivalence
import SGPT.Okounkov.AlgebraicValuationCenter

/-!
# Actual prefix coarsenings and their scheme-theoretic centres

Equivalent full-rank flag valuations determine the same flag via the centres
of their coarsenings. This module proves the algebraic centre-invariance step
using actual `AddValuation`s and actual proper-scheme centres. It assumes no
common resolution, common flag, or equality of current values.

It does not construct a flag presentation for an arbitrary valuation, or
identify the geometric members of a flag with these centres. Those remaining
steps are necessary for the whole source `rmk:valcurr`.

Blueprint: `source-valuation-coarsening-centres.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.ValCurr

open Matrix Finset AlgebraicGeometry CategoryTheory
open scoped Matrix

variable {n k : ℕ}

/-- The actual first-coordinate quotient homomorphism of lexicographic groups. -/
def prefixHom (hk : k ≤ n) : Lex (Fin n → ℤ) →+ Lex (Fin k → ℤ) where
  toFun x := toLex fun i => ofLex x (Fin.castLE hk i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem prefixHom_apply (hk : k ≤ n) (x : Lex (Fin n → ℤ)) :
    prefixHom hk x = toLex (fun i => ofLex x (Fin.castLE hk i)) := rfl

/-- A strict comparison of prefixes is already a strict comparison of the
full vectors: every coordinate before the first difference is retained. -/
theorem lt_of_prefixHom_lt (hk : k ≤ n) {x y : Lex (Fin n → ℤ)}
    (h : prefixHom hk x < prefixHom hk y) : x < y := by
  obtain ⟨i, hbefore, hi⟩ := toLex_lt_toLex_iff.mp h
  change toLex (ofLex x) < toLex (ofLex y)
  apply toLex_lt_toLex_iff.mpr
  refine ⟨Fin.castLE hk i, ?_, hi⟩
  intro j hj
  have hjk : j.val < k := lt_trans hj i.isLt
  exact hbefore ⟨j.val, hjk⟩ hj

theorem monotone_prefixHom (hk : k ≤ n) : Monotone (prefixHom hk) := by
  intro x y hxy
  by_contra h
  exact not_lt_of_ge hxy (lt_of_prefixHom_lt hk (lt_of_not_ge h))

/-- Extend the desired prefix by zero in the remaining coordinates. -/
theorem prefixHom_surjective (hk : k ≤ n) : Function.Surjective (prefixHom hk) := by
  intro z
  let x : Fin n → ℤ := fun i => if h : i.val < k then ofLex z ⟨i.val, h⟩ else 0
  refine ⟨toLex x, ?_⟩
  apply ofLex.injective
  funext i
  change (if h : i.val < k then ofLex z ⟨i.val, h⟩ else 0) = ofLex z i
  rw [dif_pos i.isLt]

/-- Prefix projection with infinity retained literally. -/
def prefixWithTopHom (hk : k ≤ n) :
    WithTop (Lex (Fin n → ℤ)) →+ WithTop (Lex (Fin k → ℤ)) :=
  (prefixHom hk).withTopMap

theorem prefixWithTopHom_surjective (hk : k ≤ n) :
    Function.Surjective (prefixWithTopHom hk) := by
  intro z
  induction z using WithTop.recTopCoe with
  | top => exact ⟨⊤, rfl⟩
  | coe z =>
    obtain ⟨x, hx⟩ := prefixHom_surjective hk z
    refine ⟨(x : WithTop (Lex (Fin n → ℤ))), ?_⟩
    change (prefixHom hk x : WithTop (Lex (Fin k → ℤ))) = (z : WithTop (Lex (Fin k → ℤ)))
    rw [hx]

theorem monotone_prefixWithTopHom (hk : k ≤ n) : Monotone (prefixWithTopHom hk) := by
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe y =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd hxy (by simp)
    | coe x =>
      change (prefixHom hk x : WithTop (Lex (Fin k → ℤ))) ≤
        (prefixHom hk y : WithTop (Lex (Fin k → ℤ)))
      exact WithTop.coe_le_coe.mpr (monotone_prefixHom hk (WithTop.coe_le_coe.mp hxy))

/-- The coarsening is manufactured by the monotone quotient, including at zero. -/
def prefixValuation {R : Type*} [Ring R] (hk : k ≤ n)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) :
    AddValuation R (WithTop (Lex (Fin k → ℤ))) :=
  v.map (prefixWithTopHom hk) rfl (monotone_prefixWithTopHom hk)

/-- Full rank is retained at every prefix length; no rank certificate for the
coarsening is supplied as a hypothesis. -/
theorem prefixValuation_surjective {R : Type*} [Ring R] (hk : k ≤ n)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v) :
    Function.Surjective (prefixValuation hk v) :=
  (prefixWithTopHom_surjective hk).comp hv

private theorem prefix_pos_vecMul_of_pos (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (x : Fin n → ℤ) (hpos : 0 < prefixHom hk (toLex x)) :
    0 < prefixHom hk (toLex (x ᵥ* G)) := by
  change toLex (0 : Fin k → ℤ) < toLex (fun i => x (Fin.castLE hk i)) at hpos
  obtain ⟨i, hbefore, hi⟩ := toLex_lt_toLex_iff.mp hpos
  have hbefore' : ∀ j : Fin n, j < Fin.castLE hk i → x j = 0 := by
    intro j hj
    have hjk : j.val < k := lt_trans hj i.isLt
    exact (hbefore ⟨j.val, hjk⟩ hj).symm
  change toLex (0 : Fin k → ℤ) < toLex (fun j => (x ᵥ* G) (Fin.castLE hk j))
  apply toLex_lt_toLex_iff.mpr
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    have hzero := vecMul_apply_eq_of_eq_le hG (x := x) (y := 0)
      (j := Fin.castLE hk j) (fun a ha => hbefore' a (lt_of_le_of_lt ha hj))
    simpa only [zero_vecMul, Pi.zero_apply] using hzero.symm
  · have hlead := vecMul_sub_apply_of_eq_lt hG (x := 0) (y := x)
      (i := Fin.castLE hk i) (fun j hj => (hbefore' j hj).symm)
    simp only [zero_vecMul, Pi.zero_apply, sub_zero] at hlead
    rw [hlead]
    exact hi

/-- Every coarsening retains its positive cone under the source's equivalence. -/
theorem prefix_pos_vecMul_iff (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G) (x : Fin n → ℤ) :
    0 < prefixHom hk (toLex (x ᵥ* G)) ↔ 0 < prefixHom hk (toLex x) := by
  constructor
  · intro h
    have hinv := prefix_pos_vecMul_of_pos hk hG.inv (x ᵥ* G) h
    simpa only [vecMul_vecMul, hG.mul_inv, vecMul_one] using hinv
  · exact prefix_pos_vecMul_of_pos hk hG x

theorem prefix_nonneg_vecMul_iff (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G) (x : Fin n → ℤ) :
    0 ≤ prefixHom hk (toLex (x ᵥ* G)) ↔ 0 ≤ prefixHom hk (toLex x) := by
  have hneg : prefixHom hk (toLex (x ᵥ* G)) < 0 ↔ prefixHom hk (toLex x) < 0 := by
    simpa only [neg_vecMul, toLex_neg, map_neg, neg_pos] using
      prefix_pos_vecMul_iff hk hG (-x)
  constructor
  · intro h
    by_contra hx
    exact not_lt_of_ge h (hneg.mpr (lt_of_not_ge hx))
  · intro h
    by_contra hx
    exact not_lt_of_ge h (hneg.mp (lt_of_not_ge hx))

theorem prefixWithTopHom_nonneg_lexMap_iff (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (x : WithTop (Lex (Fin n → ℤ))) :
    0 ≤ prefixWithTopHom hk (lexWithTopHom G hG x) ↔ 0 ≤ prefixWithTopHom hk x := by
  induction x using WithTop.recTopCoe with
  | top => rfl
  | coe x =>
    change (0 : WithTop (Lex (Fin k → ℤ))) ≤
        (prefixHom hk (toLex (ofLex x ᵥ* G)) : WithTop (Lex (Fin k → ℤ))) ↔
      0 ≤ (prefixHom hk x : WithTop (Lex (Fin k → ℤ)))
    exact_mod_cast prefix_nonneg_vecMul_iff hk hG (ofLex x)

theorem prefixWithTopHom_pos_lexMap_iff (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (x : WithTop (Lex (Fin n → ℤ))) :
    0 < prefixWithTopHom hk (lexWithTopHom G hG x) ↔ 0 < prefixWithTopHom hk x := by
  induction x using WithTop.recTopCoe with
  | top => rfl
  | coe x =>
    change (0 : WithTop (Lex (Fin k → ℤ))) <
        (prefixHom hk (toLex (ofLex x ᵥ* G)) : WithTop (Lex (Fin k → ℤ))) ↔
      0 < (prefixHom hk x : WithTop (Lex (Fin k → ℤ)))
    exact_mod_cast prefix_pos_vecMul_iff hk hG (ofLex x)

theorem prefixValuation_nonneg_lexMap_iff {R : Type*} [Ring R] (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) (r : R) :
    0 ≤ prefixValuation hk (lexMapValuation G hG v) r ↔ 0 ≤ prefixValuation hk v r :=
  prefixWithTopHom_nonneg_lexMap_iff hk hG (v r)

theorem prefixValuation_pos_lexMap_iff {R : Type*} [Ring R] (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) (r : R) :
    0 < prefixValuation hk (lexMapValuation G hG v) r ↔ 0 < prefixValuation hk v r :=
  prefixWithTopHom_pos_lexMap_iff hk hG (v r)

section SchemeCentres

variable {X : Scheme.{0}} [IsIntegral X]
variable {v v' : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))}

/-- Actual coarsened valuation rings are equal, not merely isomorphic. -/
theorem valuationRing_prefix_eq_of_lexEquivalent (hk : k ≤ n)
    (h : ValuationsLexEquivalent v v') :
    AlgebraicValuation.valuationRing (prefixValuation hk v) =
      AlgebraicValuation.valuationRing (prefixValuation hk v') := by
  obtain ⟨G, hG, rfl⟩ := h
  ext r
  change 0 ≤ prefixValuation hk v r ↔ 0 ≤ prefixValuation hk (lexMapValuation G hG v) r
  exact (prefixValuation_nonneg_lexMap_iff hk hG v r).symm

/-- Every actual scheme point satisfies the same centre conditions for the
two prefix coarsenings, because both stalk signs are preserved. -/
theorem isValuationCenter_prefix_iff_of_lexEquivalent (hk : k ≤ n)
    (h : ValuationsLexEquivalent v v') (x : X) :
    AlgebraicValuation.IsValuationCenter (prefixValuation hk v) x ↔
      AlgebraicValuation.IsValuationCenter (prefixValuation hk v') x := by
  obtain ⟨G, hG, rfl⟩ := h
  constructor
  · intro hx
    exact ⟨fun r => (prefixValuation_nonneg_lexMap_iff hk hG v _).mpr (hx.1 r),
      fun r hr => (prefixValuation_pos_lexMap_iff hk hG v _).mpr (hx.2 r hr)⟩
  · intro hx
    exact ⟨fun r => (prefixValuation_nonneg_lexMap_iff hk hG v _).mp (hx.1 r),
      fun r hr => (prefixValuation_pos_lexMap_iff hk hG v _).mp (hx.2 r hr)⟩

/-- Properness manufactures each coarsened centre and separatedness identifies
them. No point, common model, or flag equality is supplied as a certificate. -/
theorem valuationCenter_prefix_eq_of_lexEquivalent
    (f : X ⟶ Spec (.of ℂ)) [IsProper f] (hk : k ≤ n)
    (h : ValuationsLexEquivalent v v') :
    AlgebraicValuation.valuationCenter f (prefixValuation hk v) =
      AlgebraicValuation.valuationCenter f (prefixValuation hk v') := by
  have hc := AlgebraicValuation.isValuationCenter_valuationCenter f (prefixValuation hk v)
  have hc' := (isValuationCenter_prefix_iff_of_lexEquivalent hk h _).mp hc
  exact hc'.unique f
    (AlgebraicValuation.isValuationCenter_valuationCenter f (prefixValuation hk v'))

end SchemeCentres

end SGPT.Okounkov.ValCurr
