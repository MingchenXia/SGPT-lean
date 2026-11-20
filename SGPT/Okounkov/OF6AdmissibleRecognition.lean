import SGPT.Okounkov.OF6FlagRecognition
import SGPT.Okounkov.OF5AdmissibleFlagValuation

/-!
# Valuations equivalent to the valuation of an admissible flag

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`:

*Conversely, maximal-rank valuations of `ℂ(X)` are closely related to flag valuations. More
precisely, if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`,
then [CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a
valuation induced by an admissible flag on a modification of `X`.*

with the footnote: *`ν, ν'` with values in `ℤⁿ` are equivalent if `ν' = ν G` for a matrix
`G = I + N`, `N` strictly upper triangular with integral entries.*

For an admissible flag `Y•` (`def:admfl`, `SGPT.Okounkov.IsAdmissibleFlag`) on an integral scheme
`X` smooth of relative dimension `n` over `ℂ`, with its valuation `ν_{Y•}` (lane OF5,
`SGPT.Okounkov.OF5.admissibleFlagValuation`, the successive orders along local defining equations
`t₁, …, tₙ` of `Yᵢ` in `Yᵢ₋₁` at the point `Yₙ`), this file decides exactly which valuations of
`ℂ(X)` are equivalent to `ν_{Y•}`, and with which matrix:

* `eq_lexMap_admissibleFlagValuation_iff`: for `G = I + N`,
  `v = ν_{Y•} G ⟺ v ≥ 0 on 𝒪_{X,Yₙ} and v(tᵢ) = Gᵢ` (the `i`-th row of `G`) for every `i`;
* `lexEquivalent_admissibleFlagValuation_iff`: `v ∼ ν_{Y•}` iff `v` is nonnegative on
  `𝒪_{X,Yₙ}` (i.e. centred at the point `Yₙ`) and the integer matrix `(v(tᵢ))ᵢ` of the values of
  the local equations is unit upper triangular; the matrix `G` is then this value matrix
  (`eq_lexMap_valueMatrix_of_lexEquivalent`);
* `lexMap_admissibleFlagValuation_eq_iff`: `ν_{Y•} G = ν_{Y•}` iff `G = I` — every `G ≠ I` gives
  a valuation equivalent but not equal to `ν_{Y•}` (the *not necessarily equal* of the remark);
* `isValuationCenter_of_lexEquivalent`: every valuation equivalent to `ν_{Y•}` is centred at `Yₙ`.

This is the last step of the proof of [CFKLRS17, Thm 2.9]: once a model `X'` of `ℂ(X)` and an
admissible flag `Y•` on it are found such that `ν` is centred at `Yₙ` and the values of the local
equations form a unitriangular matrix, `ν` is equivalent to `ν_{Y•}`. The existence of such a model
(local uniformization of `ν`) is not proved here.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open AlgebraicGeometry CategoryTheory IsLocalRing SGPT.Okounkov.OF5 SGPT.Okounkov.ValCurr

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {Y : Fin (n + 1) → Set X} (hY : IsAdmissibleFlag f n Y)

/-- A valuation nonnegative on the local ring `𝒪_{X,x}` vanishes on its units. -/
theorem val_eq_zero_of_isUnit {x : X} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a : X.presheaf.stalk x, 0 ≤ v (algebraMap _ X.functionField a))
    {a : X.presheaf.stalk x} (ha : IsUnit a) : v (algebraMap _ X.functionField a) = 0 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  refine eq_zero_of_add_eq_zero (hnonneg a) (hnonneg b) ?_
  rw [← v.map_mul, ← map_mul, hb, map_one, v.map_one]

/-- **Equivalence criterion for admissible flags**: for local defining equations
`C.T 0, …, C.T (n-1)` (`t₁, …, tₙ`) of the members of `Y•` at `Yₙ` and `G = I + N`,
`v = ν_{Y•} G` iff `v` is nonnegative on `𝒪_{X,Yₙ}` and `v(tᵢ)` is the `i`-th row of `G`. -/
theorem eq_lexMap_admissibleFlagValuation_iff
    (C : OF5.LocalEquationChain (X.presheaf.stalk hY.point) n) (hC : C.P = admissibleIdeal hY)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    v = lexMapValuation G hG (admissibleFlagValuation hY) ↔
      (∀ a : X.presheaf.stalk hY.point, 0 ≤ v (algebraMap _ X.functionField a)) ∧
      ∀ (i : ℕ) (hi : i < n),
        v (algebraMap _ X.functionField (C.T i)) = vecValue (G ⟨i, hi⟩) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have h0 : C.P 0 = ⊥ := by rw [hC]; exact admissibleIdeal_zero hY
  rw [← fractionValuation_eq_admissibleFlagValuation hY C hC,
    LocalEquationChain.eq_lexMap_fractionValuation_iff C X.functionField h0 v G hG]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun a ha => ?_, h.2⟩⟩
  refine val_eq_zero_of_isUnit v h.1 ?_
  by_contra hu
  apply ha
  rw [hC, admissibleIdeal_last]
  exact (mem_maximalIdeal a).mpr hu

/-- **Which valuations are equivalent to `ν_{Y•}`**: `v ∼ ν_{Y•}` iff `v ≥ 0` on `𝒪_{X,Yₙ}` and
the matrix `(v(tᵢ))ᵢ` of the values of local defining equations is unit upper triangular. -/
theorem lexEquivalent_admissibleFlagValuation_iff
    (C : OF5.LocalEquationChain (X.presheaf.stalk hY.point) n) (hC : C.P = admissibleIdeal hY)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) :
    ValuationsLexEquivalent (admissibleFlagValuation hY) v ↔
      (∀ a : X.presheaf.stalk hY.point, 0 ≤ v (algebraMap _ X.functionField a)) ∧
      IsUnitUpperTriangular (LocalEquationChain.valueMatrix C X.functionField v) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  constructor
  · rintro ⟨G, hG, hv⟩
    obtain ⟨h1, h3⟩ := (eq_lexMap_admissibleFlagValuation_iff hY C hC v G hG).mp hv
    refine ⟨h1, ?_⟩
    have hGM : LocalEquationChain.valueMatrix C X.functionField v = G := by
      funext i
      unfold LocalEquationChain.valueMatrix
      rw [h3 i i.2, WithTop.untopD_coe, ofLex_toLex]
    rw [hGM]
    exact hG
  · rintro ⟨h1, h3⟩
    refine ⟨_, h3, (eq_lexMap_admissibleFlagValuation_iff hY C hC v _ h3).mpr ⟨h1, fun i hi =>
      (LocalEquationChain.vecValue_valueMatrix C X.functionField v hi).symm⟩⟩

/-- If `v ∼ ν_{Y•}`, then `v = ν_{Y•} G` with `G` the matrix of the values of the local
equations. -/
theorem eq_lexMap_valueMatrix_of_lexEquivalent
    (C : OF5.LocalEquationChain (X.presheaf.stalk hY.point) n) (hC : C.P = admissibleIdeal hY)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : ValuationsLexEquivalent (admissibleFlagValuation hY) v) :
    ∃ hM : IsUnitUpperTriangular (LocalEquationChain.valueMatrix C X.functionField v),
      v = lexMapValuation _ hM (admissibleFlagValuation hY) := by
  obtain ⟨h1, hM⟩ := (lexEquivalent_admissibleFlagValuation_iff hY C hC v).mp hv
  exact ⟨hM, (eq_lexMap_admissibleFlagValuation_iff hY C hC v _ hM).mpr ⟨h1, fun i hi =>
    (LocalEquationChain.vecValue_valueMatrix C X.functionField v hi).symm⟩⟩

/-- **Equivalent, but not necessarily equal**: `ν_{Y•} G = ν_{Y•}` iff `G = I`. -/
theorem lexMap_admissibleFlagValuation_eq_iff (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsUnitUpperTriangular G) :
    lexMapValuation G hG (admissibleFlagValuation hY) = admissibleFlagValuation hY ↔ G = 1 := by
  constructor
  · intro h
    have h1 := (eq_lexMap_admissibleFlagValuation_iff hY (admissibleFlagChain hY)
      (admissibleFlagChain_P hY) _ G hG).mp rfl
    have h2 := (eq_lexMap_admissibleFlagValuation_iff hY (admissibleFlagChain hY)
      (admissibleFlagChain_P hY) (admissibleFlagValuation hY) 1 IsUnitUpperTriangular.one).mp (by
        refine AddValuation.ext fun g => ?_
        rw [lexMapValuation_apply, lexWithTopHom_one])
    funext i
    have hi := h1.2 i i.2
    rw [h, h2.2 i i.2] at hi
    exact (toLex.injective (WithTop.coe_injective hi)).symm
  · rintro rfl
    refine AddValuation.ext fun g => ?_
    rw [lexMapValuation_apply, lexWithTopHom_one]

/-- Every valuation equivalent to `ν_{Y•}` is centred at the point `Yₙ`. -/
theorem isValuationCenter_of_lexEquivalent
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : ValuationsLexEquivalent (admissibleFlagValuation hY) v) :
    AlgebraicValuation.IsValuationCenter v hY.point := by
  obtain ⟨G, hG, rfl⟩ := hv
  obtain ⟨h1, h2⟩ := admissibleFlagValuation_isValuationCenter hY
  have hzero : lexWithTopHom G hG 0 = 0 := map_zero _
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [lexMapValuation_apply, ← hzero]
    exact monotone_lexWithTopHom _ _ (h1 g)
  · rw [lexMapValuation_apply, ← hzero]
    have h := h2 g hg
    induction h' : admissibleFlagValuation hY (algebraMap _ X.functionField g) using
      WithTop.recTopCoe with
    | top => rw [lexWithTopHom_top, hzero]; exact WithTop.coe_lt_top _
    | coe x =>
      rw [h'] at h
      rw [lexWithTopHom_coe]
      exact WithTop.coe_lt_coe.mpr ((strictMono_vecMul hG) (WithTop.coe_lt_coe.mp h))

end SGPT.Okounkov.OF6
