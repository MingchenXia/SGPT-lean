import SGPT.Foundations.Schemes.FiniteGradedPolynomialHilbertSerre

/-! # The actual eventual polynomial of finite graded polynomial modules

Genuine Hilbert--Serre rationality supplies the native coefficient consumer.
The dimension polynomial is then translated to the original integer degree,
with an explicit ambient variable-count degree bound.
-/

universe u

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeHilbertPolynomial_natDegree_le (P : Polynomial ℚ) (q : ℕ) :
    (Polynomial.hilbertPoly P q).natDegree ≤ q - 1 := by
  by_cases h : Polynomial.hilbertPoly P q = 0
  · rw [h]
    simp
  · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero h]
    omega

variable {K I M : Type u} [Field K] [hI : Fintype I] [AddCommGroup M]
  [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hI hTower hDecomp hGraded hFinite

/-- Genuine rationality and the native coefficient theorem give the actual shifted dimension polynomial. -/
theorem finiteGradedPolynomialDimensionSeries_eventualPolynomial_shifted (b : ℤ)
    (hb : ∀ m : ℤ, m < b → ℳ m = ⊥) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ Fintype.card I - 1 ∧
      (Fintype.card I = 0 → Q = 0) ∧
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        (Module.finrank K (ℳ (b + (n : ℤ))) : ℚ) = Q.eval (n : ℚ) := by
  obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_rational (I := I) ℳ b hb
  refine ⟨Polynomial.hilbertPoly P (Fintype.card I),
    nativeHilbertPolynomial_natDegree_le P (Fintype.card I), ?_, P.natDegree, ?_⟩
  · intro hcard
    rw [hcard, Polynomial.hilbertPoly_zero_right]
  · intro n hn
    rw [← actualGradedDimensionSeries_coeff ℳ b n, hP]
    exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval (Fintype.card I) hn

/-- Translation gives the actual polynomial in the original integer degree from any true lower bound. -/
theorem finiteGradedPolynomialPiece_eventualPolynomial_of_lowerBound (b : ℤ)
    (hb : ∀ m : ℤ, m < b → ℳ m = ⊥) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ Fintype.card I - 1 ∧
      (Fintype.card I = 0 → Q = 0) ∧
      ∃ c : ℤ, ∀ m : ℤ, c ≤ m →
        (Module.finrank K (ℳ m) : ℚ) = Q.eval (m : ℚ) := by
  obtain ⟨R, hRdeg, hRzero, N, hR⟩ :=
    finiteGradedPolynomialDimensionSeries_eventualPolynomial_shifted (I := I) ℳ b hb
  let Q : Polynomial ℚ := R.comp (Polynomial.X - Polynomial.C (b : ℚ))
  have hQdeg : Q.natDegree ≤ Fintype.card I - 1 := by
    dsimp [Q]
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    exact hRdeg
  refine ⟨Q, hQdeg, ?_, b + (N : ℤ) + 1, ?_⟩
  · intro hcard
    simp [Q, hRzero hcard]
  · intro m hm
    let n : ℕ := (m - b).toNat
    have hnint : (n : ℤ) = m - b := by dsimp [n]; omega
    have hn : N < n := by omega
    have hindex : b + (n : ℤ) = m := by omega
    have hnq : (n : ℚ) = (m : ℚ) - (b : ℚ) := by exact_mod_cast hnint
    calc
      (Module.finrank K (ℳ m) : ℚ) = R.eval (n : ℚ) := by
        rw [← hindex]
        exact hR n hn
      _ = Q.eval (m : ℚ) := by simp [Q, Polynomial.eval_comp, hnq]

/-- Actual finite homogeneous generators derive the genuine eventual dimension polynomial and its ambient bound. -/
theorem finiteGradedPolynomialPiece_eventualPolynomial :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ Fintype.card I - 1 ∧
      (Fintype.card I = 0 → Q = 0) ∧
      ∃ c : ℤ, ∀ m : ℤ, c ≤ m →
        (Module.finrank K (ℳ m) : ℚ) = Q.eval (m : ℚ) := by
  obtain ⟨b, hb⟩ := finiteGradedPolynomialPiece_eventually_eq_bot (I := I) ℳ
  exact finiteGradedPolynomialPiece_eventualPolynomial_of_lowerBound (I := I) ℳ b hb

end

end SGPT.Foundations.Schemes
