import SGPT.Foundations.Schemes.PolynomialHomogeneousSubsetLocalization

/-! # Actual coordinate degree shifts on product localizations

The inverse coordinate action uses the literal divisor unit on the native
localized module. Its homogeneous restriction preserves localization torsion.
-/

namespace SGPT.Foundations.Schemes
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {V : Type} [AddCommGroup V] [Module K V]
  [Module (MvPolynomial (Fin (n + 1)) K) V]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) V]
  (ℳ : ℤ → Submodule K V)
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ]

/-- The native inverse coordinate power on the genuine product localization. -/
def polynomialHomogeneousSubsetDegreeNormalizeAmbient (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m : ℕ) :
    LocalizedModule (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) V →ₗ[
      MvPolynomial (Fin (n + 1)) K]
      LocalizedModule (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) V :=
  (actualLocalizedModuleDivisorUnits (M := V) (MvPolynomial.X i)
    (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
    (homogeneousPowerDenominator (MvPolynomial.X i) m)).unit.inv

omit [Module K V] [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) V] in
/-- Native inverse coordinate multiplication has the literal complementary-numerator formula. -/
theorem polynomialHomogeneousSubsetDegreeNormalizeAmbient_mk (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m q : ℕ) (v : V) :
    polynomialHomogeneousSubsetDegreeNormalizeAmbient K n i S hi m
      (LocalizedModule.mk v (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) q)) =
    LocalizedModule.mk (polynomialHomogeneousSubsetProduct K n (S.erase i) ^ m • v)
      (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) (q + m)) := by
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff (MvPolynomial (Fin (n + 1)) K)
    (actualLocalizedModuleDivisorUnits (M := V) (MvPolynomial.X i)
      (polynomialHomogeneousSubsetProduct K n S)
      ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
        polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
      (homogeneousPowerDenominator (MvPolynomial.X i) m)) _ _).mpr
  change _ = (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m • _
  rw [LocalizedModule.smul'_mk, smul_smul, ← mul_pow,
    ← polynomialHomogeneousSubsetProduct_factor K n i S hi,
    homogeneousPowerDenominator_add]
  exact (LocalizedModule.mk_cancel_common_right
    (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) q)
    (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) m) v).symm

/-- Inverse coordinate multiplication genuinely lowers localized degree m to zero. -/
def polynomialHomogeneousSubsetDegreeNormalize (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m : ℕ) :
    polynomialHomogeneousSubsetPiece K n ℳ S (m : ℤ) →ₗ[K]
      polynomialHomogeneousSubsetPiece K n ℳ S 0 :=
  (((polynomialHomogeneousSubsetDegreeNormalizeAmbient K n i S hi m).restrictScalars K).comp
    (polynomialHomogeneousSubsetPiece K n ℳ S (m : ℤ)).subtype).codRestrict _ (by
      intro z
      obtain ⟨q, v, hv, he⟩ := z.property
      refine ⟨q + m, polynomialHomogeneousSubsetProduct K n (S.erase i) ^ m • v, ?_, ?_⟩
      · have hc := polynomialHomogeneousSubsetProduct_degree K n (S.erase i)
        have hc' := polynomialHomogeneous_mem_integral K n (S.erase i).card
          (polynomialHomogeneousSubsetProduct K n (S.erase i)) hc
        convert SetLike.GradedSMul.smul_mem
          (SetLike.pow_mem_graded (A := polynomialIntegralGrading (K := K) (I := Fin (n + 1))) m hc') hv using 1
        congr 1
        have hcard := Finset.card_erase_of_mem hi
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
        simp only [nsmul_eq_mul, vadd_eq_add, Nat.cast_add, zero_add]
        have hcard' : ((S.erase i).card : ℤ) = (S.card : ℤ) - 1 := by omega
        rw [hcard']
        ring
      · change _ = polynomialHomogeneousSubsetDegreeNormalizeAmbient K n i S hi m z.val
        rw [← he, polynomialHomogeneousSubsetDegreeNormalizeAmbient_mk])

/-- Actual coordinate multiplication raises degree zero to degree m. -/
def polynomialHomogeneousSubsetDegreeMultiply (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (m : ℕ) :
    polynomialHomogeneousSubsetPiece K n ℳ S 0 →ₗ[K]
      polynomialHomogeneousSubsetPiece K n ℳ S (m : ℤ) :=
  (((algebraMap (MvPolynomial (Fin (n + 1)) K)
    (Module.End (MvPolynomial (Fin (n + 1)) K)
      (LocalizedModule (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) V))
        ((MvPolynomial.X i) ^ m)).restrictScalars K).comp
    (polynomialHomogeneousSubsetPiece K n ℳ S 0).subtype).codRestrict _ (by
      intro z
      obtain ⟨q, v, hv, he⟩ := z.property
      refine ⟨q, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m • v, ?_, ?_⟩
      · convert SetLike.GradedSMul.smul_mem
          (SetLike.pow_mem_graded (A := polynomialIntegralGrading (K := K) (I := Fin (n + 1))) m
            (polynomialCoordinate_X_degree i)) hv using 1
        congr 1
        simp only [nsmul_eq_mul, vadd_eq_add, mul_one, zero_add]
      · change _ = (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m • z.val
        rw [← he, LocalizedModule.smul'_mk])

/-- The actual coordinate power and inverse action cancel on every true homogeneous fraction. -/
theorem polynomialHomogeneousSubsetDegreeMultiply_normalize (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m : ℕ)
    (z : polynomialHomogeneousSubsetPiece K n ℳ S (m : ℤ)) :
    polynomialHomogeneousSubsetDegreeMultiply K n ℳ i S m
      (polynomialHomogeneousSubsetDegreeNormalize K n ℳ i S hi m z) = z := by
  apply Subtype.ext
  exact Module.End.isUnit_apply_inv_apply_of_isUnit
    (actualLocalizedModuleDivisorUnits (M := V) (MvPolynomial.X i)
      (polynomialHomogeneousSubsetProduct K n S)
      ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
        polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
      (homogeneousPowerDenominator (MvPolynomial.X i) m)) z.val

/-- The actual inverse action and coordinate power cancel on every true degree-zero fraction. -/
theorem polynomialHomogeneousSubsetDegreeNormalize_multiply (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m : ℕ)
    (z : polynomialHomogeneousSubsetPiece K n ℳ S 0) :
    polynomialHomogeneousSubsetDegreeNormalize K n ℳ i S hi m
      (polynomialHomogeneousSubsetDegreeMultiply K n ℳ i S m z) = z := by
  apply Subtype.ext
  exact Module.End.isUnit_inv_apply_apply_of_isUnit
    (actualLocalizedModuleDivisorUnits (M := V) (MvPolynomial.X i)
      (polynomialHomogeneousSubsetProduct K n S)
      ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
        polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
      (homogeneousPowerDenominator (MvPolynomial.X i) m)) z.val

/-- A true inverted coordinate supplies the native linear equivalence between actual localized degrees. -/
def polynomialHomogeneousSubsetDegreeNormalizeEquiv (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (m : ℕ) :
    polynomialHomogeneousSubsetPiece K n ℳ S (m : ℤ) ≃ₗ[K]
      polynomialHomogeneousSubsetPiece K n ℳ S 0 :=
  { polynomialHomogeneousSubsetDegreeNormalize K n ℳ i S hi m with
    invFun := polynomialHomogeneousSubsetDegreeMultiply K n ℳ i S m
    left_inv := polynomialHomogeneousSubsetDegreeMultiply_normalize K n ℳ i S hi m
    right_inv := polynomialHomogeneousSubsetDegreeNormalize_multiply K n ℳ i S hi m }

end
end SGPT.Foundations.Schemes
