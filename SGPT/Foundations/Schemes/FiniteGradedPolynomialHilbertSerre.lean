import SGPT.Foundations.Schemes.FiniteGradedPolynomialDimensionSeries
import Mathlib.RingTheory.Polynomial.HilbertPoly

/-! # Genuine Hilbert--Serre induction for actual finite graded polynomial modules

The actual coordinate annihilator and quotient delete one variable. Their
native dimension recurrence derives the polynomial numerator, rather than
assuming a rational dimension series.
-/

universe u

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable {K : Type u} [Field K]

/-- Genuine variable deletion derives a polynomial denominator for actual degree dimensions. -/
theorem finiteGradedPolynomialDimensionSeries_polynomialDenominator_dimensionInduction
    (q : ℕ) :
    ∀ (I M : Type u) [Fintype I] [AddCommGroup M] [Module K M]
      [Module (MvPolynomial I K) M] [IsScalarTower K (MvPolynomial I K) M]
      (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
      [Module.Finite (MvPolynomial I K) M],
      Fintype.card I ≤ q → ∀ b : ℤ, (∀ m : ℤ, m < b → ℳ m = ⊥) →
      ∃ P : Polynomial ℚ,
        (1 - PowerSeries.X) ^ q * actualGradedDimensionSeries ℳ b = (P : PowerSeries ℚ) := by
  classical
  induction q with
  | zero =>
    intro I M _ _ _ _ _ ℳ _ _ _ hcard b _hb
    let : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
    obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_eq_polynomial_of_isEmpty (I := I) ℳ b
    exact ⟨P, by simpa only [pow_zero, one_mul] using hP⟩
  | succ q ih =>
    intro I M _ _ _ _ _ ℳ _ _ _ hcard b hb
    rcases isEmpty_or_nonempty I with hEmpty | hNonempty
    · let : IsEmpty I := hEmpty
      obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_eq_polynomial_of_isEmpty (I := I) ℳ b
      refine ⟨(1 - Polynomial.X) ^ (q + 1) * P, ?_⟩
      simpa using congrArg (fun H : PowerSeries ℚ => (1 - PowerSeries.X) ^ (q + 1) * H) hP
    · obtain ⟨i⟩ := hNonempty
      let f := LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i)
      let U : Type u := LinearMap.ker f
      let V : Type u := M ⧸ LinearMap.range f
      let ℳU := homogeneousSubmodulePiece ℳ (LinearMap.ker f)
      let ℳV := homogeneousRingQuotientPiece ℳ (LinearMap.range f)
      let hx : (MvPolynomial.X i : MvPolynomial I K) ∈
          polynomialIntegralGrading (K := K) (I := I) 1 :=
        MvPolynomial.isWeightedHomogeneous_X K (fun _ : I => (1 : ℤ)) i
      let := homogeneousScalarKernelDecomposition
        (polynomialIntegralGrading (K := K) (I := I)) ℳ hx
      let := homogeneousScalarQuotientDecomposition
        (polynomialIntegralGrading (K := K) (I := I)) ℳ hx
      let := polynomialDeletedCoordinateModule K I U i
      let := polynomialDeletedCoordinateModule K I V i
      let := polynomialDeletedCoordinateScalarTower (K := K) (I := I) (N := U) i
      let := polynomialDeletedCoordinateScalarTower (K := K) (I := I) (N := V) i
      let := polynomialCoordinateKernelDeletedGradedSMul ℳ i
      let := polynomialCoordinateQuotientDeletedGradedSMul ℳ i
      let := polynomialCoordinateKernelDeleted_finite (K := K) (I := I) (M := M) i
      let := polynomialCoordinateQuotientDeleted_finite (K := K) (I := I) (M := M) i
      have hsmall : Fintype.card {j : I // j ≠ i} ≤ q := by
        have hlt := Fintype.card_subtype_lt (p := fun j : I => j ≠ i) (x := i) (by simp)
        omega
      obtain ⟨PU, hPU⟩ := ih {j : I // j ≠ i} U ℳU hsmall b
        (fun m hm => homogeneousSubmodulePiece_eq_bot_of_eq_bot ℳ _ m (hb m hm))
      obtain ⟨PV, hPV⟩ := ih {j : I // j ≠ i} V ℳV hsmall b
        (fun m hm => homogeneousRingQuotientPiece_eq_bot_of_eq_bot ℳ _ m (hb m hm))
      have hrec := finiteGradedPolynomialDimensionSeries_coordinate_recurrence ℳ i b
        (hb (b - 1) (by omega))
      change (1 - PowerSeries.X) * actualGradedDimensionSeries ℳ b =
        actualGradedDimensionSeries ℳV b - PowerSeries.X * actualGradedDimensionSeries ℳU b at hrec
      refine ⟨PV - Polynomial.X * PU, ?_⟩
      calc
        (1 - PowerSeries.X) ^ (q + 1) * actualGradedDimensionSeries ℳ b =
            (1 - PowerSeries.X) ^ q *
              ((1 - PowerSeries.X) * actualGradedDimensionSeries ℳ b) := by
                rw [pow_succ, mul_assoc]
        _ = (1 - PowerSeries.X) ^ q *
              (actualGradedDimensionSeries ℳV b -
                PowerSeries.X * actualGradedDimensionSeries ℳU b) := by rw [hrec]
        _ = (PV : PowerSeries ℚ) - PowerSeries.X * (PU : PowerSeries ℚ) := by
          have hm : (1 - PowerSeries.X) ^ q *
              (PowerSeries.X * actualGradedDimensionSeries ℳU b) =
                PowerSeries.X * ((1 - PowerSeries.X) ^ q * actualGradedDimensionSeries ℳU b) := by
            ring
          rw [mul_sub, hPV, hm, hPU]
        _ = ((PV - Polynomial.X * PU : Polynomial ℚ) : PowerSeries ℚ) := by simp

section NativeHilbertSerre

variable {I M : Type u} [hI : Fintype I] [AddCommGroup M]
  [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hI hTower hDecomp hGraded hFinite

/-- The actual variable count supplies the genuine Hilbert--Serre denominator. -/
theorem finiteGradedPolynomialDimensionSeries_polynomialDenominator (b : ℤ)
    (hb : ∀ m : ℤ, m < b → ℳ m = ⊥) :
    ∃ P : Polynomial ℚ, (1 - PowerSeries.X) ^ Fintype.card I *
      actualGradedDimensionSeries ℳ b = (P : PowerSeries ℚ) :=
  finiteGradedPolynomialDimensionSeries_polynomialDenominator_dimensionInduction
    (K := K) (Fintype.card I) I M ℳ le_rfl b hb

/-- Actual finite homogeneous generators derive some true dimension-series polynomial numerator. -/
theorem finiteGradedPolynomialDimensionSeries_exists_polynomialDenominator :
    ∃ b : ℤ, ∃ P : Polynomial ℚ, (1 - PowerSeries.X) ^ Fintype.card I *
      actualGradedDimensionSeries ℳ b = (P : PowerSeries ℚ) := by
  obtain ⟨b, hb⟩ := finiteGradedPolynomialPiece_eventually_eq_bot (I := I) ℳ
  obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_polynomialDenominator (I := I) ℳ b hb
  exact ⟨b, P, hP⟩

/-- Actual variable induction and the native unit inverse derive the true rational dimension series. -/
theorem finiteGradedPolynomialDimensionSeries_rational (b : ℤ)
    (hb : ∀ m : ℤ, m < b → ℳ m = ⊥) :
    ∃ P : Polynomial ℚ, actualGradedDimensionSeries ℳ b =
      (P : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (Fintype.card I) : PowerSeries ℚ) := by
  obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_polynomialDenominator (I := I) ℳ b hb
  have hi : (PowerSeries.invOneSubPow ℚ (Fintype.card I) : PowerSeries ℚ) *
      (1 - PowerSeries.X) ^ Fintype.card I = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℚ (Fintype.card I)).val_inv
  have h := congrArg
    (fun H : PowerSeries ℚ => (PowerSeries.invOneSubPow ℚ (Fintype.card I) : PowerSeries ℚ) * H) hP
  rw [← mul_assoc, hi, one_mul] at h
  exact ⟨P, h.trans (mul_comm _ _)⟩

/-- Genuine finite homogeneous covers and variable induction produce an actual rational dimension series. -/
theorem finiteGradedPolynomialDimensionSeries_exists_rational :
    ∃ b : ℤ, ∃ P : Polynomial ℚ, actualGradedDimensionSeries ℳ b =
      (P : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ (Fintype.card I) : PowerSeries ℚ) := by
  obtain ⟨b, hb⟩ := finiteGradedPolynomialPiece_eventually_eq_bot (I := I) ℳ
  obtain ⟨P, hP⟩ := finiteGradedPolynomialDimensionSeries_rational (I := I) ℳ b hb
  exact ⟨b, P, hP⟩

end NativeHilbertSerre

end

end SGPT.Foundations.Schemes
