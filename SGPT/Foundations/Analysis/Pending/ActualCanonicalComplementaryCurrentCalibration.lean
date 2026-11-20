import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
import SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity

set_option autoImplicit false

/-! # Canonical calibration of actual complete current coefficient readings

The actual complex-positive basis fixes the signed pairing as well as Haar
volume.  No current positivity or supplied reading identity is required.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentPullbackDdc TopDegreeDensity ConstantFormProducts CanonicalCurrentFrame
  CanonicalSmoothCurrentDensity ActualDistributionTwoFormReading
  ActualAnalyticCurrentLocalDensity CanonicalComplementaryCurrentTests
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem testedTwoForm_tuple (A : DistributionForm U 2) (φ : 𝓓(U, ℝ))
    (v : Fin 2 → ComplexModel (m + 1)) : testedTwoForm A φ v = A v φ := by
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact testedTwoForm_apply A φ _ _

private theorem cast_constant_test {a b : ℕ} (h : a = b)
    (γ : RealForm (m + 1) a) (φ : 𝓓(U, ℝ)) :
    castTestDegree h (constantTestFormCLM γ φ) =
      constantTestFormCLM (castForm h γ) φ := by
  subst b
  rfl

private theorem cast_map_apply {a b : ℕ} (h : a = b)
    (α : TestForm U a) :
    ((h ▸ ContinuousLinearMap.id ℝ (TestForm U a)) :
      TestForm U a →L[ℝ] TestForm U b) α = castTestDegree h α := by
  subst b
  rfl

private theorem density_comm (β : RealForm (m + 1) 2)
    (γ : formSpan (m + 1) m) :
    formDensity β γ = topDensity (wedgeTo
      (by omega : 2 + 2 * m = 2 * (m + 1)) β ↑γ) := by
  exact congrArg (topDensity (n := m + 1))
    (wedgeTo_comm_of_mem_formSpan γ.property β
      (rfl : 2 * m + 2 = 2 * m + 2) (by omega : 2 + 2 * m = 2 * m + 2))

private theorem density_cast_wedge (β : RealForm (m + 1) 2)
    (γ : formSpan (m + 1) m) :
    formDensity β γ =
      topDensity (wedgeTo (by rw [complexModel_real_finrank]; omega :
        2 + (Module.finrank ℝ (ComplexModel (m + 1)) - 2) = 2 * (m + 1))
          β
          (castForm (by rw [complexModel_real_finrank]; omega :
            2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) ↑γ)) := by
  refine (density_comm β γ).trans ?_
  exact congrArg (topDensity (n := m + 1))
    (wedgeTo_castForm_right
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
      (by rw [complexModel_real_finrank]; omega :
        2 + (Module.finrank ℝ (ComplexModel (m + 1)) - 2) = 2 * (m + 1))
      (by omega : 2 + 2 * m = 2 * (m + 1)) β ↑γ).symm

private theorem canonical_pairing_eq_cast_density (A : DistributionForm U 2)
    (φ : 𝓓(U, ℝ)) (β : RealForm (m + 1) 2)
    (hβ : ∀ v, β v = A v φ) (γ : formSpan (m + 1) m) :
    toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m)) A
        (castTestDegree (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
          (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)) =
      topDensity (wedgeTo (by rw [complexModel_real_finrank]; omega :
        2 + (Module.finrank ℝ (ComplexModel (m + 1)) - 2) = 2 * (m + 1))
        β (castForm (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) ↑γ)) := by
  classical
  rw [cast_constant_test]
  change wedgePairing (currentPairingBasis (canonicalBasis (m + 1))
    (degreeTwo (Nat.succ_pos m))) A (constantTestFormCLM _ φ) = _
  rw [wedgePairing_apply]
  refine (Finset.sum_congr rfl (fun s _ => ?_)).trans
    (shuffleDensity_eq_topDensity (k := degreeTwo (Nat.succ_pos m)) β _)
  rw [testCoefficient_constantTestForm, map_smul, ← hβ]
  simp [Units.smul_def, zsmul_eq_mul, smul_eq_mul, mul_comm]

/-- The genuine canonical shuffle pairing is the complete complementary reading. -/
theorem complementaryRead_eq_canonical_pairing (A : DistributionForm U 2)
    (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    complementaryRead A γ φ =
      toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m)) A
        (castTestDegree (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
          (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)) := by
  exact (complementaryRead_apply A γ φ).trans
    ((density_cast_wedge (testedTwoForm A φ) γ).trans
      (canonical_pairing_eq_cast_density A φ (testedTwoForm A φ)
        (testedTwoForm_tuple A φ) γ).symm)

/-- Coefficients extracted in the actual canonical frame restore the entire
original chart reading, with no current positivity hypothesis. -/
theorem complementaryRead_coefficients_eq_chartSpanCurrent
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) :
    complementaryRead (T.coefficients (canonicalBasis (m + 1)) e) =
      chartSpanCurrent T e := by
  ext γ φ
  rw [complementaryRead_eq_canonical_pairing]
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (fromLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
      (T.inChart e)) _ = _
  rw [CurrentPairing.toLocalCurrent_fromLocalCurrent]
  dsimp only [chartSpanCurrent]
  apply congrArg (T.inChart e)
  exact (cast_map_apply (U := chartTarget e)
    (a := 2 * m) (b := Module.finrank ℝ (ComplexModel (m + 1)) - 2)
    (by rw [complexModel_real_finrank]; omega)
    (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)).symm

/-- Canonical signed orientation and actual Euclidean Haar normalization agree. -/
theorem haarFactor_canonicalBasis (n : ℕ) :
    LelongPoincareDivisor.haarFactor (canonicalBasis n) = 1 := by
  unfold LelongPoincareDivisor.haarFactor
  simp only [addHaar_canonicalBasis, Measure.addHaarScalarFactor_self]

end SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
