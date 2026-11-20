import SGPT.Toric.ProjectiveLineNativeManifold
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
import SGPT.Foundations.Analysis.Pending.ProductTestForms
set_option autoImplicit false

noncomputable section
namespace SGPT.BBJ
open Set TopologicalSpace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame TopDegreeDensity
open FirstPass.MongeAmpere ProductTestForms
open scoped Distributions ContDiff Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual one-dimensional canonical pairing frame is exactly ordered 1,I. -/
theorem projective_currentPairingBasis_inl (i : Fin 2) :
    currentPairingBasis (canonicalBasis 1) (degreeTwo (n := 1) (by norm_num)) (Sum.inl i) =
      ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I] i := by
  have hf : currentPairingBasis (canonicalBasis 1) (degreeTwo (n := 1) (by norm_num))
      (Sum.inl i) = coordinateRealFrame (n := 1) i := by
    simp only [currentPairingBasis, Module.Basis.reindex_apply]
    simp only [canonicalBasis, Module.Basis.reindex_apply]
    rw [topBasis_apply]
    congr 1
  rw [hf]
  fin_cases i
  · change coordinateRealFrame (n := 1) (0 : Fin 2) = projectiveModelEquiv 1
    rw [coordinateRealFrame_one_zero]
    ext j
    fin_cases j
    simp [coordinateVector, projectiveModelEquiv_apply_zero]
  · change coordinateRealFrame (n := 1) (1 : Fin 2) = projectiveModelEquiv Complex.I
    rw [coordinateRealFrame_one_one]
    ext j
    fin_cases j
    simp [coordinateVector, projectiveModelEquiv_apply_zero]

/-- The unique tuple in the actual complementary degree, retaining its dimension cast. -/
def projectiveCurrentEmptyTuple :
    Fin (Module.finrank ℝ (ComplexModel 1) - 2) → ComplexModel 1 :=
  fun i => False.elim (by have hi := i.isLt; have hd := complexModel_real_finrank 1; omega)

/-- Contracting the actual basis volume with the ordered projective pair gives one. -/
theorem projective_current_volume_contract :
    contractVolume (basisVolume
      (currentPairingBasis (canonicalBasis 1) (degreeTwo (n := 1) (by norm_num))))
      ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I]
      projectiveCurrentEmptyTuple = 1 := by
  rw [contractVolume_apply]
  have he : Sum.elim ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I]
      projectiveCurrentEmptyTuple =
        currentPairingBasis (canonicalBasis 1) (degreeTwo (n := 1) (by norm_num)) := by
    funext i
    cases i with
    | inl i => exact (projective_currentPairingBasis_inl i).symm
    | inr i => have hi := i.isLt; have hd := complexModel_real_finrank 1; omega
  rw [he, basisVolume_self]

/-- Every actual complementary test form is reconstructed from its genuine scalar test. -/
theorem projective_current_scalar_test {Ω : Opens (ComplexModel 1)}
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel 1) - 2)) :
    constantTestFormCLM
      (contractVolume (basisVolume
        (currentPairingBasis (canonicalBasis 1) (degreeTwo (n := 1) (by norm_num))))
        ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I])
      (testCoefficientCLM projectiveCurrentEmptyTuple η) = η := by
  ext z w
  have hw : w = projectiveCurrentEmptyTuple := by
    funext i
    have hi := i.isLt
    have hd := complexModel_real_finrank 1
    change i.val < Module.finrank ℝ (ComplexModel 1) - 2 at hi
    omega
  rw [hw]
  simp only [constantTestFormCLM_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, testCoefficientCLM_apply]
  rw [projective_current_volume_contract, mul_one]

/-- Genuine degree-two global-current testing equals its canonical oriented scalar coefficient. -/
theorem projective_scalar_current_calibration
    (S : GlobalCurrent 1 P1 (degreeTwo (n := 1) (by norm_num)))
    (f : ComplexChart 1 P1)
    (η : TestForm (chartTarget f) (Module.finrank ℝ (ComplexModel 1) - 2)) :
    S.inChart f η = S.coefficients (canonicalBasis 1) f
      ![projectiveModelEquiv 1, projectiveModelEquiv Complex.I]
      (testCoefficientCLM projectiveCurrentEmptyTuple η) := by
  rw [GlobalCurrent.coefficients_apply, projective_current_scalar_test]

/-- The actual zeroth form power is one on the unique empty tuple. -/
theorem projective_formPow_zero_coeff (w : SmoothRealForm 1 P1 2)
    (f : ComplexChart 1 P1) (z : ComplexModel 1) (v : Fin 0 → ComplexModel 1) :
    (formPow w 0).coeff f z v = 1 := by
  change coordinateWedgeUnit v = 1
  simp [coordinateWedgeUnit]

/-- Scalar multiplication of the actual zeroth power has its literal chart coefficient. -/
theorem projective_scalar_formPow_zero_coeff (w : SmoothRealForm 1 P1 2)
    (h : P1 → ℝ) (hh : ChartSmooth (n := 1) h)
    (f : ComplexChart 1 P1) (z : ComplexModel 1) (v : Fin 0 → ComplexModel 1) :
    (smulFun h hh (formPow w 0)).coeff f z v = h (f.val.symm z) := by
  simp only [smulFun_coeff, ContinuousAlternatingMap.smul_apply,
    projective_formPow_zero_coeff, smul_eq_mul, mul_one]

end SGPT.BBJ
