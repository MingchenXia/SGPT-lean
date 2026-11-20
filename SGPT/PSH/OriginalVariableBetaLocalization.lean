import SGPT.PSH.OriginalCompactComplexScalarExtension
import SGPT.PSH.OriginalGlobalConstantBetaLocalization
import SGPT.PSH.SemipositiveSquareDecomposition

/-! ACTUAL arbitrary smooth LOCAL beta fields globalized on compact tests. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set Filter Finset TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft
open scoped Topology ContDiff

/-- Physical finite coordinate expansion of EVERY actual complex covector,
including the empty zero-dimensional coordinate family. -/
theorem complex_covector_eq_coordinate_sum {n : ℕ} (b : ComplexModel n →L[ℂ] ℂ) :
    b=∑ j : Fin n,b (coordinateVector j) • EuclideanSpace.proj j := by
  ext v
  have hsum : b v=∑ j : Fin n,v.ofLp j*b (coordinateVector j) := by
    have h := congrArg b (eq_sum_coordinateVector v)
    simpa only [map_sum,map_smul,smul_eq_mul] using h
  rw [hsum]
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change v.ofLp j*b (coordinateVector j)=b (coordinateVector j)*v.ofLp j
  ring

universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] (A : VariableComplexAtlas X)

/-- Genuine GLOBAL smooth(1,0) form equals an ARBITRARY prescribed chart-smooth
covector field on the ACTUAL compact K. Actual global scalar/covector producers
and physical finite coordinate expansion prove every field internally. -/
theorem global_one_zero_variable_on_compact (i : A.Index)
    (K : Compacts (ComplexModel (A.dimension i))) (hKU : (K : Set _)⊆(A.chart i).target)
    (b : ComplexModel (A.dimension i) → ComplexModel (A.dimension i) →L[ℂ] ℂ)
    (hb : ContDiffOn ℝ ∞ b (A.chart i).target) :
    ∃ B : OriginalGlobalOneZeroForm A,∀ z∈(K : Set _),B.coeff i z=b z := by
  classical
  have hrestrict : ContDiffOn ℝ ∞ (fun z => (b z).restrictScalars ℝ) (A.chart i).target :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel (A.dimension i)) ℂ ℝ ℝ).toContinuousLinearMap
      |>.contDiff.comp_contDiffOn hb
  choose a ha hval using (fun j : Fin (A.dimension i) =>
    global_complex_smooth_scalar_on_compact A i K hKU
      (fun z => b z (coordinateVector j)) (hrestrict.clm_apply contDiffOn_const))
  choose B hB using (fun j : Fin (A.dimension i) =>
    original_global_one_zero_constant_on_compact A i K hKU (EuclideanSpace.proj j))
  refine ⟨finiteSumOneZero A (fun j => smoothScalarOneZero A (a j) (ha j) (B j)),?_⟩
  intro z hz
  change (∑ j : Fin (A.dimension i),a j ((A.chart i).symm z) • (B j).coeff i z)=b z
  have haz (j : Fin (A.dimension i)) : a j ((A.chart i).symm z)=b z (coordinateVector j) := hval j z hz
  have hBz (j : Fin (A.dimension i)) : (B j).coeff i z=EuclideanSpace.proj j := hB j z hz
  simp_rw [haz,hBz]
  exact (complex_covector_eq_coordinate_sum (b z)).symm

/-- Whole local smooth beta families are genuinely globalized on SAME compact
scalar-test support, with no supplied extension or positivity certificate. -/
theorem global_beta_family_variable_on_compact (i : A.Index)
    (K : Compacts (ComplexModel (A.dimension i))) (hKU : (K : Set _)⊆(A.chart i).target)
    (p : ℕ)
    (beta : Fin p → ComplexModel (A.dimension i) → ComplexModel (A.dimension i) →L[ℂ] ℂ)
    (hbeta : ∀ j,ContDiffOn ℝ ∞ (beta j) (A.chart i).target) :
    ∃ B : Fin p → OriginalGlobalOneZeroForm A,∀ j z,z∈(K : Set _) → (B j).coeff i z=beta j z := by
  classical
  choose B hB using (fun j : Fin p => global_one_zero_variable_on_compact A i K hKU (beta j) (hbeta j))
  exact ⟨B,fun j z hz => hB j z hz⟩

end SGPT.PSH.ComplexCurrentBridge
