import SGPT.PSH.HermitianProducts

/-!
# Positive current smoothing with the same radial kernels as PSH smoothing

An actual nonnegative scalar test applied to every complementary current
coefficient reconstructs a semipositive one-one form. This statement does not
depend on a choice of approximate identity. It applies in particular to the
genuine radial convolution systems used for decreasing PSH regularization,
so positivity and monotone Bedford--Taylor approximation can use the same
kernels.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentDensityMatrix LocalCurrentDeterminant
  TopDegreeDensity OneOneFormMixedTrace
open scoped Topology Distributions ContDiff ComplexOrder MatrixOrder

attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- The full real one-one form reconstructed from an actual scalar current
test, using the genuine complementary dual basis. -/
def testedForm (T : LocalProductCurrent (m + 1) U m) (φ : 𝓓(U, ℝ)) :
    RealForm (m + 1) 2 :=
  ∑ i, T (formBasis (m + 1) m i) φ • dualForm m i

/-- Every reconstructed coefficient form is of type one-one, independently
of positivity of the tested current. -/
theorem testedForm_isOneOne (T : LocalProductCurrent (m + 1) U m) (φ : 𝓓(U, ℝ)) :
    IsOneOne (testedForm T φ) :=
  isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _

/-- Testing and dual-basis reconstruction are additive in arbitrary current
inputs, with no positivity or closedness restrictions. -/
theorem testedForm_add (A B : LocalProductCurrent (m + 1) U m) (φ : 𝓓(U, ℝ)) :
    testedForm (A + B) φ = testedForm A φ + testedForm B φ := by
  classical
  simp only [testedForm, LinearMap.add_apply, _root_.add_apply, add_smul,
    Finset.sum_add_distrib]

private def testEvaluation (T : LocalProductCurrent (m + 1) U m)
    (φ : 𝓓(U, ℝ)) : formSpan (m + 1) m →ₗ[ℝ] ℝ where
  toFun γ := T γ φ
  map_add' γ δ := by simp
  map_smul' c γ := by simp

/-- The reconstructed form retains the current's exact value on every
complementary constant form, not only on basis tests. -/
theorem testedForm_pairing (T : LocalProductCurrent (m + 1) U m)
    (φ : 𝓓(U, ℝ)) (γ : formSpan (m + 1) m) :
    T γ φ = topDensity (coordinateWedge (γ : RealForm (m + 1) (2 * m))
      (testedForm T φ)) := by
  classical
  have hexpand : T γ φ = ∑ i, (formBasis (m + 1) m).repr γ i *
      T (formBasis (m + 1) m i) φ := by
    change testEvaluation T φ γ = ∑ i, (formBasis (m + 1) m).repr γ i *
      testEvaluation T φ (formBasis (m + 1) m i)
    conv_lhs => rw [← (formBasis (m + 1) m).sum_repr γ, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hexpand, ← wedgeDensity_apply, testedForm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, wedgeDensity_apply, topDensity_dualForm, smul_eq_mul, mul_comm]

/-- Positivity of an actual current and a nonnegative scalar test gives the
full semipositive Hermitian coefficient matrix of the reconstructed form. -/
theorem testedForm_matrix_posSemidef {T : LocalProductCurrent (m + 1) U m}
    (hT : IsPositive T) (φ : 𝓓(U, ℝ)) (hφ : ∀ y, 0 ≤ φ y) :
    IsOneOne (testedForm T φ) ∧
      (normalizedHermitianMatrix (testedForm T φ)).PosSemidef := by
  classical
  have h11 : IsOneOne (testedForm T φ) :=
    isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _
  refine ⟨h11, posSemidef_of_nonneg (L := testEvaluation T φ) ?_ h11 ?_⟩
  · intro γ hγ
    exact hT.positiveDistribution hγ φ hφ
  · exact testedForm_pairing T φ

/-- The actual reconstructed coefficient form is semipositive as a
differential form, so its smooth exterior products are positive. -/
theorem testedForm_isSemipositive {T : LocalProductCurrent (m + 1) U m}
    (hT : IsPositive T) (φ : 𝓓(U, ℝ)) (hφ : ∀ y, 0 ≤ φ y) :
    IsSemipositiveOneOne (testedForm T φ) := by
  obtain ⟨h11, hmatrix⟩ := testedForm_matrix_posSemidef hT φ hφ
  obtain ⟨β, hβ, hβmatrix⟩ := exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq hmatrix
  have heq : testedForm T φ = β := by
    apply sub_eq_zero.mp
    apply eq_zero_of_normalizedHermitianMatrix_eq_zero (isOneOne_sub h11 hβ.1)
    change normalizedHermitianMatrixₗ (testedForm T φ - β) = 0
    rw [map_sub]
    change normalizedHermitianMatrix (testedForm T φ) - normalizedHermitianMatrix β = 0
    rw [hβmatrix, sub_self]
  rw [heq]
  exact hβ

/-- The same translated radial kernel appearing in decreasing PSH smoothing
is an actual compact test on the original current domain. -/
def radialKernelTest {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {v : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (S : RadialConvolutionSystem V K v R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) : 𝓓(U, ℝ) where
  toFun y := S.kernel j (y - z)
  contDiff' := (S.kernel_contDiff j).comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := hK.of_isClosed_subset (isClosed_tsupport _) (S.translated_tsupport j z hz)
  tsupport_subset' := (S.translated_tsupport j z hz).trans hKU

@[simp] theorem radialKernelTest_apply {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {v : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (S : RadialConvolutionSystem V K v R) (hK : IsCompact K) (hKU : K ⊆ U)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) (y : ComplexModel (m + 1)) :
    radialKernelTest S hK hKU j z hz y = S.kernel j (y - z) := rfl

/-- Current positivity for exactly the radial kernels used by the existing
pointwise decreasing PSH approximation, with no second kernel family. -/
theorem radialKernelForm_isSemipositive {V : Opens (ComplexModel (m + 1))}
    {K : Set (ComplexModel (m + 1))} {v : ComplexModel (m + 1) → ℝ} {R : ℝ}
    (S : RadialConvolutionSystem V K v R) (hK : IsCompact K) (hKU : K ⊆ U)
    {T : LocalProductCurrent (m + 1) U m} (hT : IsPositive T)
    (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ V) :
    IsSemipositiveOneOne (testedForm T (radialKernelTest S hK hKU j z hz)) :=
  testedForm_isSemipositive hT _ (fun y => S.kernel_nonneg j (y - z))

end SGPT.PSH.HermitianProducts
