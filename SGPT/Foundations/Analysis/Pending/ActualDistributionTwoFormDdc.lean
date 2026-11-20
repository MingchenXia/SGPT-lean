import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormReading
import SGPT.Foundations.Analysis.Pending.ActualLogarithmicDivisorCurrent
import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

set_option autoImplicit false

/-! # The scalar differential in the literal two-form and complementary readers

Actual compact transposes and Dirac tests identify every coefficient,
with the actual normalization.  Global Siu assembly is separate.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalCurrentPullbackDdc TopDegreeDensity CoordinateWedgeAssoc
  ScalarLeviPositiveCurrent CompactDdcCoordinateExpansion
  ActualDistributionTwoFormReading ActualLogarithmicDivisorCurrent
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private def coefficientAdjoint (v w : ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)) :
    𝓓(U, ℝ) :=
  (-1 / (4 * Real.pi) : ℝ) •
    (dTest (Complex.I • w) (dTest v φ) - dTest (Complex.I • v) (dTest w φ))

private theorem coefficient_transpose (T : 𝓓'(U, ℝ))
    (v w : ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)) :
    ddC T ![v, w] φ = T (coefficientAdjoint v w φ) := by
  simp only [ddC_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul,
    Distribution.lineDerivCLM_apply, neg_neg, coefficientAdjoint, map_smul, map_sub]

private def coordinateAdjoint (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  (1 / 2 : ℝ) • ∑ a, ∑ b,
    formDensity (coordinateWedge
      (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) a))
      (CoordinateWedgeAssoc.oneForm (m + 1) (coordCLM (m + 1) b))) γ •
      coefficientAdjoint (realBasis (m + 1) a) (realBasis (m + 1) b) φ

private theorem reading_transpose (T : 𝓓'(U, ℝ))
    (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    complementaryRead (ddC T) γ φ = T (coordinateAdjoint γ φ) := by
  simp only [complementaryRead, coordinateAdjoint, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, map_sum, map_smul, coefficient_transpose]

private theorem tested_dirac_differential (φ : 𝓓(U, ℝ))
    (x : ComplexModel (m + 1)) :
    testedTwoForm (ddC (Distribution.delta x)) φ = smoothDDC φ x := by
  ext w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw, testedTwoForm_apply, coefficient_transpose, Distribution.delta_apply]
  rw [smoothDDC_apply_eq_realHessian (φ.contDiff.contDiffAt.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  simp only [coefficientAdjoint, _root_.smul_apply, _root_.sub_apply, smul_eq_mul,
    dTest, testFunction_lineDerivCLM_lineDerivCLM_apply]
  have hsym (v u : ComplexModel (m + 1)) : realHessian φ x v u = realHessian φ x u v := by
    simpa only [realHessian_eq_fderiv] using
      (φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).isSymmSndFDerivAt
        (by norm_num) v u
  rw [hsym (Complex.I • w 1) (w 0), hsym (Complex.I • w 0) (w 1)]
  ring

private theorem coordinateAdjoint_apply (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ))
    (x : ComplexModel (m + 1)) :
    coordinateAdjoint γ φ x = formDensity (smoothDDC φ x) γ := by
  rw [← Distribution.delta_apply x (coordinateAdjoint γ φ),
    ← reading_transpose, complementaryRead_apply, tested_dirac_differential]

private def nativeAdjoint (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  ∑ a, ∑ b, (-(1 / (4 * Real.pi)) *
    topDensity ((wedgeLM m (isOneOne_coeffForm a b) γ : formSpan (m + 1) (m + 1)) :
      RealForm (m + 1) (2 * (m + 1)))) •
    dTest (realBasis (m + 1) b) (dTest (realBasis (m + 1) a) φ)

private theorem native_transpose (T : 𝓓'(U, ℝ))
    (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ)) :
    ddc (scalarTopCurrent T) γ φ = T (nativeAdjoint γ φ) := by
  simp only [nativeAdjoint, map_sum, map_smul, smul_eq_mul,
    ddc_apply_apply, scalarTopCurrent_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem nativeAdjoint_apply (γ : formSpan (m + 1) m) (φ : 𝓓(U, ℝ))
    (x : ComplexModel (m + 1)) :
    nativeAdjoint γ φ x = formDensity (smoothDDC φ x) γ := by
  have hφ : ContDiffAt ℝ 2 (φ : ComplexModel (m + 1) → ℝ) x :=
    φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [formDensity_apply, smoothDDC_eq_sum hφ]
  change _ = topDensityLM (m + 1)
    (wedgeLeftLM (m + 1) (γ : RealForm (m + 1) (2 * m)) 2 _)
  simp only [nativeAdjoint, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [dTest_dTest_eq_realHessian, coe_wedgeLM_apply, topDensityLM_apply]
  change _ = _ * topDensity
    (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (coeffForm a b))
  have hs : realHessian φ x (realBasis (m + 1) b) (realBasis (m + 1) a) =
      realHessian φ x (realBasis (m + 1) a) (realBasis (m + 1) b) := by
    simpa only [realHessian_eq_fderiv] using
      hφ.isSymmSndFDerivAt (by norm_num) (realBasis (m + 1) b) (realBasis (m + 1) a)
  rw [hs]
  ring

/-- The literal two-form and native complementary differentials agree on all tests. -/
theorem complementaryRead_ddC (T : 𝓓'(U, ℝ)) :
    complementaryRead (ddC T) = ddc (scalarTopCurrent T) := by
  ext γ φ
  rw [reading_transpose, native_transpose]
  congr 1
  ext x
  rw [coordinateAdjoint_apply, nativeAdjoint_apply]


/-- The produced logarithmic scalar distribution has the genuine geometric
native divisor reading on every complementary form and compact test. -/
theorem single_logarithmic_native_ddc_eq_divisorCurrent
    (d : ComplexModel (m + 1) → ℂ) {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ d (Metric.ball (0 : ComplexModel (m + 1)) r))
    (hdne : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), d x = 0)
    {c : ℝ} (hc : 0 < c) :
    let V : Opens (ComplexModel (m + 1)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
    let p := fun x => (c : EReal) * generatorLog (fun _ : Fin 1 => d) x
    ∃ (hp : PlurisubharmonicOn p V) (hne : ∃ a ∈ V, p a ≠ ⊥)
      (hd0 : ∀ y ∈ V, ∃ᶠ z in 𝓝 y, d z ≠ 0),
      let hV := (convex_ball (0 : ComplexModel (m + 1)) r).isPreconnected
      let T := pshRegularDistribution hp volume hV hne
      ddc (scalarTopCurrent T) = complementaryRead
        (c • DivisorIntegrationCurrent.divisorCurrent hd hd0) := by
  obtain ⟨hp, hne, hd0, hD⟩ :=
    single_logarithmic_ddC_eq_divisorCurrent d hr hd hdne hc
  refine ⟨hp, hne, hd0, ?_⟩
  dsimp only at hD ⊢
  rw [← complementaryRead_ddC, hD]

end SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
