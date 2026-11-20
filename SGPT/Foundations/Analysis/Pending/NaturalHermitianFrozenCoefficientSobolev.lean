import SGPT.Foundations.Analysis.Pending.NaturalVectorCoefficientSobolev
import SGPT.Foundations.Analysis.Pending.NaturalHermitianOrthonormalFormBasis

/-! # Actual frozen original Hermitian form coefficient jets and compact value projection

Three complete mathematical statements and proofs precede this source.
All original model and alternating tensor norms are kept.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenCoefficientSobolev

open FirstPass FirstPass.MongeAmpere NaturalScalarSobolevJet NaturalScalarSobolevBasisGradient
  NaturalCoefficientSobolevRellich NaturalVectorCoefficientSobolev
  NaturalHermitianMetricCoefficients NaturalHermitianOriginalFormMetric
  NaturalHermitianSmoothFormMetric NaturalHermitianOrthonormalFormBasis NaturalHermitianUnitVolume

variable {n : ℕ}

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

variable (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a) (hp : IsStrictlyPositive a)

/-- Literal original-form native coefficient jet in its separate genuine finite Hilbert copy. -/
def fixedFormCoefficientJet (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n)) :
    𝓓_{K}(ComplexModel n, FormCoefficients n q) →ₗ[ℝ]
      CoefficientJetHilbert μ K b (FormIndex n q) :=
  nativeVectorCoefficientJet K (metricFormBasis a hJ hp b q) μ b

/-- The actual fixed-form value map is exactly the preceding genuine coefficient projection. -/
def fixedFormValueCLM (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n)) :
    CoefficientJetHilbert μ K b (FormIndex n q) →L[ℝ] CoefficientL2 μ (FormIndex n q) :=
  coefficientValueCLM μ K b

/-- Original whole-form coefficient test and its actual scalar first jet on every index. -/
theorem fixedFormCoefficientJet_apply
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n))
    (η : 𝓓_{K}(ComplexModel n, FormCoefficients n q)) (s : FormIndex n q) :
    fixedFormCoefficientJet a hJ hp b q μ K η s =
      toSobolevFirstJet μ K b (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η) := rfl

/-- Literal original scalar L2 value readback for every full native form coefficient. -/
theorem fixedFormValueCLM_apply_native
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n))
    (η : 𝓓_{K}(ComplexModel n, FormCoefficients n q)) (s : FormIndex n q) :
    fixedFormValueCLM b q μ K (fixedFormCoefficientJet a hJ hp b q μ K η) s =
      scalarStageL2 μ K (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η) :=
  nativeVectorCoefficientJet_value_apply K (metricFormBasis a hJ hp b q) μ b η s

/-- Exact whole-tensor frozen metric value squared integral, with the original Haar measure. -/
theorem fixedFormValueCLM_norm_sq_native
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n))
    (η : 𝓓_{K}(ComplexModel n, FormCoefficients n q)) :
    ‖fixedFormValueCLM b q μ K (fixedFormCoefficientJet a hJ hp b q μ K η)‖ ^ 2 =
      ∫ x, originalFormMetric a hJ hp q (η x) (η x) ∂μ := by
  change ‖coefficientValueCLM μ K b
    (nativeVectorCoefficientJet K (metricFormBasis a hJ hp b q) μ b η)‖ ^ 2 = _
  rw [nativeVectorCoefficientJet_value_norm_sq]
  simp_rw [metricFormBasis_metric_self a hJ hp b hb q]
  symm
  apply integral_finsetSum
  intro s _
  simpa only [coefficientTestCLM_apply] using
    ((coefficientTestCLM K (metricFormBasis a hJ hp b q) s η).continuous.memLp_of_hasCompactSupport
      (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η).hasCompactSupport :
        MemLp (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η : ComplexModel n → ℝ) 2 μ).integrable_sq

/-- Exact entire original frozen form metric first-jet squared integral in every degree. -/
theorem fixedFormCoefficientJet_norm_sq
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n))
    (η : 𝓓_{K}(ComplexModel n, FormCoefficients n q)) :
    ‖fixedFormCoefficientJet a hJ hp b q μ K η‖ ^ 2 =
      (∫ x, originalFormMetric a hJ hp q (η x) (η x) ∂μ) +
        ∑ i, ∫ x, originalFormMetric a hJ hp q (fderiv ℝ η x (b i))
          (fderiv ℝ η x (b i)) ∂μ := by
  change ‖nativeVectorCoefficientJet K (metricFormBasis a hJ hp b q) μ b η‖ ^ 2 = _
  rw [nativeVectorCoefficientJet_norm_sq]
  simp_rw [metricFormBasis_metric_self a hJ hp b hb q]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · symm
    apply integral_finsetSum
    intro s _
    simpa only [coefficientTestCLM_apply] using
      ((coefficientTestCLM K (metricFormBasis a hJ hp b q) s η).continuous.memLp_of_hasCompactSupport
        (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η).hasCompactSupport :
          MemLp (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η : ComplexModel n → ℝ) 2 μ).integrable_sq
  · apply Finset.sum_congr rfl
    intro i _
    symm
    apply integral_finsetSum
    intro s _
    simpa only [coefficientTest_directional] using
      directional_square_integrable K μ
        (coefficientTestCLM K (metricFormBasis a hJ hp b q) s η) (b i)

/-- Genuine original arbitrary-basis scalar Rellich supplies the actual fixed-form compact projection. -/
theorem isCompactOperator_fixedFormValue
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n)) :
    IsCompactOperator (fixedFormValueCLM b q μ K) :=
  isCompactOperator_coefficientValue μ K b

/-- Compact closure of the actual fixed-form coefficient value image of every original closed ball. -/
theorem isCompact_fixedFormValue_image_closedBall_closure
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n)) (R : ℝ) :
    IsCompact (closure (fixedFormValueCLM b q μ K ''
      Metric.closedBall (0 : CoefficientJetHilbert μ K b (FormIndex n q)) R)) :=
  isCompact_coefficientValue_image_closedBall_closure μ K b R

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Original Hermitian chart data internally constructs the genuine frozen form jets and compact projections. -/
theorem exists_original_chart_frozen_form_jets (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (K : Compacts (ComplexModel n)) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∀ q : ℕ, IsCompactOperator (fixedFormValueCLM b q μ K) ∧
        (∀ η : 𝓓_{K}(ComplexModel n, FormCoefficients n q),
          ‖fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q μ K η‖ ^ 2 =
            (∫ x, formMetricCoefficients w e z q (η x) (η x) ∂μ) +
              ∑ i, ∫ x, formMetricCoefficients w e z q (fderiv ℝ η x (b i))
                (fderiv ℝ η x (b i)) ∂μ) ∧
        ∀ η : 𝓓_{K}(ComplexModel n, FormCoefficients n q),
          ‖fixedFormValueCLM b q μ K
            (fixedFormCoefficientJet (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b q μ K η)‖ ^ 2 =
              ∫ x, formMetricCoefficients w e z q (η x) (η x) ∂μ := by
  obtain ⟨b, hb, ho⟩ := (original_chart_unit_volume w hw e z hz).1
  refine ⟨b, hb, ho, ?_⟩
  intro q
  refine ⟨isCompactOperator_fixedFormValue b q μ K, ?_, ?_⟩
  · intro η
    simpa only [formMetricCoefficients_eq_original w hw e z hz q] using
      fixedFormCoefficientJet_norm_sq (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb q μ K η
  · intro η
    simpa only [formMetricCoefficients_eq_original w hw e z hz q] using
      fixedFormValueCLM_norm_sq_native (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb q μ K η

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenCoefficientSobolev
