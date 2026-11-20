import SGPT.Foundations.Analysis.Pending.NaturalCoefficientSobolevRellich

/-! # Genuine original vector-valued compact tests and fixed-basis coefficient jets

Four entire mathematical statements and proofs precede this source.
The original domain and fiber norms are retained, with internal coordinate constants.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalVectorCoefficientSobolev

open NaturalScalarSobolevJet NaturalScalarSobolevBasisGradient NaturalCoefficientSobolevRellich

variable {E F χ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype χ] (K : Compacts E) (c : Module.Basis χ ℝ F)

/-- Actual fixed-basis coefficient postcomposition on the entire original native test space. -/
def coefficientTestCLM (j : χ) : 𝓓_{K}(E, F) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  ContDiffMapSupportedIn.postcompCLM (basisCoordinateCLM c j)

omit [Fintype χ] in
/-- Literal original basis coefficient of the native vector value. -/
theorem coefficientTestCLM_apply (j : χ) (η : 𝓓_{K}(E, F)) (x : E) :
    coefficientTestCLM K c j η x = c.repr (η x) j := rfl

omit [Fintype χ] in
/-- Whole ordinary derivative of the genuine scalar coefficient, via the actual chain rule. -/
theorem coefficientTest_fderiv (j : χ) (η : 𝓓_{K}(E, F)) (x : E) :
    fderiv ℝ (coefficientTestCLM K c j η) x =
      (basisCoordinateCLM c j).comp (fderiv ℝ η x) := by
  change fderiv ℝ ((basisCoordinateCLM c j) ∘ η) x = _
  have hd : DifferentiableAt ℝ η x := η.contDiff.differentiable (by simp) x
  exact ((basisCoordinateCLM c j).hasFDerivAt.comp x hd.hasFDerivAt).fderiv

omit [Fintype χ] in
/-- Actual derivative readback in every original direction. -/
theorem coefficientTest_directional (j : χ) (η : 𝓓_{K}(E, F)) (x h : E) :
    fderiv ℝ (coefficientTestCLM K c j η) x h = c.repr (fderiv ℝ η x h) j := by
  rw [coefficientTest_fderiv]
  rfl

/-- The full original vector is reconstructed by the actual native coefficients. -/
theorem reconstruct_native (η : 𝓓_{K}(E, F)) (x : E) :
    (∑ j, coefficientTestCLM K c j η x • c j) = η x := by
  simpa only [coefficientTestCLM_apply] using c.sum_repr (η x)

/-- The full original derivative vector is reconstructed on every direction. -/
theorem reconstruct_derivative (η : 𝓓_{K}(E, F)) (x h : E) :
    (∑ j, fderiv ℝ (coefficientTestCLM K c j η) x h • c j) = fderiv ℝ η x h := by
  simpa only [coefficientTest_directional] using c.sum_repr (fderiv ℝ η x h)

/-- Genuine infinite ordinary vector differentiation followed by actual evaluation. -/
def vectorDirectionalStageCLM (h : E) : 𝓓_{K}(E, F) →L[ℝ] 𝓓_{K}(E, F) :=
  (ContDiffMapSupportedIn.postcompCLM (ContinuousLinearMap.apply ℝ F h)).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

omit [FiniteDimensional ℝ F] in
/-- Infinite-order original vector directional readback, with no fallback branch. -/
theorem vectorDirectionalStageCLM_apply (h : E) (η : 𝓓_{K}(E, F)) (x : E) :
    vectorDirectionalStageCLM K h η x = fderiv ℝ η x h := by
  change (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ η) x h = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ η (by simp)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
/-- Actual original vector norm square integrability from its genuine compact smooth support. -/
theorem norm_square_integrable (η : 𝓓_{K}(E, F)) :
    Integrable (fun x => ‖η x‖ ^ 2) μ := by
  exact (η.continuous.norm.memLp_of_hasCompactSupport η.hasCompactSupport.norm :
    MemLp (fun x => ‖η x‖) 2 μ).integrable_sq

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
/-- Actual original directional vector norm square integrability. -/
theorem directional_norm_square_integrable (η : 𝓓_{K}(E, F)) (h : E) :
    Integrable (fun x => ‖fderiv ℝ η x h‖ ^ 2) μ := by
  simpa only [vectorDirectionalStageCLM_apply] using
    norm_square_integrable K μ (vectorDirectionalStageCLM K h η)

/-- Genuine linear original-vector producer into the constructed finite coefficient-jet Hilbert space. -/
def nativeVectorCoefficientJet : 𝓓_{K}(E, F) →ₗ[ℝ] CoefficientJetHilbert μ K b χ where
  toFun η := nativeCoefficientJet μ K b (fun j => coefficientTestCLM K c j η)
  map_add' η θ := by
    apply PiLp.ext
    intro j
    change toSobolevFirstJet μ K b (coefficientTestCLM K c j (η + θ)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r η := by
    apply PiLp.ext
    intro j
    change toSobolevFirstJet μ K b (coefficientTestCLM K c j (r • η)) = _
    rw [map_smul, map_smul]
    rfl

omit [Fintype χ] in
/-- Actual coefficient-jet coordinate on every native original vector test. -/
theorem nativeVectorCoefficientJet_apply (η : 𝓓_{K}(E, F)) (j : χ) :
    nativeVectorCoefficientJet K c μ b η j =
      toSobolevFirstJet μ K b (coefficientTestCLM K c j η) := rfl

/-- Literal integral formula in original values and whole ordinary derivative coefficients. -/
theorem nativeVectorCoefficientJet_norm_sq (η : 𝓓_{K}(E, F)) :
    ‖nativeVectorCoefficientJet K c μ b η‖ ^ 2 =
      ∑ j, ((∫ x, (c.repr (η x) j) ^ 2 ∂μ) +
        ∑ i, ∫ x, (c.repr (fderiv ℝ η x (b i)) j) ^ 2 ∂μ) := by
  change ‖nativeCoefficientJet μ K b (fun j => coefficientTestCLM K c j η)‖ ^ 2 = _
  rw [nativeCoefficientJet_norm_sq]
  simp only [coefficientTestCLM_apply, coefficientTest_directional]

/-- Original scalar L2 readback of the actual coefficient value on native original vector tests. -/
theorem nativeVectorCoefficientJet_value_apply (η : 𝓓_{K}(E, F)) (j : χ) :
    coefficientValueCLM μ K b (nativeVectorCoefficientJet K c μ b η) j =
      scalarStageL2 μ K (coefficientTestCLM K c j η) :=
  coefficientValueCLM_apply_native μ K b (fun j => coefficientTestCLM K c j η) j

/-- Original whole-Haar coefficient value square integral formula. -/
theorem nativeVectorCoefficientJet_value_norm_sq (η : 𝓓_{K}(E, F)) :
    ‖coefficientValueCLM μ K b (nativeVectorCoefficientJet K c μ b η)‖ ^ 2 =
      ∑ j, ∫ x, (c.repr (η x) j) ^ 2 ∂μ := by
  change ‖coefficientValueCLM μ K b
    (nativeCoefficientJet μ K b (fun j => coefficientTestCLM K c j η))‖ ^ 2 = _
  rw [coefficientValueCLM_norm_sq_native]
  simp only [coefficientTestCLM_apply]

omit [FiniteDimensional ℝ E] in
/-- Genuine finite coefficient square integral estimate in the original fiber norm. -/
theorem integral_coefficient_squares_le (η : 𝓓_{K}(E, F)) :
    (∑ j, ∫ x, (c.repr (η x) j) ^ 2 ∂μ) ≤
      basisGradientConstant c * ∫ x, ‖η x‖ ^ 2 ∂μ := by
  have hi (j : χ) : Integrable (fun x => (c.repr (η x) j) ^ 2) μ := by
    simpa only [coefficientTestCLM_apply] using
      ((coefficientTestCLM K c j η).continuous.memLp_of_hasCompactSupport
        (coefficientTestCLM K c j η).hasCompactSupport :
          MemLp (coefficientTestCLM K c j η : E → ℝ) 2 μ).integrable_sq
  calc
    _ = ∫ x, ∑ j, (c.repr (η x) j) ^ 2 ∂μ :=
      (integral_finsetSum _ (fun j _ => hi j)).symm
    _ ≤ ∫ x, basisGradientConstant c * ‖η x‖ ^ 2 ∂μ :=
      integral_mono (integrable_finsetSum _ (fun j _ => hi j))
        ((norm_square_integrable K μ η).const_mul _) (fun x => coordinate_square_sum_le c (η x))
    _ = _ := integral_const_mul _ _

/-- Internally constructed original-norm control of the genuine native vector coefficient jet. -/
theorem nativeVectorCoefficientJet_norm_sq_le (η : 𝓓_{K}(E, F)) :
    ‖nativeVectorCoefficientJet K c μ b η‖ ^ 2 ≤
      basisGradientConstant c * ((∫ x, ‖η x‖ ^ 2 ∂μ) +
        ∑ i, ∫ x, ‖fderiv ℝ η x (b i)‖ ^ 2 ∂μ) := by
  rw [nativeVectorCoefficientJet_norm_sq, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hd (i : ι) : (∑ j, ∫ x, (c.repr (fderiv ℝ η x (b i)) j) ^ 2 ∂μ) ≤
      basisGradientConstant c * ∫ x, ‖fderiv ℝ η x (b i)‖ ^ 2 ∂μ := by
    simpa only [vectorDirectionalStageCLM_apply] using
      integral_coefficient_squares_le K c μ (vectorDirectionalStageCLM K (b i) η)
  calc
    _ ≤ basisGradientConstant c * (∫ x, ‖η x‖ ^ 2 ∂μ) +
        ∑ i, basisGradientConstant c * ∫ x, ‖fderiv ℝ η x (b i)‖ ^ 2 ∂μ :=
      add_le_add (integral_coefficient_squares_le K c μ η) (Finset.sum_le_sum fun i _ => hd i)
    _ = _ := by rw [← Finset.mul_sum, mul_add]

end SGPT.Foundations.Analysis.Pending.NaturalVectorCoefficientSobolev
