import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisRellich

/-! # Genuine finite-coefficient Hilbert Rellich embedding

Four entire mathematical statements and proofs precede this source.
The coefficient Hilbert products are explicit copies; every original model norm is kept.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace ContinuousLinearMap Metric
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalCoefficientSobolevRellich

open NaturalScalarSobolevJet NaturalScalarSobolevBasisRellich

variable {E : Type*} [MeasurableSpace E] (μ : Measure E)

/-- The literal finite Hilbert product of original real scalar L2 classes. -/
abbrev CoefficientL2 (χ : Type*) := PiLp 2 (fun _ : χ => Lp ℝ 2 μ)

variable {χ : Type*} [Fintype χ]

/-- Actual single-coordinate inclusion in the genuine finite L2 Hilbert product. -/
def coefficientSingleCLM (j : χ) : Lp ℝ 2 μ →L[ℝ] CoefficientL2 μ χ := by
  classical
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : χ => Lp ℝ 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : χ => Lp ℝ 2 μ) j)

omit [Fintype χ] in
/-- Exact original scalar coordinate readback of the actual single-coordinate inclusion. -/
theorem coefficientSingleCLM_apply [DecidableEq χ] (j : χ) (v : Lp ℝ 2 μ) (i : χ) :
    coefficientSingleCLM μ j v i = (Pi.single j v : χ → Lp ℝ 2 μ) i := by
  classical
  by_cases h : i = j
  · subst i
    simp [coefficientSingleCLM]
  · simp [coefficientSingleCLM, h]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [μ.IsAddHaarMeasure] (K : Compacts E)
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)

/-- Genuine finite Hilbert product of the original closed scalar first-jet spaces. -/
abbrev CoefficientJetHilbert (χ : Type*) := PiLp 2 (fun _ : χ => SobolevFirstJet μ K b)

/-- Literal finite sum of original scalar compact value maps and actual coordinate inclusions. -/
def coefficientValueCLM : CoefficientJetHilbert μ K b χ →L[ℝ] CoefficientL2 μ χ :=
  ∑ j, (coefficientSingleCLM μ j).comp ((jetCoordinateCLM μ K b (Sum.inl ())).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : χ => SobolevFirstJet μ K b) j))

/-- The actual coefficient map reads precisely the original scalar value in every coordinate. -/
theorem coefficientValueCLM_apply (a : CoefficientJetHilbert μ K b χ) (j : χ) :
    coefficientValueCLM μ K b a j = jetCoordinateCLM μ K b (Sum.inl ()) (a j) := by
  classical
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : χ => Lp ℝ 2 μ) j)
    ((∑ i, (coefficientSingleCLM μ i).comp ((jetCoordinateCLM μ K b (Sum.inl ())).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : χ => SobolevFirstJet μ K b) i))) a) = _
  rw [sum_apply, map_sum]
  simp [coefficientSingleCLM_apply, Pi.single_apply]

/-- Actual native finite-coefficient jets in their own constructed closed Hilbert ranges. -/
def nativeCoefficientJet (f : χ → 𝓓_{K}(E, ℝ)) : CoefficientJetHilbert μ K b χ :=
  WithLp.toLp 2 (fun j => toSobolevFirstJet μ K b (f j))

omit [Fintype χ] in
/-- Native coordinate identity with the exact original scalar first jet. -/
theorem nativeCoefficientJet_apply (f : χ → 𝓓_{K}(E, ℝ)) (j : χ) :
    nativeCoefficientJet μ K b f j = toSobolevFirstJet μ K b (f j) := rfl

/-- The literal original native coefficient first-jet Hilbert norm has its actual integral formula. -/
theorem nativeCoefficientJet_norm_sq (f : χ → 𝓓_{K}(E, ℝ)) :
    ‖nativeCoefficientJet μ K b f‖ ^ 2 =
      ∑ j, ((∫ x, (f j) x ^ 2 ∂μ) + ∑ i, ∫ x, (fderiv ℝ (f j) x (b i)) ^ 2 ∂μ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  change ‖firstJetLinear μ K b (f j)‖ ^ 2 = _
  exact firstJetLinear_norm_sq μ K b (f j)

/-- Actual scalar L2 readback on every original native coefficient. -/
theorem coefficientValueCLM_apply_native (f : χ → 𝓓_{K}(E, ℝ)) (j : χ) :
    coefficientValueCLM μ K b (nativeCoefficientJet μ K b f) j = scalarStageL2 μ K (f j) := by
  rw [coefficientValueCLM_apply, nativeCoefficientJet_apply,
    jetCoordinateCLM_apply_native, firstJetLinear_value]

/-- Exact original whole-Haar value squared norm, with genuine scalar L2 classes. -/
theorem coefficientValueCLM_norm_sq_native (f : χ → 𝓓_{K}(E, ℝ)) :
    ‖coefficientValueCLM μ K b (nativeCoefficientJet μ K b f)‖ ^ 2 =
      ∑ j, ∫ x, (f j) x ^ 2 ∂μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficientValueCLM_apply_native, scalarStageL2_norm_sq]

/-- The actual finite-coefficient value inclusion is contractive in the literal Hilbert product norms. -/
theorem coefficientValueCLM_norm_le (a : CoefficientJetHilbert μ K b χ) :
    ‖coefficientValueCLM μ K b a‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  rw [coefficientValueCLM_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (jetCoordinateCLM_norm_le μ K b (Sum.inl ()) (a j))

/-- Genuine finite-coefficient Rellich compactness from the internally proved original scalar operator. -/
theorem isCompactOperator_coefficientValue : IsCompactOperator (coefficientValueCLM μ K b (χ := χ)) := by
  change (∑ j, (coefficientSingleCLM μ j).comp ((jetCoordinateCLM μ K b (Sum.inl ())).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : χ => SobolevFirstJet μ K b) j))) ∈
      compactOperator (RingHom.id ℝ) (CoefficientJetHilbert μ K b χ) (CoefficientL2 μ χ)
  apply Submodule.sum_mem
  intro j _
  exact ((isCompactOperator_value μ K b).comp_clm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : χ => SobolevFirstJet μ K b) j)).clm_comp
      (coefficientSingleCLM μ j)

/-- Compact closure of the actual coefficient value image of every original closed ball. -/
theorem isCompact_coefficientValue_image_closedBall_closure (R : ℝ) :
    IsCompact (closure (coefficientValueCLM μ K b (χ := χ) ''
      closedBall (0 : CoefficientJetHilbert μ K b χ) R)) := by
  have h : IsCompactOperator (coefficientValueCLM μ K b (χ := χ)).toLinearMap :=
    isCompactOperator_coefficientValue μ K b
  exact h.isCompact_closure_image_closedBall R

end SGPT.Foundations.Analysis.Pending.NaturalCoefficientSobolevRellich
