import SGPT.Foundations.Analysis.Pending.DistributionRegularizationFinal

set_option autoImplicit false

/-! # Actual directional transport for smoothing arbitrary distributions

The full mathematical statements and entire proofs precede this source.
This supplies the derivative transport needed before smoothing arbitrary
closed distribution-valued forms. No density, Levi positivity or class is
presupposed, and no global current-potential theorem is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.DistributionRegularizationDirectionalTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

private theorem directionalKernel_test_eq
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z : E}
    (hz : z ∈ closure (D.inner : Set E)) (v : E) :
    TestFunction.ofSupportedIn D.cutoffCompact_subset
        (cutoffTranslatedKernelSupportedIn D.cutoff
          (translationDirectionalKernel (D.kernel j) v)
          (translationDirectionalKernel_contDiff (D.kernel j) (D.kernel_contDiff j) v)
          D.cutoffCompact (by rfl) z) =
      -TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
        (TestFunction.ofSupportedIn D.cutoffCompact_subset
          (D.localizedKernelSupportedIn j z)) := by
  let θ := TestFunction.ofSupportedIn D.cutoffCompact_subset
    (D.localizedKernelSupportedIn j z)
  have hθ : (θ : E → ℝ) = fun q => D.kernel j (q - z) := by
    funext q
    exact D.localizedKernelSupportedIn_eq_kernel j hz
  ext y
  change D.cutoff y * fderiv ℝ (D.kernel j) (y - z) (-v) =
    -(TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v θ) y
  rw [TestFunction.lineDerivCLM_apply]
  simp only [le_top, ↓reduceIte]
  rw [(θ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv,
    hθ, fderiv_comp_sub, map_neg]
  by_cases hy : y ∈ tsupport (fun q : E => D.kernel j (q - z))
  · rw [D.cutoff_one_on_compact y
      (D.translatedKernel_tsupport_subset_compact_for_smoothing j hz hy), one_mul]
  · have hzero := fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
    rw [fderiv_comp_sub] at hzero
    simp [hzero]

/-- Actual smoothing commutes with every distributional directional derivative
on the buffered inner domain, without a density or positivity assumption. -/
theorem fderiv_regularizedValue_eq
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ)) (j : ℕ)
    {z : E} (hz : z ∈ closure (D.inner : Set E)) (v : E) :
    fderiv ℝ (D.distributionRegularizedValue T j) z v =
      D.distributionRegularizedValue
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) j z := by
  have hχK : tsupport D.cutoff ⊆ (D.cutoffCompact : Set E) := by
    intro y hy
    exact hy
  have heq : D.distributionRegularizedValue T j =
      distributionCutoffTranslatedPairing T D.cutoff (D.kernel j)
        (D.kernel_contDiff j) D.cutoffCompact hχK D.cutoffCompact_subset := by
    funext q
    rfl
  rw [heq, fderiv_distributionCutoffTranslatedPairing_apply]
  change T (TestFunction.ofSupportedIn D.cutoffCompact_subset
    (cutoffTranslatedKernelSupportedIn D.cutoff
      (translationDirectionalKernel (D.kernel j) v)
      (translationDirectionalKernel_contDiff (D.kernel j) (D.kernel_contDiff j) v)
      D.cutoffCompact (by rfl) z)) = _
  rw [directionalKernel_test_eq D j hz v, map_neg]
  exact (Distribution.lineDerivCLM_apply).symm

private def regularizationLM (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    𝓓'(Ω, ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun T := D.distributionRegularizedValue T j
  map_add' T S := by
    funext z
    simp [AdaptedRadialKernelData.distributionRegularizedValue]
  map_smul' c T := by
    funext z
    simp [AdaptedRadialKernelData.distributionRegularizedValue]

/-- The original point and domain internally supply one common family of linear
smoothings, with actual derivative transport and all-test weak convergence. -/
theorem exists_local_linear_smoothing (μ : Measure E) [μ.IsAddHaarMeasure]
    {Ω : Opens E} {x : E} (hx : x ∈ Ω) :
    ∃ (U : Opens E) (_ : U ≤ Ω)
      (R : ℕ → (𝓓'(Ω, ℝ) →ₗ[ℝ] (E → ℝ))), x ∈ U ∧
      ∀ T : 𝓓'(Ω, ℝ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (R j T)) ∧
        (∀ j z, z ∈ U → ∀ v,
          fderiv ℝ (R j T) z v =
            R j (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) z) ∧
        (∀ φ : 𝓓(U, ℝ), Tendsto
          (fun j => ∫ z, φ z * R j T z ∂μ) atTop
          (𝓝 (T (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))))) := by
  let D : AdaptedRadialKernelData μ Ω x :=
    Classical.choice (exists_adaptedRadialKernelData μ hx)
  refine ⟨D.inner, D.inner_le, regularizationLM D, D.center_mem, ?_⟩
  intro T
  refine ⟨fun j => D.distributionRegularizedValue_contDiff T j, ?_, ?_⟩
  · intro j z hz v
    exact fderiv_regularizedValue_eq D T j (subset_closure hz) v
  · intro φ
    have hpairing := T.continuous.continuousAt.tendsto.comp
      (D.tendsto_ambientConvolutionTestFunction φ)
    refine hpairing.congr fun j => ?_
    exact (D.distribution_convolution_transpose T j φ).symm

end SGPT.Foundations.Analysis.Pending.DistributionRegularizationDirectionalTransport
