import SGPT.Foundations.Analysis.Pending.DistributionRegularizationDirectionalTransport
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false

/-! # Genuine regularization of distribution-valued forms

All coefficients of an arbitrary distribution form use one actual adapted
kernel. The resulting continuous alternating-form-valued map is genuinely
smooth, and its actual exterior derivative equals the regularization of the
original distributional exterior derivative on the buffered inner domain.
Reference: Demailly, CADG I.2.D.3, with actual cutoff and derivative transport.
No cohomology comparison or distributional Poincare theorem is presupposed.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology
open SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.Pending.DistributionFormRegularization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

private def kernelEvaluationLM (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) (z : E) : 𝓓'(Ω, ℝ) →ₗ[ℝ] ℝ where
  toFun T := D.distributionRegularizedValue T j z
  map_add' T S := by simp [AdaptedRadialKernelData.distributionRegularizedValue]
  map_smul' c T := by simp [AdaptedRadialKernelData.distributionRegularizedValue]

/-- Every original distribution coefficient is smoothed by the same kernel,
with actual continuous alternating forms as values. -/
def regularizedForm (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) {k : ℕ} (A : DistributionForm Ω k) (z : E) :
    E [⋀^Fin k]→L[ℝ] ℝ := by
  let f := (kernelEvaluationLM D j z).compAlternatingMap A
  refine { f with cont := ?_ }
  have h := (multilinearMapToContinuousOfFiniteDimensional f.toMultilinearMap).cont
  convert h using 1
  funext v
  exact (multilinearMapToContinuousOfFiniteDimensional_apply f.toMultilinearMap v).symm

private theorem regularizedForm_apply (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) {k : ℕ} (A : DistributionForm Ω k) (z : E) (v : Fin k → E) :
    regularizedForm D j A z v = D.distributionRegularizedValue (A v) j z := rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_form_of_coefficients {k : ℕ}
    (form : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (h : ∀ v : Fin k → E, ContDiff ℝ (⊤ : ℕ∞) (fun z => form z v)) :
    ContDiff ℝ (⊤ : ℕ∞) form := by
  let b := Module.finBasis ℝ E
  let Q : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
      ((Fin k → Fin (Module.finrank ℝ E)) → ℝ) :=
    { toFun f := fun I => f (fun i => b (I i))
      map_add' f g := by rfl
      map_smul' c f := by rfl }
  have hQ : Function.Injective Q := by
    intro f g hfg
    apply DFunLike.coe_injective
    have heq : f.toAlternatingMap = g.toAlternatingMap := by
      apply b.ext_alternating
      intro I _
      exact congrFun hfg I
    funext v
    exact DFunLike.congr_fun heq v
  obtain ⟨L, hL⟩ := Q.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hQ)
  have harray : ContDiff ℝ (⊤ : ℕ∞) (fun z => Q (form z)) :=
    contDiff_pi.mpr fun I => h (fun i => b (I i))
  have hresult := L.toContinuousLinearMap.contDiff.comp harray
  convert hresult using 1
  funext z
  exact (LinearMap.congr_fun hL (form z)).symm

/-- Smoothness holds in the actual normed space of continuous alternating forms,
not only for each separate coefficient. -/
theorem contDiff_regularizedForm (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) {k : ℕ} (A : DistributionForm Ω k) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedForm D j A) := by
  apply contDiff_form_of_coefficients
  intro v
  exact D.distributionRegularizedValue_contDiff (A v) j

/-- The ordinary exterior derivative of the genuine smooth form is the
regularization of the actual distributional exterior derivative. -/
theorem extDeriv_regularizedForm_eq (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) {k : ℕ} (A : DistributionForm Ω k) {z : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    extDeriv (regularizedForm D j A) z =
      regularizedForm D j (exteriorDerivative A) z := by
  ext v
  rw [extDeriv_apply ((contDiff_regularizedForm D j A).differentiable (by simp) z)]
  calc
    _ = ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
        D.distributionRegularizedValue
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v i)
            (A (i.removeNth v))) j z := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact DistributionRegularizationDirectionalTransport.fderiv_regularizedValue_eq
        D (A (i.removeNth v)) j hz (v i)
    _ = regularizedForm D j (exteriorDerivative A) z v := by
      rw [regularizedForm_apply, exteriorDerivative_apply]
      change _ = kernelEvaluationLM D j z _
      simp only [map_sum, map_zsmul]
      rfl

private def regularizationLM (D : AdaptedRadialKernelData μ Ω x)
    (k j : ℕ) : DistributionForm Ω k →ₗ[ℝ] (E → E [⋀^Fin k]→L[ℝ] ℝ) where
  toFun A := regularizedForm D j A
  map_add' A B := by
    funext z
    ext v
    simp [regularizedForm_apply, AdaptedRadialKernelData.distributionRegularizedValue]
  map_smul' c A := by
    funext z
    ext v
    simp [regularizedForm_apply, AdaptedRadialKernelData.distributionRegularizedValue]

/-- The original point internally supplies smooth linear regularizations for
all degrees and forms, preserving actual closedness, type, scalar-test
constant-direction positivity and all-coefficient all-test weak limits. -/
theorem exists_local_regularization (μ : Measure E) [μ.IsAddHaarMeasure]
    {Ω : Opens E} {x : E} (hx : x ∈ Ω) :
    ∃ (U : Opens E) (_ : U ≤ Ω)
      (R : (k : ℕ) → ℕ → (DistributionForm Ω k →ₗ[ℝ]
        (E → E [⋀^Fin k]→L[ℝ] ℝ))), x ∈ U ∧
      (∀ k (A : DistributionForm Ω k),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (R k j A)) ∧
        (∀ j z, z ∈ U → extDeriv (R k j A) z =
          R (k + 1) j (exteriorDerivative A) z) ∧
        (∀ v : Fin k → E, ∀ φ : 𝓓(U, ℝ), Tendsto
          (fun j => ∫ z, φ z * R k j A z v ∂μ) atTop
          (𝓝 ((A v) (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))))) ∧
        (IsClosed A → ∀ j z, z ∈ U → extDeriv (R k j A) z = 0)) ∧
      (∀ A : DistributionForm Ω 2, IsOneOne A →
        ∀ j z v w, R 2 j A z ![Complex.I • v, Complex.I • w] =
          R 2 j A z ![v, w]) ∧
      (∀ A : DistributionForm Ω 2, ConstantDirectionPositive A →
        ∀ j z v, 0 ≤ R 2 j A z ![v, Complex.I • v]) := by
  let D : AdaptedRadialKernelData μ Ω x :=
    Classical.choice (exists_adaptedRadialKernelData μ hx)
  refine ⟨D.inner, D.inner_le, regularizationLM D, D.center_mem, ?_, ?_, ?_⟩
  · intro k A
    refine ⟨fun j => contDiff_regularizedForm D j A, ?_, ?_, ?_⟩
    · intro j z hz
      exact extDeriv_regularizedForm_eq D j A (subset_closure hz)
    · intro v φ
      have hpairing := (A v).continuous.continuousAt.tendsto.comp
        (D.tendsto_ambientConvolutionTestFunction φ)
      refine hpairing.congr fun j => ?_
      exact (D.distribution_convolution_transpose (A v) j φ).symm
    · intro hclosed j z hz
      change extDeriv (regularizedForm D j A) z = 0
      rw [extDeriv_regularizedForm_eq D j A (subset_closure hz), hclosed]
      ext v
      simp [regularizedForm_apply, AdaptedRadialKernelData.distributionRegularizedValue]
  · intro A htype j z v w
    change D.distributionRegularizedValue (A ![Complex.I • v, Complex.I • w]) j z =
      D.distributionRegularizedValue (A ![v, w]) j z
    rw [htype v w]
  · intro A hpositive j z v
    apply hpositive v
    intro y
    change 0 ≤ D.cutoff y * D.kernel j (y - z)
    exact mul_nonneg (D.cutoff_mem_Icc y).1 (D.kernel_nonneg j (y - z))

end SGPT.Foundations.Analysis.Pending.DistributionFormRegularization
