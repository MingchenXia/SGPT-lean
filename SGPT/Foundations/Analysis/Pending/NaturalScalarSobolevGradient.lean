import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevTranslation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Actual orthonormal scalar gradient and uniform first-jet translation bounds

All four complete mathematical proofs precede this source.
The genuine orthonormal basis uses the original inner-product-space norm.
-/

noncomputable section

open Set MeasureTheory Function TopologicalSpace
open scoped Distributions RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevGradient

open NaturalScalarSobolevJet NaturalScalarSobolevTranslation

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- Actual finite-coordinate square Cauchy--Schwarz for a real functional. -/
theorem linear_apply_square_le_gradient (L : E →L[ℝ] ℝ) (h : E) :
    (L h) ^ 2 ≤ ‖h‖ ^ 2 * ∑ j, (L (b j)) ^ 2 := by
  have hl : L h = ∑ j, ⟪b j, h⟫ * L (b j) := by
    nth_rw 1 [← b.sum_repr' h]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hl]
  simpa only [b.sum_sq_inner_right] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ⟪b j, h⟫) (fun j => L (b j))

variable (K : Compacts E)

/-- The true ordinary original-test directional differential obeys the basis gradient bound. -/
theorem directional_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (x h : E) :
    (fderiv ℝ f x h) ^ 2 ≤ ‖h‖ ^ 2 * ∑ j, (fderiv ℝ f x (b j)) ^ 2 :=
  linear_apply_square_le_gradient b (fderiv ℝ f x) h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
/-- Actual original compact directional tests have integrable scalar squares. -/
theorem directional_square_integrable (f : 𝓓_{K}(E, ℝ)) (h : E) :
    Integrable (fun x => (fderiv ℝ f x h) ^ 2) μ := by
  simp_rw [← directionalStageCLM_apply K h f]
  exact ((directionalStageCLM K h f).continuous.memLp_of_hasCompactSupport
    (directionalStageCLM K h f).hasCompactSupport :
      MemLp (directionalStageCLM K h f : E → ℝ) 2 μ).integrable_sq

omit [FiniteDimensional ℝ E] in
/-- Genuine real square-integral gradient inequality, with integrability supplied internally. -/
theorem integral_directional_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (fderiv ℝ f x h) ^ 2 ∂μ) ≤
      ‖h‖ ^ 2 * ∑ j, ∫ x, (fderiv ℝ f x (b j)) ^ 2 ∂μ := by
  have hi : Integrable (fun x => ∑ j, (fderiv ℝ f x (b j)) ^ 2) μ :=
    integrable_finsetSum _ fun j _ => directional_square_integrable K μ f (b j)
  calc
    _ ≤ ∫ x, ‖h‖ ^ 2 * ∑ j, (fderiv ℝ f x (b j)) ^ 2 ∂μ :=
      integral_mono (directional_square_integrable K μ f h) (hi.const_mul _)
        (fun x => directional_square_le_gradient b K f x h)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ =>
        directional_square_integrable K μ f (b j)]

/-- Whole actual translation square integral bounded by the finite native ON gradient energy. -/
theorem integral_translation_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
      ‖h‖ ^ 2 * ∑ j, ∫ x, (fderiv ℝ f x (b j)) ^ 2 ∂μ :=
  (integral_translation_square_le K μ f h).trans
    (integral_directional_square_le_gradient b K μ f h)

/-- The genuine uniform-rate translation inequality reads precisely the actual first-jet norm. -/
theorem integral_translation_square_le_firstJet (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
      ‖h‖ ^ 2 * ‖firstJetLinear μ K b f‖ ^ 2 := by
  apply (integral_translation_square_le_gradient b K μ f h).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖h‖)
  rw [firstJetLinear_norm_sq]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)

/-- One actual square error bound for every member of a native first-jet bounded family. -/
theorem uniform_translation_square_le (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K b f‖ ≤ R) (h : E) (f : 𝓓_{K}(E, ℝ))
    (hf : f ∈ A) : (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤ ‖h‖ ^ 2 * R ^ 2 := by
  apply (integral_translation_square_le_firstJet b K μ f h).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖h‖)
  exact (sq_le_sq₀ (norm_nonneg _) hR).2 (hA f hf)

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevGradient
