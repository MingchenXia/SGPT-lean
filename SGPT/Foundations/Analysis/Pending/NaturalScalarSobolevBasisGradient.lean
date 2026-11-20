import SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevTranslation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Original-norm scalar first-jet translation bounds for every finite linear basis

Four entire mathematical statements and proofs precede this source.
Coordinate operator norms are constructed internally; the original norm is retained.
-/

noncomputable section

open Set MeasureTheory Function TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisGradient

open NaturalScalarSobolevJet NaturalScalarSobolevTranslation

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (b : Module.Basis ι ℝ E)

/-- The original actual finite-basis coordinate functional, with its existing continuous structure. -/
def basisCoordinateCLM (j : ι) : E →L[ℝ] ℝ :=
  (b.coord j).toContinuousLinearMap

omit [Fintype ι] in
/-- The actual coordinate map reads exactly the original basis expansion coefficient. -/
theorem basisCoordinateCLM_apply (j : ι) (h : E) :
    basisCoordinateCLM b j h = b.repr h j := rfl

/-- Genuine finite comparison constant, using operator norms for the original norm. -/
def basisGradientConstant : ℝ := ∑ j, ‖basisCoordinateCLM b j‖ ^ 2

/-- Every actual coordinate comparison constant is nonnegative, including an empty basis. -/
theorem basisGradientConstant_nonneg : 0 ≤ basisGradientConstant b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Actual coordinate squares bounded in the original norm without orthonormality. -/
theorem coordinate_square_sum_le (h : E) :
    (∑ j, (b.repr h j) ^ 2) ≤ basisGradientConstant b * ‖h‖ ^ 2 := by
  calc
    _ ≤ ∑ j, ‖basisCoordinateCLM b j‖ ^ 2 * ‖h‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hs := (sq_le_sq₀ (norm_nonneg (basisCoordinateCLM b j h))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        ((basisCoordinateCLM b j).le_opNorm h)
      simpa only [basisCoordinateCLM_apply, Real.norm_eq_abs, sq_abs, mul_pow] using hs
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Actual finite-basis Cauchy--Schwarz with its internally constructed original-norm constant. -/
theorem linear_apply_square_le_gradient (L : E →L[ℝ] ℝ) (h : E) :
    (L h) ^ 2 ≤ basisGradientConstant b * ‖h‖ ^ 2 * ∑ j, (L (b j)) ^ 2 := by
  have hl : L h = ∑ j, b.repr h j * L (b j) := by
    nth_rw 1 [← b.sum_repr h]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hl]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => b.repr h j) (fun j => L (b j))).trans
      (mul_le_mul_of_nonneg_right (coordinate_square_sum_le b h)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))

variable (K : Compacts E)

/-- Pointwise specialization to the true ordinary directional differential of an original test. -/
theorem directional_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (x h : E) :
    (fderiv ℝ f x h) ^ 2 ≤ basisGradientConstant b * ‖h‖ ^ 2 *
      ∑ j, (fderiv ℝ f x (b j)) ^ 2 :=
  linear_apply_square_le_gradient b (fderiv ℝ f x) h

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
/-- Genuine compact smooth directional tests supply their own square integrability. -/
theorem directional_square_integrable (f : 𝓓_{K}(E, ℝ)) (h : E) :
    Integrable (fun x => (fderiv ℝ f x h) ^ 2) μ := by
  simp_rw [← directionalStageCLM_apply K h f]
  exact ((directionalStageCLM K h f).continuous.memLp_of_hasCompactSupport
    (directionalStageCLM K h f).hasCompactSupport :
      MemLp (directionalStageCLM K h f : E → ℝ) 2 μ).integrable_sq

/-- Whole-space actual square integrals obey the internally calibrated finite-basis estimate. -/
theorem integral_directional_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (fderiv ℝ f x h) ^ 2 ∂μ) ≤
      basisGradientConstant b * ‖h‖ ^ 2 * ∑ j, ∫ x, (fderiv ℝ f x (b j)) ^ 2 ∂μ := by
  have hi : Integrable (fun x => ∑ j, (fderiv ℝ f x (b j)) ^ 2) μ :=
    integrable_finsetSum _ fun j _ => directional_square_integrable K μ f (b j)
  calc
    _ ≤ ∫ x, basisGradientConstant b * ‖h‖ ^ 2 * ∑ j, (fderiv ℝ f x (b j)) ^ 2 ∂μ :=
      integral_mono (directional_square_integrable K μ f h) (hi.const_mul _)
        (fun x => directional_square_le_gradient b K f x h)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ =>
        directional_square_integrable K μ f (b j)]

/-- Original Haar translation square integral controlled by the genuine arbitrary-basis gradient. -/
theorem integral_translation_square_le_gradient (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
      basisGradientConstant b * ‖h‖ ^ 2 * ∑ j, ∫ x, (fderiv ℝ f x (b j)) ^ 2 ∂μ :=
  (integral_translation_square_le K μ f h).trans
    (integral_directional_square_le_gradient b K μ f h)

/-- Quantitative translation reads the literal original first-jet norm for the given basis. -/
theorem integral_translation_square_le_firstJet (f : 𝓓_{K}(E, ℝ)) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤
      basisGradientConstant b * ‖h‖ ^ 2 * ‖firstJetLinear μ K b f‖ ^ 2 := by
  apply (integral_translation_square_le_gradient b K μ f h).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (basisGradientConstant_nonneg b) (sq_nonneg ‖h‖))
  rw [firstJetLinear_norm_sq]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)

/-- One genuine uniform translation rate for every member of an original finite-basis jet-bounded family. -/
theorem uniform_translation_square_le (A : Set 𝓓_{K}(E, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ f ∈ A, ‖firstJetLinear μ K b f‖ ≤ R) (h : E)
    (f : 𝓓_{K}(E, ℝ)) (hf : f ∈ A) :
    (∫ x, (f (x + h) - f x) ^ 2 ∂μ) ≤ basisGradientConstant b * ‖h‖ ^ 2 * R ^ 2 := by
  apply (integral_translation_square_le_firstJet b K μ f h).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (basisGradientConstant_nonneg b) (sq_nonneg ‖h‖))
  exact (sq_le_sq₀ (norm_nonneg _) hR).2 (hA f hf)

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevBasisGradient
