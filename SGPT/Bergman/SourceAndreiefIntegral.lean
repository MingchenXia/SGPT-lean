import SGPT.Bergman.SourceAndreiefExpansion
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.Andreief
open Set MeasureTheory
open scoped BigOperators ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

/-- The actual Gram matrix obtained by integrating the scalar pairings. -/
def integralGram (μ : Measure K) (f : ι → K → ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, conj (f i x) * f j x ∂μ

omit [CompactSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Continuity of actual determinant density follows solely from genuine
pair continuity. Individual preferred-frame coordinate functions are NOT
assumed continuous or measurable. -/
theorem squaredEvaluationDet_continuous (f : ι → K → ℂ)
    (hpair : ∀ i j, Continuous (fun x => conj (f i x) * f j x)) :
    Continuous (squaredEvaluationDet f) := by
  have hp (σ τ : Equiv.Perm ι) : Continuous (fun x : ι → K =>
      ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j)) :=
    continuous_finsetProd _ (fun j _ => (hpair (σ j) (τ j)).comp (continuous_apply j))
  have hc : Continuous (fun x : ι → K =>
      ∑ σ : Equiv.Perm ι, ∑ τ : Equiv.Perm ι,
        permutationSign σ * permutationSign τ *
          ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j)) :=
    continuous_finsetSum _ (fun σ _ => continuous_finsetSum _
      (fun τ _ => continuous_const.mul (hp σ τ)))
  exact (Complex.continuous_re.comp hc).congr (fun x => by
    dsimp only [Function.comp_apply]
    rw [← ofReal_squaredEvaluationDet]
    rfl)

/-- Genuine Andreief identity: finite-product Fubini integrates the actual
determinant density to factorial times the actual Gram determinant. -/
theorem integral_squaredEvaluationDet (μ : Measure K) [IsFiniteMeasure μ]
    (f : ι → K → ℂ)
    (hpair : ∀ i j, Continuous (fun x => conj (f i x) * f j x)) :
    (∫ x : ι → K, squaredEvaluationDet f x ∂Measure.pi (fun _ : ι => μ)) =
      ((Fintype.card ι).factorial : ℝ) * (integralGram μ f).det.re := by
  let ν := Measure.pi (fun _ : ι => μ)
  have hp (σ τ : Equiv.Perm ι) : Integrable (fun x : ι → K =>
      ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j)) ν :=
    (continuous_finsetProd _ (fun j _ => (hpair (σ j) (τ j)).comp
      (continuous_apply j))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hscaled (σ τ : Equiv.Perm ι) : Integrable (fun x : ι → K =>
      permutationSign σ * permutationSign τ *
        ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j)) ν :=
    (hp σ τ).const_mul _
  have hprod (σ τ : Equiv.Perm ι) :
      (∫ x : ι → K, ∏ j, conj (f (σ j) (x j)) * f (τ j) (x j) ∂ν) =
        ∏ j, ∫ x : K, conj (f (σ j) x) * f (τ j) x ∂μ := by
    simpa only [ν] using! (integral_fintype_prod_eq_prod
      (fun j (x : K) => conj (f (σ j) x) * f (τ j) x) (μ := fun _ : ι => μ))
  have hc : Complex.ofReal (∫ x : ι → K, squaredEvaluationDet f x ∂ν) =
      (((Fintype.card ι).factorial : ℂ) * (integralGram μ f).det) := by
    rw [← integral_complex_ofReal]
    simp_rw [ofReal_squaredEvaluationDet]
    rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hscaled σ τ))]
    simp_rw [integral_finsetSum _ (fun τ _ => hscaled _ τ)]
    simp only [integral_const_mul]
    simp_rw [hprod]
    exact double_perm_pair_sum (integralGram μ f)
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] using hr

end SGPT.Bergman.Andreief
