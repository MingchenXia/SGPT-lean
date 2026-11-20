import SGPT.Foundations.Analysis.Pending.BidimensionOneFullTestFunctional
import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback

set_option autoImplicit false

/-! # Actual full test density of a relatively supported weighted pullback

The two complete mathematical statements and entire proofs precede this file.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.WeightedFullTestPullbackDensity

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorForms ClosedProductCurrents BidimensionOneFullTestFunctional
  RelativeSupportWeightedCurrentPullback LocalCurrentPullback BedfordTaylor

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {A B V : Opens (ComplexModel n)}

/-- The genuine span-valued canonical `(1,1)` projection of a real two-form. -/
def oneOneProjection (a : RealForm n 2) : formSpan n 1 :=
  ⟨pi11 a, oneOne_mem_formSpan (isOneOne_pi11 a)⟩

private def scalarTest (α : LocalCurrents.TestForm V 2)
    (i : Fin (Module.finrank ℝ (formSpan n 1))) : 𝓓(V, ℝ) :=
  TestFunction.postcompCLM ((coeffCLM n 1 i).comp (pi11CLM n)) α

private theorem projection_expansion (a : RealForm n 2) :
    oneOneProjection a = ∑ i, coeffCLM n 1 i (pi11 a) • formBasis n 1 i := by
  have hc (i : Fin (Module.finrank ℝ (formSpan n 1))) :
      coeffCLM n 1 i (pi11 a) = (formBasis n 1).repr (oneOneProjection a) i := by
    change (formBasis n 1).repr (formProj n 1 (oneOneProjection a : RealForm n 2)) i = _
    rw [formProj_coe]
  simp only [hc]
  exact ((formBasis n 1).sum_repr (oneOneProjection a)).symm

private theorem weighted_density_expansion
    {σ : ComplexModel n → ComplexModel n} {T : LocalProductCurrent n B 1}
    (hT : IsPositive T) (χ : ComplexModel n → ℝ)
    (α : LocalCurrents.TestForm V 2) (y : ComplexModel n) :
    (∑ i, scalarTest α i (σ y) * χ (σ y) *
      densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i))) =
      χ (σ y) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) := by
  rw [projection_expansion, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  change coeffCLM n 1 i (pi11 (α (σ y))) * χ (σ y) *
    densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i)) =
    χ (σ y) * (coeffCLM n 1 i (pi11 (α (σ y))) *
      densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i)))
  ring

/-- All genuine real two-form tests have the actual weighted inverse-density formula. -/
theorem fullTestFunctional_weightedExtendedPullback_density
    {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B 1}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (α : LocalCurrents.TestForm V 2) :
    IntegrableOn (fun y => χ (σ y) * densityForm hT y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y))))) B hT.traceMeasure ∧
    fullTestFunctional (weightedExtendedPullback h hT hAV χ hχ hsupp) α =
      ∫ y in B, χ (σ y) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) ∂hT.traceMeasure := by
  classical
  have hi (i : Fin (Module.finrank ℝ (formSpan n 1))) :=
    (weightedExtendedPullback_integral h hT hAV χ hχ hsupp
      (formBasis n 1 i) (scalarTest α i)).1
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
    (Eventually.of_forall (weighted_density_expansion hT χ α)), ?_⟩
  simp only [fullTestFunctional, _root_.sum_apply]
  change (∑ i, weightedExtendedPullback h hT hAV χ hχ hsupp
    (formBasis n 1 i) (scalarTest α i)) = _
  simp only [(weightedExtendedPullback_integral h hT hAV χ hχ hsupp _ _).2]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  exact integral_congr_ae (Eventually.of_forall (weighted_density_expansion hT χ α))

end SGPT.Foundations.Analysis.Pending.WeightedFullTestPullbackDensity
