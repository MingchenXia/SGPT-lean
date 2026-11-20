import SGPT.Foundations.Analysis.Pending.BorelSupportedCurrentPullback
import SGPT.Foundations.Analysis.Pending.WeightedFullTestPullbackDensity
import SGPT.Foundations.Analysis.Pending.RestrictedFullTestPullbackDensity

set_option autoImplicit false

/-! # Full real test densities of an actual signed Borel supported pullback

The complete mathematical statements and entire proofs precede this file.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.BorelFullTestPullbackDensity
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalBedfordTaylorForms ClosedProductCurrents BidimensionOneFullTestFunctional
  BorelSupportedCurrentPullback LocalCurrentPullback BedfordTaylor
  WeightedFullTestPullbackDensity RestrictedFullTestPullbackDensity

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan
variable {n : ℕ} {A B U V : Opens (ComplexModel n)}

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

private theorem borel_density_expansion
    {σ : ComplexModel n → ComplexModel n} {T : LocalProductCurrent n B 1}
    (hT : IsPositive T) (f χ : ComplexModel n → ℝ)
    (α : LocalCurrents.TestForm V 2) (y : ComplexModel n) :
    (∑ i, scalarTest α i (σ y) * f (σ y) * χ (σ y) *
      densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i))) =
      (f (σ y) * χ (σ y)) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) := by
  rw [projection_expansion, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  change coeffCLM n 1 i (pi11 (α (σ y))) * f (σ y) * χ (σ y) *
    densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i)) =
    (f (σ y) * χ (σ y)) * (coeffCLM n 1 i (pi11 (α (σ y))) *
      densityForm hT y (pullSpan 1 (fderiv ℂ σ y) (formBasis n 1 i)))
  ring

theorem fullTestFunctional_borelWeightedExtendedPullback_density
    {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B 1}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (α : LocalCurrents.TestForm V 2) :
    IntegrableOn (fun y => (f (σ y) * χ (σ y)) * densityForm hT y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y))))) B hT.traceMeasure ∧
    fullTestFunctional (borelWeightedExtendedPullback h hT hAV χ hχ hsupp f hf hb) α =
      ∫ y in B, (f (σ y) * χ (σ y)) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) ∂hT.traceMeasure := by
  classical
  have hi (i : Fin (Module.finrank ℝ (formSpan n 1))) :=
    (borelWeightedExtendedPullback_integral h hT hAV χ hχ hsupp f hf hb
      (formBasis n 1 i) (scalarTest α i)).1
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
    (Eventually.of_forall (borel_density_expansion hT f χ α)), ?_⟩
  simp only [fullTestFunctional, _root_.sum_apply]
  change (∑ i, borelWeightedExtendedPullback h hT hAV χ hχ hsupp f hf hb
    (formBasis n 1 i) (scalarTest α i)) = _
  simp only [(borelWeightedExtendedPullback_integral h hT hAV χ hχ hsupp f hf hb _ _).2]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  exact integral_congr_ae (Eventually.of_forall (borel_density_expansion hT f χ α))

theorem fullTestFunctional_borelWeighted_restriction_density
    {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n U 1}
    (hT : IsPositive T) (hBU : B ≤ U) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (α : LocalCurrents.TestForm V 2) :
    IntegrableOn (fun y => (f (σ y) * χ (σ y)) * densityForm hT y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y))))) B hT.traceMeasure ∧
    fullTestFunctional
      (borelWeightedExtendedPullback h (isPositive_restrict hT hBU) hAV χ hχ hsupp f hf hb) α =
      ∫ y in B, (f (σ y) * χ (σ y)) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) ∂hT.traceMeasure := by
  have hR := isPositive_restrict hT hBU
  have hk := fullTestFunctional_borelWeightedExtendedPullback_density h hR hAV χ hχ hsupp f hf hb α
  have hμ : hR.traceMeasure.restrict B = hT.traceMeasure.restrict B := by
    rw [traceMeasure_restrict hT hBU, Measure.restrict_restrict B.isOpen.measurableSet]
    simp only [inter_self]
  have hd := densityForm_restrict_ae_all hT hBU
  rw [traceMeasure_restrict hT hBU] at hd
  have hae : (fun y => (f (σ y) * χ (σ y)) * densityForm hR y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))))
      =ᵐ[hT.traceMeasure.restrict B] fun y => (f (σ y) * χ (σ y)) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) := by
    filter_upwards [hd] with y hy
    rw [hy]
  have hi := hk.1
  change Integrable _ (hR.traceMeasure.restrict B) at hi
  rw [hμ] at hi
  refine ⟨hi.congr hae, ?_⟩
  rw [hk.2, hμ]
  exact integral_congr_ae hae

end SGPT.Foundations.Analysis.Pending.BorelFullTestPullbackDensity
