import SGPT.Foundations.Analysis.Pending.WeightedFullTestPullbackDensity

set_option autoImplicit false

/-! # Actual restrictions tested with the original full trace density

The complete mathematical statements and entire proofs precede this file.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.RestrictedFullTestPullbackDensity

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality LocalBedfordTaylorForms
  LocalCurrentPullback BedfordTaylor
  BidimensionOneFullTestFunctional RelativeSupportWeightedCurrentPullback
  WeightedFullTestPullbackDensity

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {A B U V : Opens (ComplexModel n)}

/-- The actual restricted linear density agrees simultaneously on the whole span. -/
theorem densityForm_restrict_ae_all {T : LocalProductCurrent n U q}
    (hT : IsPositive T) (hBU : B ≤ U) :
    densityForm (isPositive_restrict hT hBU) =ᵐ[(isPositive_restrict hT hBU).traceMeasure]
      densityForm hT := by
  classical
  have hb : ∀ᵐ x ∂(isPositive_restrict hT hBU).traceMeasure,
      ∀ i : Fin (Module.finrank ℝ (formSpan n q)),
        densityForm (isPositive_restrict hT hBU) x (formBasis n q i) =
          densityForm hT x (formBasis n q i) :=
    ae_all_iff.mpr fun i => densityForm_restrict_ae hT hBU (formBasis n q i)
  filter_upwards [hb] with x hx
  ext γ
  rw [← (formBasis n q).sum_repr γ, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, hx i]

/-- The actual weighted restriction formula uses the original current's full density. -/
theorem fullTestFunctional_weighted_restriction_density
    {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n U 1}
    (hT : IsPositive T) (hBU : B ≤ U) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (α : LocalCurrents.TestForm V 2) :
    IntegrableOn (fun y => χ (σ y) * densityForm hT y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y))))) B hT.traceMeasure ∧
    fullTestFunctional
      (weightedExtendedPullback h (isPositive_restrict hT hBU) hAV χ hχ hsupp) α =
      ∫ y in B, χ (σ y) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) ∂hT.traceMeasure := by
  have hR := isPositive_restrict hT hBU
  have hk := fullTestFunctional_weightedExtendedPullback_density h hR hAV χ hχ hsupp α
  have hμ : hR.traceMeasure.restrict B = hT.traceMeasure.restrict B := by
    rw [traceMeasure_restrict hT hBU, Measure.restrict_restrict B.isOpen.measurableSet]
    simp only [inter_self]
  have hd := densityForm_restrict_ae_all hT hBU
  rw [traceMeasure_restrict hT hBU] at hd
  have hae : (fun y => χ (σ y) * densityForm hR y
      (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))))
      =ᵐ[hT.traceMeasure.restrict B] fun y => χ (σ y) * densityForm hT y
        (pullSpan 1 (fderiv ℂ σ y) (oneOneProjection (α (σ y)))) := by
    filter_upwards [hd] with y hy
    rw [hy]
  have hi := hk.1
  change Integrable _ (hR.traceMeasure.restrict B) at hi
  rw [hμ] at hi
  refine ⟨hi.congr hae, ?_⟩
  rw [hk.2]
  rw [hμ]
  exact integral_congr_ae hae

end SGPT.Foundations.Analysis.Pending.RestrictedFullTestPullbackDensity
