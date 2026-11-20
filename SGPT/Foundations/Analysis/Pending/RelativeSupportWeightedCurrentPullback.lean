import SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

set_option autoImplicit false

/-! # Genuine weighted pullbacks extended across a relative support

The complete mathematical blueprint and four entire proofs precede this file.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback BedfordTaylor

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {A B V : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

private theorem relative_support_locallyIntegrable
    {μ : Measure (ComplexModel n)} {f χ : ComplexModel n → ℝ}
    (hAV : A ≤ V) (hf : LocallyIntegrableOn f A μ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A) :
    LocallyIntegrableOn (fun x => χ x * f x) V μ := by
  have hA := hf.continuousOn_mul (hχ.mono hAV) A.isOpen.isLocallyClosed
  intro x hx
  by_cases hxA : x ∈ A
  · simpa only [nhdsWithin_eq_nhds.2 (A.isOpen.mem_nhds hxA),
      nhdsWithin_eq_nhds.2 (V.isOpen.mem_nhds hx)] using hA x hxA
  · have hxs : x ∉ tsupport χ := fun hs => hxA (hsupp ⟨hs, hx⟩)
    refine ⟨(tsupport χ)ᶜ,
      nhdsWithin_le_nhds ((isClosed_tsupport χ).isOpen_compl.mem_nhds hxs), ?_⟩
    refine (integrableOn_zero : IntegrableOn (fun _ : ComplexModel n => (0 : ℝ))
      (tsupport χ)ᶜ μ).congr ?_
    filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet.compl] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- A natural relative support internally supplies local integrability. -/
theorem locallyIntegrableOn_weighted_pbDensity
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => χ x * pbDensity A τ σ hT γ x) V (pbMeasure σ hT) :=
  relative_support_locallyIntegrable hAV (locallyIntegrableOn_pbDensity h hT γ) hχ hsupp

private theorem integrable_test_mul {μ : Measure (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : LocallyIntegrableOn f V μ) (φ : 𝓓(V, ℝ)) :
    Integrable (fun x => φ x * f x) μ := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hi := (hf.integrableOn_compact_subset φ.tsupport_subset hK).continuousOn_mul
    φ.continuous.continuousOn hK
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- The actual continuous distributions on the entire larger open set. -/
def weightedExtendedPullback
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A) :
    LocalProductCurrent n V q where
  toFun γ := regularDistribution (pbMeasure σ hT)
    (fun x => χ x * pbDensity A τ σ hT γ x)
    (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ)
  map_add' γ γ' := by
    ext φ
    rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply, ← integral_add
        (integrable_test_mul (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ) φ)
        (integrable_test_mul (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ') φ)]
    congr 1
    funext x
    rw [pbDensity_add]
    ring
  map_smul' c γ := by
    ext φ
    rw [RingHom.id_apply, _root_.smul_apply, regularDistribution_apply,
      regularDistribution_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [pbDensity_smul]
    ring

/-- Integrability and the genuine inverse-derivative formula are conclusions. -/
theorem weightedExtendedPullback_integral
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (γ : formSpan n q) (φ : 𝓓(V, ℝ)) :
    IntegrableOn (fun y => φ (σ y) * χ (σ y) *
      densityForm hT y (pullSpan q (fderiv ℂ σ y) γ)) B hT.traceMeasure ∧
    weightedExtendedPullback h hT hAV χ hχ hsupp γ φ =
      ∫ y in B, φ (σ y) * χ (σ y) *
        densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) ∂hT.traceMeasure := by
  have hi := integrable_test_mul
    (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ) φ
  have hb := (integrable_pbMeasure_iff h hT hi.aestronglyMeasurable).mp hi
  refine ⟨hb.congr_fun (fun y hy => ?_) B.isOpen.measurableSet, ?_⟩
  · change φ (σ y) * (χ (σ y) * pbDensity A τ σ hT γ (σ y)) = _
    rw [pbDensity_comp h hT γ hy]
    ring
  · change regularDistribution (pbMeasure σ hT)
      (fun x => χ x * pbDensity A τ σ hT γ x)
      (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ) φ = _
    rw [regularDistribution_apply, integral_pbMeasure h hT hi.aestronglyMeasurable]
    apply setIntegral_congr_fun B.isOpen.measurableSet
    intro y hy
    change φ (σ y) * (χ (σ y) * pbDensity A τ σ hT γ (σ y)) =
      φ (σ y) * χ (σ y) * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ)
    rw [pbDensity_comp h hT γ hy]
    ring

/-- A nonnegative weight preserves positivity on every variable test form. -/
theorem isPositive_weightedExtendedPullback
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (hχnonneg : ∀ x, 0 ≤ χ x) :
    IsPositive (weightedExtendedPullback h hT hAV χ hχ hsupp) := by
  intro ι _ γ φ hγ
  simp only [(weightedExtendedPullback_integral h hT hAV χ hχ hsupp _ _).2]
  rw [← integral_finsetSum _ fun i _ =>
    (weightedExtendedPullback_integral h hT hAV χ hχ hsupp (γ i) (φ i)).1]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_densityForm_nonneg hT)] with y hy
  have hmem : (∑ i, φ i (σ y) • γ i) ∈ posCone n q := by
    change ((∑ i, φ i (σ y) • γ i : formSpan n q) : RealForm n (2 * q)) ∈ spCone q
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hγ (σ y)
  have hp := hy _ (pullSpan_mem_posCone (fderiv ℂ σ y) hmem)
  simp only [map_sum, map_smul, smul_eq_mul] at hp
  have heq : (∑ i, φ i (σ y) * χ (σ y) *
      densityForm hT y (pullSpan q (fderiv ℂ σ y) (γ i))) =
      χ (σ y) * ∑ i, φ i (σ y) *
        densityForm hT y (pullSpan q (fderiv ℂ σ y) (γ i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  exact mul_nonneg (hχnonneg _) hp

end SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback
