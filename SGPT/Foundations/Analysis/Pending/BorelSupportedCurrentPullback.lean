import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCurrentPullback

set_option autoImplicit false

/-! # Signed Borel coefficients in a genuine supported pullback

The complete mathematical statements and entire proofs precede this file.
-/

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.BorelSupportedCurrentPullback

open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback RelativeSupportWeightedCurrentPullback BedfordTaylor

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {A B V : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

private theorem locallyIntegrableOn_bounded_mul
    {μ : Measure (ComplexModel n)} {g f : ComplexModel n → ℝ}
    (hg : LocallyIntegrableOn g V μ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    LocallyIntegrableOn (fun x => f x * g x) V μ := by
  obtain ⟨C, hC⟩ := hb
  intro x hx
  obtain ⟨s, hs, hi⟩ := hg x hx
  refine ⟨s, hs, hi.bdd_mul (c := C) hf.aestronglyMeasurable.restrict ?_⟩
  exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC y

/-- A bounded signed Borel multiplier preserves the genuine relative-support density. -/
theorem locallyIntegrableOn_borel_weighted_pbDensity
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => f x * (χ x * pbDensity A τ σ hT γ x))
      V (pbMeasure σ hT) :=
  locallyIntegrableOn_bounded_mul
    (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ) hf hb

private theorem integrable_test_mul {μ : Measure (ComplexModel n)}
    {g : ComplexModel n → ℝ} (hg : LocallyIntegrableOn g V μ) (φ : 𝓓(V, ℝ)) :
    Integrable (fun x => φ x * g x) μ := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hi := (hg.integrableOn_compact_subset φ.tsupport_subset hK).continuousOn_mul
    φ.continuous.continuousOn hK
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- The actual signed current on the entire larger open set. -/
def borelWeightedExtendedPullback
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) : LocalProductCurrent n V q where
  toFun γ := regularDistribution (pbMeasure σ hT)
    (fun x => f x * (χ x * pbDensity A τ σ hT γ x))
    (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ)
  map_add' γ γ' := by
    ext φ
    rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply, ← integral_add
        (integrable_test_mul
          (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ) φ)
        (integrable_test_mul
          (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ') φ)]
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

/-- Integrability and the true inverse-derivative evaluation follow from the original data. -/
theorem borelWeightedExtendedPullback_integral
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) (γ : formSpan n q) (φ : 𝓓(V, ℝ)) :
    IntegrableOn (fun y => φ (σ y) * f (σ y) * χ (σ y) *
      densityForm hT y (pullSpan q (fderiv ℂ σ y) γ)) B hT.traceMeasure ∧
    borelWeightedExtendedPullback h hT hAV χ hχ hsupp f hf hb γ φ =
      ∫ y in B, φ (σ y) * f (σ y) * χ (σ y) *
        densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) ∂hT.traceMeasure := by
  have hi := integrable_test_mul
    (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ) φ
  have hiB := (integrable_pbMeasure_iff h hT hi.aestronglyMeasurable).mp hi
  refine ⟨hiB.congr_fun (fun y hy => ?_) B.isOpen.measurableSet, ?_⟩
  · change φ (σ y) * (f (σ y) * (χ (σ y) * pbDensity A τ σ hT γ (σ y))) = _
    rw [pbDensity_comp h hT γ hy]
    ring
  · change regularDistribution (pbMeasure σ hT)
      (fun x => f x * (χ x * pbDensity A τ σ hT γ x))
      (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ) φ = _
    rw [regularDistribution_apply, integral_pbMeasure h hT hi.aestronglyMeasurable]
    apply setIntegral_congr_fun B.isOpen.measurableSet
    intro y hy
    change φ (σ y) * (f (σ y) * (χ (σ y) * pbDensity A τ σ hT γ (σ y))) = _
    rw [pbDensity_comp h hT γ hy]
    ring

end SGPT.Foundations.Analysis.Pending.BorelSupportedCurrentPullback
