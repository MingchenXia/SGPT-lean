import SGPT.Foundations.Analysis.Pending.BorelSupportedCurrentPullback
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms

set_option autoImplicit false

/-! # Native Borel multiplication for positive relative-support weighted pullback
Full mathematical statement and entire proof precede this implementation. -/

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SupportedBorelNativeReconstruction
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback LocalBedfordTaylorLocality LocalBedfordTaylorForms
  RelativeSupportWeightedCurrentPullback BorelSupportedCurrentPullback BedfordTaylor

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan
variable {n q : ℕ} {A B V : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

/-- The weighted measure is finite on compact subsets of V because its
REAL density is locally integrable. No finiteness of the raw measure is used. -/
private theorem positive_weighted_measure_data
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (hχnonneg : ∀ x, 0 ≤ χ x) {γ : formSpan n q} (hγ : γ ∈ posCone n q) :
    let μ := pbMeasure σ hT
    let d := fun x => χ x * pbDensity A τ σ hT γ x
    let κ := (μ.restrict V).withDensity (fun x => ENNReal.ofReal (d x))
    IsLocalDensity (U := V) κ (fun _ => (1 : ℝ)) ∧
      ∀ w : ComplexModel n → ℝ,
        (∫ x, w x ∂κ) = ∫ x, d x * w x ∂(μ.restrict V) := by
  dsimp only
  let μ := pbMeasure σ hT
  let d := fun x => χ x * pbDensity A τ σ hT γ x
  let κ := (μ.restrict V).withDensity (fun x => ENNReal.ofReal (d x))
  have hd : LocallyIntegrableOn d V μ :=
    locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ
  have hdm : AEMeasurable (fun x => ENNReal.ofReal (d x)) (μ.restrict V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hd.aestronglyMeasurable.aemeasurable
  have hdp : ∀ᵐ x ∂μ, 0 ≤ d x :=
    (ae_pbDensity_nonneg h hT hγ).mono fun x hx => mul_nonneg (hχnonneg x) hx
  have hκV : κ ((V : Set (ComplexModel n))ᶜ) = 0 := by
    apply withDensity_absolutelyContinuous _ _
    rw [Measure.restrict_apply' V.isOpen.measurableSet]
    simp
  have hκK : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ V → κ K < ⊤ := by
    intro K hK hKV
    have hi := hd.integrableOn_compact_subset hKV hK
    change ((μ.restrict V).withDensity (fun x => ENNReal.ofReal (d x))) K < ⊤
    rw [withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict_of_subset hKV]
    exact (hasFiniteIntegral_iff_ofReal (ae_restrict_of_ae hdp)).mp hi.2
  refine ⟨⟨hκV, hκK, measurable_const,
    fun K _ _ => ⟨1, fun x _ => by simp⟩⟩, ?_⟩
  intro w
  rw [integral_withDensity_eq_integral_toReal_smul₀ hdm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hdp] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

/-- Positive coefficient forms suffice; the representation is entirely
internal and the scalar test remains genuine smooth φ. -/
private theorem positive_coefficient_borel_evaluation
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (hχnonneg : ∀ x, 0 ≤ χ x)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (φ : 𝓓(V, ℝ)) :
    borelWeightedExtendedPullback h hT hAV χ hχ hsupp f hf hb γ φ =
      mulBorel (weightedExtendedPullback h hT hAV χ hχ hsupp) f γ φ := by
  let μ := pbMeasure σ hT
  let d := fun x => χ x * pbDensity A τ σ hT γ x
  let κ := (μ.restrict V).withDensity (fun x => ENNReal.ofReal (d x))
  let W := weightedExtendedPullback h hT hAV χ hχ hsupp
  have hW : IsPositive W := isPositive_weightedExtendedPullback h hT hAV χ hχ hsupp hχnonneg
  obtain ⟨hκ, hκint⟩ := positive_weighted_measure_data h hT hAV χ hχ hsupp hχnonneg hγ
  have hrep : ∀ ψ : 𝓓(V, ℝ), W γ ψ = ∫ x, ψ x * (1 : ℝ) ∂κ := by
    intro ψ
    change regularDistribution μ d
      (locallyIntegrableOn_weighted_pbDensity h hT hAV χ hχ hsupp γ) ψ = _
    rw [regularDistribution_apply]
    simp only [mul_one]
    rw [hκint]
    calc
      (∫ x, ψ x * d x ∂μ) = ∫ x, ψ x * d x ∂(μ.restrict V) :=
        (integral_restrict_mul ψ μ d).symm
      _ = ∫ x, d x * ψ x ∂(μ.restrict V) :=
        integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hfb : IsLocallyBoundedOn f V := fun K _ _ => hb.imp fun C hC x _ => hC x
  have e := mulBorel_apply_of_integral_eq hW γ hκ hrep hf hfb φ
  change regularDistribution μ (fun x => f x * d x)
    (locallyIntegrableOn_borel_weighted_pbDensity h hT hAV χ hχ hsupp f hf hb γ) φ = _
  rw [regularDistribution_apply, e, hκint]
  simp only [mul_one]
  calc
    (∫ x, φ x * (f x * d x) ∂μ) = ∫ x, φ x * (f x * d x) ∂(μ.restrict V) :=
      (integral_restrict_mul φ μ (fun x => f x * d x)).symm
    _ = ∫ x, d x * (φ x * f x) ∂(μ.restrict V) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)

/-- Natural public producer: bounded Borel multiplication commutes with
this positive relatively supported extension on every coefficient form. -/
theorem borelWeightedExtendedPullback_eq_mulBorel
    (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) (hAV : A ≤ V) (χ : ComplexModel n → ℝ)
    (hχ : ContinuousOn χ V) (hsupp : tsupport χ ∩ (V : Set (ComplexModel n)) ⊆ A)
    (hχnonneg : ∀ x, 0 ≤ χ x)
    (f : ComplexModel n → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    borelWeightedExtendedPullback h hT hAV χ hχ hsupp f hf hb =
      mulBorel (weightedExtendedPullback h hT hAV χ hχ hsupp) f := by
  ext γ φ
  obtain ⟨C, _, hm, hp⟩ := exists_orderUnit γ.2
  let δ : formSpan n q := C • kahlerPower n q
  have hm' : δ - γ ∈ posCone n q := by
    change C • formPower (kahlerForm n) q - (γ : RealForm n (2 * q)) ∈ spCone q
    exact hm
  have hp' : δ + γ ∈ posCone n q := by
    change C • formPower (kahlerForm n) q + (γ : RealForm n (2 * q)) ∈ spCone q
    exact hp
  have em := positive_coefficient_borel_evaluation h hT hAV χ hχ hsupp hχnonneg f hf hb hm' φ
  have ep := positive_coefficient_borel_evaluation h hT hAV χ hχ hsupp hχnonneg f hf hb hp' φ
  simp only [map_sub, map_add, _root_.sub_apply, _root_.add_apply] at em ep
  linarith

end SGPT.Foundations.Analysis.Pending.SupportedBorelNativeReconstruction
