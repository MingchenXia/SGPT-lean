import SGPT.Bergman.SourcePartialWeightTranslations
import SGPT.Bergman.SourcePartialEnergyMeasureData
import SGPT.Bergman.SourceUniformTranslateMAContinuity
import SGPT.Bergman.SourcePartialEnergyCalculus

/-! Differentiability of real partial equilibrium energy along continuous weights on a closed subset. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PartialEnergyDifferentiability

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The actual original RHS integral is genuinely integrable on the SAME
closed subtype; finite measure and compact-subtype bounds are produced. -/
theorem partialIEnvelope_subtype_integrable (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (w f : C(K, ℝ)) :
    Integrable (fun x : K => f x)
      ((sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun y => (w y : EReal)))
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w).1).comap Subtype.val) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  let μ := sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun y => (w y : EReal)))
    (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w).1
  let : IsFiniteMeasure μ := sourcePotentialMeasure_finite ω
    (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w).1
  change Integrable (fun x : K => f x) (μ.comap Subtype.val)
  simpa only [integrableOn_univ] using
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ f.continuous.continuousOn

/-- WHOLE ORIGINAL prop:differential_P at EVERY real point, for ALL actual
continuous original subtype weights/directions and a genuine positive phi.
The derivative is the integral against the ACTUAL partial-I MA measure,
using its exact original subtype comap. No I-good hypothesis is introduced. -/
theorem partialEquilibriumEnergy_hasDerivAt (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v f : C(K, ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => partialEquilibriumEnergy ω hφ hφpos hKc hK (v + s • f))
      (∫ x : K, f x ∂(sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ K (fun y => ((v + t • f) y : EReal)))
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK (v + t • f)).1).comap Subtype.val) t := by
  let U : ℝ → M → EReal := fun s => partialIEnvelope θ φ K (fun x => (affineWeight v f s x : EReal))
  let hU : ∀ s, (ofFixedModel n M).IsThetaPSH θ (U s) :=
    fun s => (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK (affineWeight v f s)).1
  let μ : ℝ → Measure M := fun s => sourcePotentialNonPluripolarMeasure θ (U s) (hU s)
  let E : ℝ → ℝ := fun s => partialEquilibriumEnergy ω hφ hφpos hKc hK (affineWeight v f s)
  let I : ℝ → ℝ := fun s => ∫ x : K, f x ∂(μ s).comap Subtype.val
  have hinfty (s) := partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK (affineWeight v f s)
  have hfinite (s) := partialIEnvelope_finiteEnergy_continuous ω hφ hφpos hKc hK (affineWeight v f s)
  have hcontact (s) : ∀ᵐ x ∂μ s, ∃ hx : x ∈ K, U s x = (affineWeight v f s ⟨x, hx⟩ : EReal) :=
    partialIEnvelope_continuous_contact_ae ω hφ hφpos hKc hK (affineWeight v f s)
  have hout (s) : μ s Kᶜ = 0 := by
    have hmem : ∀ᵐ x ∂μ s, x ∈ K := (hcontact s).mono fun _ hx => hx.choose
    exact ae_iff.mp hmem
  obtain ⟨F, hF, hread⟩ := exists_continuous_extension_integral hKc f
  have hreadI (s) : I s = ∫ x, F x ∂μ s := hread (μ s) (hout s)
  have hFval (x : K) : F x.val = f x := by
    exact congrArg (fun g : C(K, ℝ) => g x) hF
  obtain ⟨R, _hRnonneg, hsand⟩ := partialI_affineWeight_translate_control hφ hKc hK v f
  have hmass (s r) : μ r univ = μ s univ :=
    partialIEnvelope_continuous_mass_eq ω hφ hφpos hKc hK (affineWeight v f s) (affineWeight v f r)
  have hIcontinuous : Continuous I := by
    have heq : I = fun s => ∫ x, F x ∂μ s := funext hreadI
    rw [heq]
    exact continuous_integral_of_translate_control ω hU R hsand hmass F.continuous
  have hFint (s) : Integrable (fun x => F x) (μ s) := by
    let : IsFiniteMeasure (μ s) := sourcePotentialMeasure_finite ω (hU s)
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ F.continuous.continuousOn
  have hpole (s r) : ∀ᵐ x ∂μ r, U s x ≠ ⊥ := by
    apply ae_iff.mpr
    have h := sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hU r) (hU s)
    simpa only [not_not, sourceMixedNonPluripolarMeasure_diagonal] using h
  have hobstacle (s r) : ∀ᵐ x ∂μ r, ∀ hx : x ∈ K, U s x ≤ (affineWeight v f s ⟨x, hx⟩ : EReal) :=
    partialIEnvelope_continuous_obstacle_ae ω (hU r) hKc hK (affineWeight v f s)
  have hline (s r) (x : K) : affineWeight v f r x - affineWeight v f s x = (r - s) * f x := by
    simp only [affineWeight, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have hb (s r) : (r - s) * I r ≤ E r - E s ∧ E r - E s ≤ (r - s) * I s := by
    have hendpoint := sourceRelativeEnergy_endpoint_bounds ω (iEnvelope_model_of_positive ω hφ hφpos)
      (hinfty r) (hinfty s)
    change (∫ x, canonicalERealDiffToReal (U r x) (U s x) ∂μ r) ≤ E r - E s ∧
      E r - E s ≤ ∫ x, canonicalERealDiffToReal (U r x) (U s x) ∂μ s at hendpoint
    have hdiff (q) : Integrable (fun x => canonicalERealDiffToReal (U r x) (U s x)) (μ q) :=
      sourceRelativeFiniteEnergy_integrable_independent_diagonal ω (hfinite r) (hfinite s) (hfinite q)
    have hlowAE : ∀ᵐ x ∂μ r, (r - s) * F x ≤ canonicalERealDiffToReal (U r x) (U s x) := by
      filter_upwards [hcontact r, hobstacle s r, hpole s r] with x hx ho hn
      obtain ⟨hxK, hUr⟩ := hx
      have hUs := EReal.coe_toReal ((hU s).1 x) hn
      have ho' := ho hxK
      rw [← hUs, EReal.coe_le_coe_iff] at ho'
      rw [hUr, ← hUs, canonicalERealDiffToReal_coe_coe, hFval ⟨x, hxK⟩]
      have h := hline s r ⟨x, hxK⟩
      linarith
    have hupAE : ∀ᵐ x ∂μ s, canonicalERealDiffToReal (U r x) (U s x) ≤ (r - s) * F x := by
      filter_upwards [hcontact s, hobstacle r s, hpole r s] with x hx ho hn
      obtain ⟨hxK, hUs⟩ := hx
      have hUr := EReal.coe_toReal ((hU r).1 x) hn
      have ho' := ho hxK
      rw [← hUr, EReal.coe_le_coe_iff] at ho'
      rw [← hUr, hUs, canonicalERealDiffToReal_coe_coe, hFval ⟨x, hxK⟩]
      have h := hline s r ⟨x, hxK⟩
      linarith
    have hlow := integral_mono_ae ((hFint r).const_mul (r - s)) (hdiff r) hlowAE
    have hup := integral_mono_ae (hdiff s) ((hFint s).const_mul (r - s)) hupAE
    rw [integral_const_mul] at hlow hup
    rw [← hreadI r] at hlow
    rw [← hreadI s] at hup
    exact ⟨hlow.trans hendpoint.1, hendpoint.2.trans hup⟩
  change HasDerivAt E (I t) t
  exact hasDerivAt_of_contact_bounds hIcontinuous.continuousAt (hb t)

/-- The displayed original d/dt formula, for ALL real t and the SAME
actual original real functional and actual restricted partial-I MA measure. -/
theorem partialEquilibriumEnergy_deriv (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v f : C(K, ℝ)) (t : ℝ) :
    deriv (fun s : ℝ => partialEquilibriumEnergy ω hφ hφpos hKc hK (v + s • f)) t =
      ∫ x : K, f x ∂(sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ K (fun y => ((v + t • f) y : EReal)))
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK (v + t • f)).1).comap Subtype.val :=
  (partialEquilibriumEnergy_hasDerivAt ω hφ hφpos hKc hK v f t).deriv

end SGPT.Bergman.PartialEnergyDifferentiability
