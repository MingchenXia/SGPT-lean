import SGPT.Bergman.SourcePartialEquilibriumMeasures
import SGPT.Envelopes.SourceMixedEnergyIntegrability

/-! Finite mass, contact, obstacle retention and relative finite energy for partial-I envelopes. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PartialEnergyDifferentiability

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeIComparison SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEquilibriumMeasure
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending GlobalNonPluripolar
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Actual original QE predicates hold AE for EVERY actual genuine original
diagonal MA measure, using its true original pluripolar-null dictionary. -/
theorem sourceQuasiEverywhere_ae_nonPluripolar
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {P : M → Prop}
    (hP : SourceQuasiEverywhere (n := n) P) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ u hu, P x := by
  apply ae_iff.mpr
  exact globalMixedMeasure_doesNotChargeManifoldPluripolar
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu).1) _
    ((sourceQuasiEverywhere_iff_native P).mp hP)

omit [ConnectedSpace M] in
/-- Finiteness is a theorem of the SAME actual global diagonal measure. -/
theorem sourcePotentialMeasure_finite (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    IsFiniteMeasure (sourcePotentialNonPluripolarMeasure θ u hu) :=
  globalMixedMeasure_isFiniteMeasure ω
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu).1)

/-- Actual E-infinity membership supplies full mass AND the actual finite
own-measure energy integral; this is not a real-energy output certificate. -/
theorem partialIEnvelope_finiteEnergy_continuous (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (w : C(K, ℝ)) :
    SourceRelativeFiniteEnergy θ (sourceIEnvelope θ φ)
      (partialIEnvelope θ φ K (fun x => (w x : EReal))) (iEnvelope_model_of_positive ω hφ hφpos) := by
  apply (sourceRelativeFiniteEnergy_iff_native θ _ _ _).mpr
  exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity ω
    ((sourceRelativeEInfinity_iff_native θ _ _).mp
      (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w))

/-- ALL continuous real weights have the SAME actual total mass, via the
two true ordinary comparisons with the ACTUAL ideal-envelope model. -/
theorem partialIEnvelope_continuous_mass_eq (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v w : C(K, ℝ)) :
    sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun x => (w x : EReal)))
      (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w).1 univ =
    sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun x => (v x : EReal)))
      (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK v).1 univ := by
  have hv := partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK v
  have hw := partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w
  exact le_antisymm
    (sourcePotentialNonPluripolarMass_mono ω hw.1 hv.1 (hw.2.1.trans hv.2.2))
    (sourcePotentialNonPluripolarMass_mono ω hv.1 hw.1 (hv.2.1.trans hw.2.2))

/-- Full actual ideal contact and support, derived from the full
ordinary balayage at the ACTUAL positive PIphi and the exact I/P bridge. -/
theorem partialIEnvelope_continuous_contact_ae (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (w : C(K, ℝ)) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ K (fun y => (w y : EReal)))
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK w).1,
      ∃ hx : x ∈ K, partialIEnvelope θ φ K (fun y => (w y : EReal)) x = (w ⟨x, hx⟩ : EReal) := by
  let Q := sourceIEnvelope θ φ
  have hmodel : SourceModelPotential θ Q := iEnvelope_model_of_positive ω hφ hφpos
  have hQ := hmodel.thetaPSH
  have hQpos : 0 < sourcePotentialNonPluripolarMeasure θ Q hQ univ := hmodel.choose_spec.2
  let W : SGPT.Bergman.WeightedSubset.WeightedSubset n M := ⟨K, hKc, hK, w⟩
  obtain ⟨hJ, _hH, _hsharp, houtside, hneq⟩ := weighted_partial_balayage ω hQ hQpos W
  have hc : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ
      (partialEnvelope θ Q K (fun y => (w y : EReal))) hJ,
      ∃ hx : x ∈ K, partialEnvelope θ Q K (fun y => (w y : EReal)) x = (w ⟨x, hx⟩ : EReal) := by
    have hKae : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ
        (partialEnvelope θ Q K (fun y => (w y : EReal))) hJ, x ∈ K := by
      apply ae_iff.mpr
      exact houtside
    have hneqae : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ
        (partialEnvelope θ Q K (fun y => (w y : EReal))) hJ,
        ¬ ∃ hx : x ∈ K, partialEnvelope θ Q K (fun y => (w y : EReal)) x ≠ (w ⟨x, hx⟩ : EReal) := by
      apply ae_iff.mpr
      simp only [not_not]
      exact hneq
    filter_upwards [hKae, hneqae] with x hx hn
    exact ⟨hx, by by_contra he; exact hn ⟨hx, he⟩⟩
  simpa only [partialIEnvelope_eq_partialEnvelope_iEnvelope hφ, Q] using hc

/-- Every original partial-I QE obstacle is read under ANY independent
genuine diagonal measure after the actual null-set dictionary, not pointwise. -/
theorem partialIEnvelope_continuous_obstacle_ae (_ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (w : C(K, ℝ)) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ u hu, ∀ hx : x ∈ K,
      partialIEnvelope θ φ K (fun y => (w y : EReal)) x ≤ (w ⟨x, hx⟩ : EReal) := by
  let W : SGPT.Bergman.WeightedSubset.WeightedSubset n M := ⟨K, hKc, hK, w⟩
  obtain ⟨R, _hR0, hR⟩ := W.exists_real_abs_bound
  apply sourceQuasiEverywhere_ae_nonPluripolar hu
  exact partialIEnvelope_obstacle θ φ hK
    ⟨R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩

end SGPT.Bergman.PartialEnergyDifferentiability
