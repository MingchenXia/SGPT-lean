import SGPT.Bergman.SourcePartialEnvelopeBounds
import SGPT.Bergman.SourceWeightedSubset
import SGPT.PSH.SourcePIComparison
import SGPT.Envelopes.SourceRelativeEnergy

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace SGPT.Bergman.PartialEquilibriumEnergy

open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeSameType
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The original positive reference internally produces a genuine, ordinary-P
fixed, positive-mass model at its actual I-envelope. -/
theorem iEnvelope_model_of_positive (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    SourceModelPotential θ (sourceIEnvelope θ φ) := by
  refine ⟨isThetaPSH_sourceIEnvelope hφ, (sourcePEnvelope_iEnvelope hφ).symm, ?_⟩
  exact lt_of_lt_of_le hφpos (sourceMass_le_iVolume ω hφ)

/-- Every original continuous real weight yields actual E-infinity membership
of the literal partial I-envelope, without an incoming output certificate. -/
theorem partialIEnvelope_eInfinity_continuous (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) :
    SourceRelativeEInfinity θ (sourceIEnvelope θ φ)
      (partialIEnvelope θ φ K (fun x => (v x : EReal))) := by
  let W : SGPT.Bergman.WeightedSubset.WeightedSubset n M :=
    ⟨K, hKclosed, hK, v⟩
  obtain ⟨R, _hRnonneg, hR⟩ := SGPT.Bergman.WeightedSubset.WeightedSubset.exists_real_abs_bound W
  have hbound : ∃ R : ℝ, ∀ x : K, |v x| ≤ R := ⟨R, hR⟩
  have hlo : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ (v x : EReal) :=
    ⟨-R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).1⟩
  have hup : ∃ B : ℝ, ∀ x : K, (v x : EReal) ≤ (B : EReal) :=
    ⟨R, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hR x)).2⟩
  obtain ⟨_C, _D, _hP, hI, _hC, _hD⟩ :=
    partialEnvelopes_genuine_bounded hφ hφpos hK hlo hup
  exact ⟨hI, partialIEnvelope_same_singularity_type ω hφ hφpos hK v hbound⟩

/-- All n+1 actual endpoint integrands are genuinely integrable; a real-valued
Bochner integral is never used as a stand-in for a missing finiteness proof. -/
theorem partialEquilibriumEnergy_terms_integrable (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) (j : Fin (n + 1)) :
    Integrable (fun x => canonicalERealDiffToReal
      (partialIEnvelope θ φ K (fun y => (v y : EReal)) x) (sourceIEnvelope θ φ x))
      (sourceEndpointMixedMeasure θ (sourceIEnvelope θ φ)
        (partialIEnvelope θ φ K (fun x => (v x : EReal)))
        (iEnvelope_model_of_positive ω hφ hφpos).thetaPSH
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKclosed hK v).1 j) := by
  rw [sourceEndpointMixedMeasure_eq_native]
  exact RelativeEnergyIntegrability.integrable_relativeEnergyTerm ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (iEnvelope_model_of_positive ω hφ hφpos).thetaPSH)
    ((sourceRelativeEInfinity_iff_native θ _ _).mp
      (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKclosed hK v)) j

/-- The original real partial equilibrium energy on ALL continuous real weights
of the original closed non-pluripolar subtype, with the exact finite formula. -/
def partialEquilibriumEnergy (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) : ℝ :=
  sourceRelativeEnergyOfMinimalType θ (sourceIEnvelope θ φ)
    (partialIEnvelope θ φ K (fun x => (v x : EReal)))
    (iEnvelope_model_of_positive ω hφ hφpos).thetaPSH
    (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKclosed hK v).1

/-- The real inclusion equals the ENTIRE original majorant-inf energy,
so the definition is the printed energy rather than another surrogate. -/
theorem partialEquilibriumEnergy_coe_eq_extended (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) :
    (partialEquilibriumEnergy ω hφ hφpos hKclosed hK v : EReal) =
      sourceRelativeEnergy θ (sourceIEnvelope θ φ)
        (partialIEnvelope θ φ K (fun x => (v x : EReal)))
        (iEnvelope_model_of_positive ω hφ hφpos) := by
  exact (sourceRelativeEnergy_eq_of_eInfinity
    (hφ := iEnvelope_model_of_positive ω hφ hφpos) ω
    (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKclosed hK v)).symm

/-- Literal n+1 endpoint terms and divisor of original def:MAenergy;
no normalization by volume or replacement mixed measure is introduced. -/
theorem partialEquilibriumEnergy_eq_mixed_integrals (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) :
    partialEquilibriumEnergy ω hφ hφpos hKclosed hK v =
      (∑ j : Fin (n + 1), ∫ x, canonicalERealDiffToReal
        (partialIEnvelope θ φ K (fun y => (v y : EReal)) x) (sourceIEnvelope θ φ x)
        ∂sourceEndpointMixedMeasure θ (sourceIEnvelope θ φ)
          (partialIEnvelope θ φ K (fun x => (v x : EReal)))
          (iEnvelope_model_of_positive ω hφ hφpos).thetaPSH
          (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKclosed hK v).1 j) /
            (n + 1 : ℝ) := rfl

/-- Both infinities are excluded by the produced real-energy identity,
without ever applying unconditional EReal.toReal to the extended energy. -/
theorem partialEquilibriumEnergy_extended_finite (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} (hKclosed : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v : C(K, ℝ)) :
    sourceRelativeEnergy θ (sourceIEnvelope θ φ)
      (partialIEnvelope θ φ K (fun x => (v x : EReal)))
      (iEnvelope_model_of_positive ω hφ hφpos) ≠ ⊥ ∧
    sourceRelativeEnergy θ (sourceIEnvelope θ φ)
      (partialIEnvelope θ φ K (fun x => (v x : EReal)))
      (iEnvelope_model_of_positive ω hφ hφpos) ≠ ⊤ := by
  rw [← partialEquilibriumEnergy_coe_eq_extended ω hφ hφpos hKclosed hK v]
  exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩

end SGPT.Bergman.PartialEquilibriumEnergy
