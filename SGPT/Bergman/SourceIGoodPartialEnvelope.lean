import SGPT.Bergman.SourcePartialEnvelopeEverywhere
import SGPT.PSH.SourceIGoodBackground
import SGPT.PSH.SourcePIComparison

/-! # The full original I-good partial-envelope corollary

The arbitrary extended-real obstacle has only a finite real lower bound.
Every ideal candidate, including one of zero original mass, is compared in
an internally produced positive enlarged background. All original candidate
functions and the literal original QE obstacle remain unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.IGoodPartialEnvelope

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialPOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Whole original cor:I-good_partial_env, retaining the arbitrary original
lower-bounded extended-real obstacle and possible positive-infinite outputs. -/
theorem partialIEnvelope_eq_partialEnvelope_of_iGood (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hgood : sourceIGood (n := n) φ) (K : Set M) (f : K → EReal)
    (hf : ∃ L : ℝ, ∀ x : K, (L : EReal) ≤ f x) :
    partialIEnvelope θ φ K f = partialEnvelope θ φ K f := by
  have horder {η : M → EReal} (hη : (ofFixedModel n M).IsThetaPSH θ η)
      (hI : sourceIOrder (ofFixedModel n M) η φ) :
      GlobalPComparison.sourcePOrder (n := n) η φ := by
    let Θ := θ.add (nativeClosedFormToAtlas ω.form)
    have hηΘ : (ofFixedModel n M).IsThetaPSH Θ η := sourceThetaPSH_add_kahler ω hη
    have hφΘ : (ofFixedModel n M).IsThetaPSH Θ φ := sourceThetaPSH_add_kahler ω hφ
    have hηΘpos : 0 < sourcePotentialNonPluripolarMeasure Θ η hηΘ univ :=
      sourcePositiveMass_add_kahler ω hη
    have hφΘpos : 0 < sourcePotentialNonPluripolarMeasure Θ φ hφΘ univ :=
      sourcePositiveMass_add_kahler ω hφ
    have heq : sourceSingularityEnvelope Θ φ = sourceIEnvelope Θ φ :=
      (sourceIGood_iff_PI_eq ω hφΘ hφΘpos).mp hgood
    have hIle : sourceIEnvelope Θ η ≤ sourceIEnvelope Θ φ :=
      (sourceIOrder_iff_sourceIEnvelope_le hηΘ hφΘ).mp hI
    have hP : sourceSingularityEnvelope Θ η ≤ sourceSingularityEnvelope Θ φ := by
      rw [heq]
      exact (sourcePEnvelope_le_IEnvelope hηΘ).trans hIle
    apply (GlobalPComparison.sourcePOrder_iff_positive_background ω (atlasClosedFormToNative Θ)
      ((isThetaPSH_iff_nativeThetaPotential Θ η).mp hηΘ)
      ((isThetaPSH_iff_nativeThetaPotential Θ φ).mp hφΘ) hηΘpos hφΘpos).mpr
    change singularityEnvelope (atlasClosedFormToNative Θ).val η ≤
      singularityEnvelope (atlasClosedFormToNative Θ).val φ
    simpa only [sourceSingularityEnvelope_eq_native] using hP
  rw [(SGPT.Bergman.PartialEnvelopeEverywhere.partialEnvelope_globalP_full_descriptions
    ω hφ hφpos hf).1]
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialPCompetitors θ φ K f => w.val x)
      ⟨v.val, v.property.1, v.property.2.1, horder v.property.1 v.property.2.2⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialICompetitors θ φ K f => w.val x)
      ⟨v.val, v.property.1, v.property.2.1,
        sourceIOrder_of_sourcePOrder ⟨θ, v.property.1⟩ ⟨θ, hφ⟩ v.property.2.2⟩

end SGPT.Bergman.IGoodPartialEnvelope
