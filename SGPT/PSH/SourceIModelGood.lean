import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] in
/-- Original positive I-models are genuinely I-good in the SAME background,
and hence globally I-good. No assertion is made for zero-mass I-models. -/
theorem sourceIModel_positive_iGood
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : sourceIModel θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu.1 univ) :
    sourceIGoodWith θ u hu.1 ∧ sourceIGood (n := n) u := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1
  have he : u = FirstPass.IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val u :=
    hu.2.trans (sourceIEnvelope_eq_native θ u hu.1)
  have hid := singularityEnvelope_iSingularityEnvelope (atlasClosedFormToNative θ).val
    (atlasClosedFormToNative θ).property.1 (atlasClosedFormToNative θ).property.2
    hn.1.hasSmoothLocalPotentials u hn
  have henv : sourceSingularityEnvelope θ u = sourceIEnvelope θ u := by
    rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native θ u hu.1]
    exact (congrArg (FirstPass.singularityEnvelope (atlasClosedFormToNative θ).val) he).trans hid
  have hg : sourceIGoodWith θ u hu.1 := ⟨hpos,henv⟩
  exact ⟨hg,⟨θ,hu.1,hg⟩⟩

/-- The additional printed minimal-potential clause of the whole original
positive I-model example, from original bigness in EVERY natural dimension. -/
theorem sourceMinimalEnvelope_iModel_iGood (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    sourceIModel θ (sourceMinimalEnvelope θ) ∧
      sourceIGood (n := n) (sourceMinimalEnvelope θ) := by
  obtain ⟨hV,_,hpos⟩ := sourceMinimalEnvelope_model omega θ hbig
  have hfix : sourceMinimalEnvelope θ = sourceIEnvelope θ (sourceMinimalEnvelope θ) := by
    apply le_antisymm
    · exact le_sourceIEnvelope hV (sourceMinimalEnvelope_le_zero θ)
        (sourceIEquivalent_refl ⟨θ,hV⟩)
    · have hUSC := ((isThetaPSH_iff_nativeThetaPotential θ _).mp hV).quasiPshPotential.1.upperSemicontinuous
      apply uscRegularization_le hUSC
      intro x
      apply iSup_le
      intro v
      exact le_iSup (fun a : {a : M → EReal // (ofFixedModel n M).IsThetaPSH θ a ∧ a ≤ 0} => a.1 x)
        ⟨v.1,v.2.1,v.2.2.1⟩
  have hm : sourceIModel θ (sourceMinimalEnvelope θ) := ⟨hV,hfix⟩
  exact ⟨hm,(sourceIModel_positive_iGood θ (sourceMinimalEnvelope θ) hm hpos).2⟩

end SGPT.PSH.VariableComplexAtlas
