import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.IEnvelopeDecreasingModelInfimum
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDecreasingNets

/-! Original `prop:decnetmodelPI`, entire decreasing-net envelope identity
and I-model corollary. Source: author/chapter_envelopes.tex:2381--2415.
Actual infimum membership is manufactured through a genuine monotone
sequence selection with the same entire pointwise infimum. No countable
cofinality, target envelope identity or prime quotient is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass
open SingularModelEnergyDecreasingNets ActualDecreasingModelInfimum
open IEnvelopeDecreasingModelInfimum ActualIEnvelopeOrderInfimum

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] in
/-- The literal pointwise infimum of a decreasing directed net of original
positive model potentials is genuinely theta-PSH, with no supplied domain
or noncollapse certificate. -/
theorem sourceThetaPSH_iInf_of_antitone_models
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hmodel : ∀ i, SourceModelPotential θ (v i)) (hanti : Antitone v) :
    IsThetaPSH θ (⨅ i, v i) := by
  classical
  have hvn (i : I) : IsModelPotential (atlasClosedFormToNative θ) (v i) :=
    (hmodel i).toNative
  obtain ⟨j, hj, _, hinf⟩ := exists_monotone_sequence_iInf_eq (Classical.arbitrary I)
    (fun i => (hvn i).plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous) hanti
  have hseq := isThetaPshPotential_iInf_of_antitone_model
    (fun k => hvn (j k)) (fun _ _ hkl => hanti (hj hkl))
  rw [hinf] at hseq
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hseq

/-- Whole original `prop:decnetmodelPI`, first assertion. Its only limit
mass hypothesis is the printed positive mass of the actual infimum; the
membership witness used to state that measure is produced above. -/
theorem sourceIEnvelope_iInf_of_antitone_models_positive
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hmodel : ∀ i, SourceModelPotential θ (v i)) (hanti : Antitone v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ (⨅ i, v i)
      (sourceThetaPSH_iInf_of_antitone_models hmodel hanti) univ) :
    (⨅ i, sourceIEnvelope θ (v i)) = sourceIEnvelope θ (⨅ i, v i) := by
  classical
  let Θ := atlasClosedFormToNative θ
  have hu : IsThetaPSH θ (⨅ i, v i) := sourceThetaPSH_iInf_of_antitone_models hmodel hanti
  have hbig : IsBigClass (RealBottChern.ofRepresentative Θ) := sourcePositiveMass_isBig omega hu hpos
  have hvn (i : I) : IsModelPotential Θ (v i) := (hmodel i).toNative
  obtain ⟨j, hj, _, hinf⟩ := exists_monotone_sequence_iInf_eq (Classical.arbitrary I)
    (fun i => (hvn i).plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous) hanti
  have hseqpsh := isThetaPshPotential_iInf_of_antitone_model
    (fun k => hvn (j k)) (fun _ _ hkl => hanti (hj hkl))
  have hupos : HasPositivePotentialMass Θ (⨅ i, v i)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu) := hpos
  have hseqpos : HasPositivePotentialMass Θ (⨅ k, v (j k)) hseqpsh := by
    simpa only [hinf] using hupos
  have hseq := iInf_iSingularityEnvelope_eq omega Θ hbig
    (fun k => hvn (j k)) (fun _ _ hkl => hanti (hj hkl)) hseqpos
  rw [hinf] at hseq
  have hread : (fun i => sourceIEnvelope θ (v i)) =
      fun i => IEnvelope.iSingularityEnvelope Θ.val (v i) :=
    funext fun i => sourceIEnvelope_eq_native θ _ (hmodel i).thetaPSH
  rw [hread, sourceIEnvelope_eq_native θ _ hu]
  apply le_antisymm
  · rw [← hseq]
    exact le_iInf fun k => iInf_le (fun i => IEnvelope.iSingularityEnvelope Θ.val (v i)) (j k)
  · apply le_iInf
    intro i
    exact iSingularityEnvelope_le_of_iOrderOnManifold Θ (hvn i).plurisubharmonic
      (iOrderOnManifold_of_le (hvn i).plurisubharmonic.1.quasiPlurisubharmonic (iInf_le v i))

/-- Whole original `prop:decnetmodelPI`, final assertion. Both the original
model-net domain and the natural positive actual infimum mass are retained. -/
theorem sourceIModel_iInf_of_antitone_models_positive
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hmodel : ∀ i, SourceModelPotential θ (v i)) (hanti : Antitone v)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ (⨅ i, v i)
      (sourceThetaPSH_iInf_of_antitone_models hmodel hanti) univ)
    (hiModel : ∀ i, sourceIModel θ (v i)) :
    sourceIModel θ (⨅ i, v i) := by
  refine ⟨sourceThetaPSH_iInf_of_antitone_models hmodel hanti, ?_⟩
  have heq := sourceIEnvelope_iInf_of_antitone_models_positive omega hmodel hanti hpos
  have hread : v = fun i => sourceIEnvelope θ (v i) := funext fun i => (hiModel i).2
  exact (congrArg (fun a : I → M → EReal => ⨅ i, a i) hread).trans heq

end SGPT.PSH.VariableComplexAtlas
