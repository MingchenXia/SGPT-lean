import SGPT.PSH.SourceMixedIVolumeSemicontinuityTails
import SGPT.PSH.SourceIModelGood
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations
import SGPT.PSH.SourceIGoodClosed
import SGPT.PSH.SourceIGoodOperations
import SGPT.PSH.SourceIGoodBackground
import SGPT.PSH.SourceSingularityPositiveCompleteness
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.PSH.SourceMixedMassSingularityContinuity

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.SourceUSCModelsDraft
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  VariableComplexAtlas CompactPrimeOver CompactPrimeNumerical SourceUSCTailsDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The original I-equivalence criterion gives equality of ACTUAL prime readers. -/
theorem presentationReader_eq_of_IEquivalent {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v)
    (hI : sourceIEquivalent (ofFixedModel n X) u v) (p : PrimePresentation n X) :
    presentationReader u p = presentationReader v p :=
  le_antisymm ((sourceIOrder_iff_presentationComparison hv hu).mp hI.2 p)
    ((sourceIOrder_iff_presentationComparison hu hv).mp hI.1 p)

/-- A literal original ordinary envelope of the entire actual directed tail. -/
def modelTail {J : Type*} [Preorder J]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : J → X → EReal) (j : J) : X → EReal :=
  sourceSingularityEnvelope θ (tailSup u j)

/-- Normalized original positive I-model nets produce TRUE I-good model tails,
with unchanged divisorial readers, a genuine common target bound and actual
source dS convergence. There are no supplied convergence or model certificates. -/
theorem positiveIModel_modelTail_tendsto {J : Type*} [Preorder J]
    [IsDirectedOrder J] [Nonempty J]
    (ω : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : J → X → EReal) (v : X → EReal)
    (hu : ∀ j, sourceIModel θ (u j)) (hv : sourceIModel θ v)
    (hpos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (u j) (hu j).1 univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv.1 univ)
    (hν : ∀ p : PrimePresentation n X, Tendsto (fun j => presentationReader (u j) p)
      atTop (𝓝 (presentationReader v p))) :
    ∃ hw : ∀ j, (ofFixedModel n X).IsThetaPSH θ (modelTail θ u j),
      (∀ j, v ≤ modelTail θ u j) ∧
      (∀ j, sourceIModel θ (modelTail θ u j)) ∧
      (∀ (j : J) (p : PrimePresentation n X), presentationReader (modelTail θ u j) p = presentationReader (tailSup u j) p) ∧
      Tendsto (fun j => (⟨modelTail θ u j,hw j⟩ : SourceThetaPotentialL1 θ)) atTop
        (@nhds (SourceThetaPotentialL1 θ)
          (sourceSingularityTopology ω θ (sourcePositiveMass_isBig ω hv.1 hvpos)) ⟨v,hv.1⟩) := by
  have hzero (j : J) (x : X) : u j x ≤ ((0 : ℝ) : EReal) := by
    rw [(hu j).2]
    exact sourceIEnvelope_le_zero θ (u j) x
  have ht (j : J) := tailSup_thetaPSH θ u (fun j => (hu j).1) hzero j
  have htpos (j : J) : 0 < sourcePotentialNonPluripolarMeasure θ (tailSup u j) (ht j) univ :=
    (hpos j).trans_le (sourcePotentialNonPluripolarMass_mono ω (hu j).1 (ht j)
      (MoreSingularOn.of_le fun x _ => (tailSup_bounds u hzero j).1 x))
  have htg (j : J) : sourceIGood (n := n) (tailSup u j) := by
    let : Nonempty (Ici j) := ⟨⟨j,le_rfl⟩⟩
    have hb : FirstPass.LocallyUniformlyBoundedAbove
        (range fun k : Ici j => u k.val) univ := by
      intro x _
      refine ⟨univ,Filter.univ_mem,0,?_⟩
      rintro a ⟨k,rfl⟩ y _
      exact hzero k.val y
    have hg := sourceIGood_uscSup ω (fun k : Ici j => u k.val) (fun k => (hu k.val).1)
      (fun k => (sourceIModel_positive_iGood θ (u k.val) (hu k.val) (hpos k.val)).2) hb
    have hraw : (⨆ k : Ici j, u k.val) = (fun x => ⨆ k : Ici j, u k.val x) := by
      funext x
      simp only [iSup_apply]
    rw [hraw] at hg
    exact hg
  have hPI (j : J) : modelTail θ u j = sourceIEnvelope θ (tailSup u j) :=
    ((sourceIGood_iff_with_positive_background ω (ht j) (htpos j)).mp (htg j)).2
  have hm (j : J) : SourceModelPotential θ (modelTail θ u j) :=
    sourceOrdinaryEnvelope_model ω (ht j) (htpos j)
  have hw (j : J) : (ofFixedModel n X).IsThetaPSH θ (modelTail θ u j) := (hm j).thetaPSH
  have hmi (j : J) : sourceIModel θ (modelTail θ u j) := by
    rw [hPI j]
    exact sourceIEnvelope_isIModel (ht j)
  have hreader (j : J) (p : PrimePresentation n X) :
      presentationReader (modelTail θ u j) p = presentationReader (tailSup u j) p := by
    rw [hPI j]
    exact (presentationReader_eq_of_IEquivalent ⟨θ,ht j⟩
      ⟨θ,isThetaPSH_sourceIEnvelope (ht j)⟩ (sourceIEquivalent_iEnvelope (ht j)) p).symm
  have htarget (j : J) : v ≤ modelTail θ u j := by
    rw [hPI j, hv.2]
    exact (sourceIOrder_iff_sourceIEnvelope_le hv.1 (ht j)).mp
      (target_IOrder_tailSup θ u v (fun j => (hu j).1) hv.1 hzero hν j)
  have ha : Antitone (modelTail θ u) := by
    intro j k hjk
    exact sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => tailSup_antitone u hjk x)
  have hfin : sourcePotentialNonPluripolarMeasure θ v hv.1 univ < ⊤ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      (sourceMixedNonPluripolarMass_lt_top ω (fun _ : Fin n => θ)
        (fun _ => v) (fun _ => hv.1))
  let δ : ℝ := (sourcePotentialNonPluripolarMeasure θ v hv.1 univ).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hvpos.ne' hfin.ne
  have hbound (j : J) : ENNReal.ofReal δ ≤
      sourcePotentialNonPluripolarMeasure θ (modelTail θ u j) (hw j) univ := by
    rw [ENNReal.ofReal_toReal hfin.ne]
    exact sourcePotentialNonPluripolarMass_mono ω hv.1 (hw j)
      (MoreSingularOn.of_le fun x _ => htarget j x)
  let W : J → SourceThetaPotentialL1 θ := fun j => ⟨modelTail θ u j,hw j⟩
  let hbig := sourcePositiveMass_isBig ω hv.1 hvpos
  obtain ⟨U,hUm,hUδ,hlim⟩ :=
    sourceSingularity_exists_model_limit_of_antitone ω θ hbig W ha hδ hbound
  have hUg : sourceIGood (n := n) U.val :=
    sourceIGood_of_tendsto atTop ω θ hbig W U
      (Eventually.of_forall fun j =>
        (sourceIModel_positive_iGood θ (modelTail θ u j) (hmi j) ((hm j).choose_spec.2)).2) hlim
  have hUpos : 0 < sourcePotentialNonPluripolarMeasure θ U.val U.property univ :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le hUδ
  have hUgood := (sourceIGood_iff_with_positive_background ω U.property hUpos).mp hUg
  have hUI : sourceIModel θ U.val := ⟨U.property,hUm.choose_spec.1.trans hUgood.2⟩
  have hread (p : PrimePresentation n X) : presentationReader U.val p = presentationReader v p := by
    have hLU := tendsto_sourceGenericLelong_comp_of_sourceSingularityTopology
      ω θ hbig p.modification atTop W U hlim p.divisor
    have hLV := (tendsto_presentationReader_tailSup θ u v
      (fun j => (hu j).1) hzero hν p).congr'
      (Eventually.of_forall fun j => (hreader j p).symm)
    exact tendsto_nhds_unique hLU hLV
  have hI : sourceIEquivalent (ofFixedModel n X) U.val v := by
    constructor
    · exact (sourceIOrder_iff_presentationComparison ⟨θ,U.property⟩ ⟨θ,hv.1⟩).mpr
        (fun p => (hread p).ge)
    · exact (sourceIOrder_iff_presentationComparison ⟨θ,hv.1⟩ ⟨θ,U.property⟩).mpr
        (fun p => (hread p).le)
  have hUv : U.val = v := hUI.2.trans ((sourceIEnvelope_eq_of_equivalent hI).trans hv.2.symm)
  have hUE : U = (⟨v,hv.1⟩ : SourceThetaPotentialL1 θ) := Subtype.ext hUv
  refine ⟨hw,htarget,hmi,hreader,?_⟩
  change Tendsto W atTop (@nhds (SourceThetaPotentialL1 θ)
    (sourceSingularityTopology ω θ hbig) ⟨v,hv.1⟩)
  rw [hUE] at hlim
  exact hlim

end SGPT.PSH.SourceUSCModelsDraft
