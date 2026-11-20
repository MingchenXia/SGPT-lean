import SGPT.PSH.SourceMixedIVolumeSemicontinuityModels
import SGPT.PSH.SourceGeneralMixedIVolume

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.SourceUSCMixedDraft
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  VariableComplexAtlas CompactPrimeOver CompactPrimeNumerical SourceUSCTailsDraft SourceUSCModelsDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
private theorem actual_kahlerPerturbedPSH (ω : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) (ε : NNReal) :
    (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε : ℝ) • ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive ε.property)

/-- Actual ordinary mixed masses of original positive I-model nets are upper
semicontinuous under original prime-reader convergence, with genuine model
tails and their source dS limits produced internally. -/
theorem mixedMass_limsup_of_positiveIModels {J : Type*} [Preorder J]
    [IsDirectedOrder J] [Nonempty J]
    (ω : KahlerBackground n X) (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : Fin n → J → X → EReal) (v : Fin n → X → EReal)
    (hu : ∀ i j, sourceIModel (θ i) (u i j)) (hv : ∀ i, sourceIModel (θ i) (v i))
    (hpos : ∀ i j, 0 < sourcePotentialNonPluripolarMeasure (θ i) (u i j) (hu i j).1 univ)
    (hvpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure (θ i) (v i) (hv i).1 univ)
    (hν : ∀ i (p : PrimePresentation n X), Tendsto (fun j => presentationReader (u i j) p)
      atTop (𝓝 (presentationReader (v i) p))) :
    limsup (fun j => sourceMixedNonPluripolarMass θ (fun i => u i j) (fun i => (hu i j).1))
      atTop ≤ sourceMixedNonPluripolarMass θ v (fun i => (hv i).1) := by
  classical
  choose hw htarget hmi hreader hds using fun i =>
    positiveIModel_modelTail_tendsto ω (θ i) (u i) (v i) (hu i) (hv i) (hpos i) (hvpos i) (hν i)
  have hzero (i : Fin n) (j : J) (x : X) : u i j x ≤ ((0 : ℝ) : EReal) := by
    rw [(hu i j).2]
    exact sourceIEnvelope_le_zero (θ i) (u i j) x
  have ht (i : Fin n) (j : J) := tailSup_thetaPSH (θ i) (u i) (fun j => (hu i j).1) (hzero i) j
  have hbound (j : J) : sourceMixedNonPluripolarMass θ (fun i => u i j) (fun i => (hu i j).1) ≤
      sourceMixedNonPluripolarMass θ (fun i => modelTail (θ i) (u i) j) (fun i => hw i j) := by
    have hmono := sourceMixedNonPluripolarMass_mono ω (fun i => (hu i j).1) (fun i => ht i j)
      (fun i => MoreSingularOn.of_le fun x _ => (tailSup_bounds (u i) (hzero i) j).1 x)
    have he := sourceOrdinaryEnvelope_mixedMass_eq ω (fun i => ht i j)
    exact hmono.trans_eq he.symm
  have hlim := tendsto_sourceMixedNonPluripolarMass_of_sourceSingularityTopology ω θ
    (fun i => sourcePositiveMass_isBig ω (hv i).1 (hvpos i)) atTop
    (fun j i => (⟨modelTail (θ i) (u i) j,hw i j⟩ : SourceThetaPotentialL1 (θ i)))
    (fun i => (⟨v i,(hv i).1⟩ : SourceThetaPotentialL1 (θ i))) hds
  exact (limsup_le_limsup (Eventually.of_forall hbound)).trans hlim.limsup_eq.le

/-- Whole positive-individual-I-volume case, retaining zero original ordinary
masses. Actual I-envelopes manufacture every normalized positive I-model. -/
theorem envelopeMixedIVolume_limsup_of_primeReader_tendsto {J : Type*} [Preorder J]
    [IsDirectedOrder J] [Nonempty J]
    (ω : KahlerBackground n X) (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : Fin n → J → X → EReal) (v : Fin n → X → EReal)
    (hu : ∀ i j, (ofFixedModel n X).IsThetaPSH (θ i) (u i j))
    (hv : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (v i))
    (hpos : ∀ i j, 0 < sourceIVolume (θ i) (u i j) (hu i j))
    (hvpos : ∀ i, 0 < sourceIVolume (θ i) (v i) (hv i))
    (hν : ∀ i (p : PrimePresentation n X), Tendsto (fun j => presentationReader (u i j) p)
      atTop (𝓝 (presentationReader (v i) p))) :
    limsup (fun j => sourceEnvelopeMixedIVolume θ (fun i => u i j) (fun i => hu i j)) atTop ≤
      sourceEnvelopeMixedIVolume θ v hv := by
  let U (i : Fin n) (j : J) := sourceIEnvelope (θ i) (u i j)
  let V (i : Fin n) := sourceIEnvelope (θ i) (v i)
  have hU (i : Fin n) (j : J) : sourceIModel (θ i) (U i j) := sourceIEnvelope_isIModel (hu i j)
  have hV (i : Fin n) : sourceIModel (θ i) (V i) := sourceIEnvelope_isIModel (hv i)
  have hUpos (i : Fin n) (j : J) :
      0 < sourcePotentialNonPluripolarMeasure (θ i) (U i j) (hU i j).1 univ := hpos i j
  have hVpos (i : Fin n) : 0 < sourcePotentialNonPluripolarMeasure (θ i) (V i) (hV i).1 univ := hvpos i
  have hνU (i : Fin n) (p : PrimePresentation n X) :
      Tendsto (fun j => presentationReader (U i j) p) atTop (𝓝 (presentationReader (V i) p)) := by
    have heV := presentationReader_eq_of_IEquivalent ⟨θ i,hv i⟩
      ⟨θ i,isThetaPSH_sourceIEnvelope (hv i)⟩ (sourceIEquivalent_iEnvelope (hv i)) p
    change Tendsto (fun j => presentationReader (U i j) p) atTop
      (𝓝 (presentationReader (sourceIEnvelope (θ i) (v i)) p))
    rw [← heV]
    exact (hν i p).congr' (Eventually.of_forall fun j =>
      presentationReader_eq_of_IEquivalent ⟨θ i,hu i j⟩
        ⟨θ i,isThetaPSH_sourceIEnvelope (hu i j)⟩ (sourceIEquivalent_iEnvelope (hu i j)) p)
  exact mixedMass_limsup_of_positiveIModels ω θ U V hU hV hUpos hVpos hνU

/-- WHOLE thm:usc_mix_vol on EVERY original proper smooth prime presentation.
All original backgrounds and currents, arbitrary directed nets, zero original
I-volumes and dimension0 are retained. No supplied tail/limit/model certificate. -/
theorem source_usc_mix_vol_presentations {J : Type*} [Preorder J]
    [IsDirectedOrder J] [Nonempty J]
    (ω : KahlerBackground n X) (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : Fin n → J → X → EReal) (v : Fin n → X → EReal)
    (hu : ∀ i j, (ofFixedModel n X).IsThetaPSH (θ i) (u i j))
    (hv : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (v i))
    (hν : ∀ i (p : PrimePresentation n X), Tendsto (fun j => presentationReader (u i j) p)
      atTop (𝓝 (presentationReader (v i) p))) :
    limsup (fun j => sourceGeneralMixedIVolume ω θ (fun i => u i j) (fun i => hu i j)) atTop ≤
      sourceGeneralMixedIVolume ω θ v hv := by
  change limsup (fun j => sourceGeneralMixedIVolume ω θ (fun i => u i j) (fun i => hu i j)) atTop ≤
    ⨅ ε : Ioi (0 : NNReal), sourceMixedIVolumeKahlerPerturbation ω θ v hv ε.val
  apply le_iInf
  intro ε
  let Θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X) :=
    fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (ε.val : ℝ) • ω.form)
  have hΘ (i : Fin n) (j : J) : (ofFixedModel n X).IsThetaPSH (Θ i) (u i j) :=
    actual_kahlerPerturbedPSH ω (hu i j) ε.val
  have hV (i : Fin n) : (ofFixedModel n X).IsThetaPSH (Θ i) (v i) :=
    actual_kahlerPerturbedPSH ω (hv i) ε.val
  have hε : 0 < (ε.val : ℝ) := by exact_mod_cast ε.property
  have hUpos (i : Fin n) (j : J) : 0 < sourceIVolume (Θ i) (u i j) (hΘ i j) :=
    sourceIVolume_add_kahler_pos ω (hu i j) hε
  have hVpos (i : Fin n) : 0 < sourceIVolume (Θ i) (v i) (hV i) :=
    sourceIVolume_add_kahler_pos ω (hv i) hε
  have hbound (j : J) : sourceGeneralMixedIVolume ω θ (fun i => u i j) (fun i => hu i j) ≤
      sourceEnvelopeMixedIVolume Θ (fun i => u i j) (fun i => hΘ i j) :=
    iInf_le (fun t : Ioi (0 : NNReal) =>
      sourceMixedIVolumeKahlerPerturbation ω θ (fun i => u i j) (fun i => hu i j) t.val) ε
  exact (limsup_le_limsup (Eventually.of_forall hbound)).trans
    (envelopeMixedIVolume_limsup_of_primeReader_tendsto ω Θ u v hΘ hV hUpos hVpos hν)

/-- WHOLE original theorem with its ORIGINAL prime-divisor-over-X input read on
the actual direct prime quotient. Each reader is the actual original source
generic Lelong number at every geometric representative, including n=0. -/
theorem source_usc_mix_vol {J : Type*} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (ω : KahlerBackground n X) (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : Fin n → J → X → EReal) (v : Fin n → X → EReal)
    (hu : ∀ i j, (ofFixedModel n X).IsThetaPSH (θ i) (u i j))
    (hv : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (v i))
    (hν : ∀ i (q : DirectPrimeOver n X),
      Tendsto (fun j => directSourceQPSHReader (u i j) ⟨θ i,hu i j⟩ q) atTop
        (𝓝 (directSourceQPSHReader (v i) ⟨θ i,hv i⟩ q))) :
    limsup (fun j => sourceGeneralMixedIVolume ω θ (fun i => u i j) (fun i => hu i j)) atTop ≤
      sourceGeneralMixedIVolume ω θ v hv := by
  apply source_usc_mix_vol_presentations ω θ u v hu hv
  intro i p
  exact hν i (Quot.mk commonResolutionRelation p)

end SGPT.PSH.SourceUSCMixedDraft
