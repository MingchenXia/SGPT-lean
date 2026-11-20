import SGPT.Hodge.SourceCartierMatchedFamilies
import SGPT.Okounkov.PartialBodyDS
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
open scoped Topology ENNReal

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The literal original modelwise order follows from original potential
I-order in the same native background; no current is required nondivisorial. -/
theorem representedFamily_le_of_iOrder (θ : ClosedRealOneOneForm (m+1) X)
    (u v : X → EReal) (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hI : IOrderOnManifold (n := m+1) u v) :
    LEAny (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu))
      (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ v hv)) := by
  let A := representedCurrent θ u hu
  let B := representedCurrent θ v hv
  have hp := (isPresentationAny_iff_book A θ u).mp (representedCurrent_isPresentation θ u hu)
  have hq := (isPresentationAny_iff_book B θ v).mp (representedCurrent_isPresentation θ v hv)
  apply (leAny_iff_existing (Nat.succ_pos m) _ _).mpr
  rw [currentBDivisorAnyOn_eq_existing,currentBDivisorAnyOn_eq_existing]
  exact currentBDivisor_le_of_iOrder (hp.currentClass_eq.trans hq.currentClass_eq.symm)
    ⟨θ,θ,u,v,hu,hv,hp.2,hq.2,hI⟩

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Actual pointwise-decreasing QEA gives decreasing original whole families. -/
theorem representedFamily_antitone_of_qea (θ : ClosedRealOneOneForm (m+1) X)
    (u : X → EReal) (U : ℕ → X → EReal)
    (hQ : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j)) :
    ∀ i j : ℕ, i ≤ j →
      LEAny (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ (U j) (hU j)))
        (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ (U i) (hU i))) := by
  intro i j hij
  apply representedFamily_le_of_iOrder
  exact iOrderOnManifold_of_le (hU i).1.quasiPlurisubharmonic (fun x => hQ.2.2.1.1 x hij)

/-- Genuine QEA and original DS continuity give the original topology limit
of the SAME whole current family; the I-envelope family equality is proved. -/
theorem representedFamily_converges_of_kahler_qea (_ω : KahlerBackground (m+1) X)
    (θ : ClosedRealOneOneForm (m+1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hK : IsKahlerCurrentPotential θ u)
    (U : ℕ → X → EReal) (hQ : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j)) :
    ConvergesAny atTop
      (fun j => currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ (U j) (hU j)))
      (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu)) := by
  obtain ⟨ω₀,ε,hnat⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation hQ
  have hbig := SGPT.Okounkov.PartialBody.isBigClass_of_isKahlerCurrentPotential hK
  have hpos := SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hK hu
  obtain ⟨-,hI,-,hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      ω₀ θ hbig hnat hU hpos
  let θa := nativeClosedFormToAtlas θ
  let W : ℕ → SourceThetaPotentialL1 θa := fun j =>
    ⟨U j,(isThetaPSH_iff_nativeThetaPotential θa _).mpr (hU j)⟩
  let v : SourceThetaPotentialL1 θa :=
    ⟨iSingularityEnvelope θ.val u,(isThetaPSH_iff_nativeThetaPotential θa _).mpr hI⟩
  have hsrc : Tendsto W atTop (@nhds _ (sourceSingularityTopology ω₀ θa hbig) v) :=
    (sourceSingularity_tendsto_iff_native atTop ω₀ θa hbig W v).mpr hlim
  have hc := currentBDivisor_converges_of_dS ω₀ θa hbig atTop W v hsrc
  have hbridge (f : X → EReal) (hf : IsThetaPshPotential θ.val f) :
      toExisting (ModelSystem.blowup (m+1) X) (Nat.succ_pos m)
        (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ f hf)) =
      currentBDivisor (sourcePotentialCurrent θa
        ⟨f,(isThetaPSH_iff_nativeThetaPotential θa _).mpr hf⟩) :=
    SourceDSDraft.sourcePotentialCurrentAny_bdivisor_pos θa _
  have hcAny : ConvergesAny atTop
      (fun j => currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ (U j) (hU j)))
      (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
        (representedCurrent θ (iSingularityEnvelope θ.val u) hI)) := by
    apply (convergesAny_iff_existing (Nat.succ_pos m) atTop _ _).mpr
    intro π
    simpa only [hbridge] using hc π
  have hp := representedCurrent_isPresentation θ (iSingularityEnvelope θ.val u) hI
  have hq := representedCurrent_isPresentation θ u hu
  have hIE := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  have hFamily : currentBDivisorAnyOn (ModelSystem.blowup (m+1) X)
      (representedCurrent θ (iSingularityEnvelope θ.val u) hI) =
      currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu) :=
    currentBDivisorAnyOn_eq_of_currentIEquivalent
      ((currentClassAny_eq_of_presentation _ _ _ hp).trans
        (currentClassAny_eq_of_presentation _ _ _ hq).symm)
      ⟨θ,θ,_,u,hp,hq,hIE.2⟩ ⟨θ,θ,u,_,hq,hp,hIE.1⟩
  rw [hFamily] at hcAny
  exact hcAny

/-- Every actual analytic Kähler-current term produces a genuinely big nef
Cartier family. Original volume positivity is a conclusion, not an input. -/
theorem representedFamily_big_nefCartier (ω : KahlerBackground (m+1) X)
    (θ : ClosedRealOneOneForm (m+1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hK : IsKahlerCurrentPotential θ u)
    {c : ℚ} {𝔞 : GermIdeal (m+1) X} (htype : HasAnalyticSingularitiesOfType u c 𝔞) :
    IsNefCartierAny (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu)) ∧
      0 < volumeAny (currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu)) := by
  let A := representedCurrent θ u hu
  have hp := (isPresentationAny_iff_book A θ u).mp (representedCurrent_isPresentation θ u hu)
  have hA := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent A)
  have hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
  have he := (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m+1) X) A).trans
    (currentBDivisorOn_congr _ hp.2 hA hT)
  constructor
  · apply (isNefCartierAny_iff_existing (Nat.succ_pos m) _).mpr
    rw [he]
    exact currentBDivisor_isNefCartier_of_hasAnalyticSingularitiesOfType ω θ hu htype
  · rw [volumeAny_eq_existing (Nat.succ_pos m),he,
      currentBDivisorOn_vol_of_isKahlerCurrentPotential θ hK hu]
    exact (SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hK hu).trans_le
      (SGPT.Okounkov.PartialBody.diagonalPotentialMass_le_iVolume ω hu)

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
