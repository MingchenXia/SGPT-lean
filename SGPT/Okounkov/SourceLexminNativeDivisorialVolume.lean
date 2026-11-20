import SGPT.Okounkov.SourceLexminDivisorialVolume

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceLexmin
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending NaturalThetaPshGeometricCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Hodge.BDivChain.NativeDraft.DTUniformDraft
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
open SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
open SGPT.Okounkov.TranscendentalCore

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The independent whole-current I-volume reads the SAME native potential
and native background, with no family-volume definition substituted. -/
theorem currentIVolumeAny_thetaPositiveCurrent (ω : KahlerBackground (m + 1) X)
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    currentIVolumeAny (ofBookCurrent (SGPT.PSH.BookCurrent.thetaPositiveCurrent θ u hu)) =
      iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) u hu := by
  let T := ofBookCurrent (SGPT.PSH.BookCurrent.thetaPositiveCurrent θ u hu)
  have hp : IsPresentationAny T θ u := by
    apply (isPresentationAny_iff_book T θ u).mpr
    rw [show toBookCurrent T = SGPT.PSH.BookCurrent.thetaPositiveCurrent θ u hu from
      toBookCurrent_ofBookCurrent _]
    exact SGPT.PSH.BookCurrent.isPresentation_thetaPositiveCurrent θ u hu
  have hpa : IsPresentationAny T (atlasClosedFormToNative (nativeClosedFormToAtlas θ)) u := by
    simpa only [sourceNativeAtlasForm_roundTrip] using hp
  have h := currentIVolumeAny_eq_of_presentation ω T (nativeClosedFormToAtlas θ) u hpa
  rw [sourceIVolume_eq_native _ _ _
    (LocalPotentials.closedRealOneOne_hasLocalPotentials
      (atlasClosedFormToNative (nativeClosedFormToAtlas θ)))] at h
  simpa only [sourceNativeAtlasForm_roundTrip] using h

/-- The original native I-volume equality for arbitrary REAL divisorial
addition, including all original poles and zero coefficient/zero mass. -/
theorem iVolume_add_weight (ω : KahlerBackground (m + 1) X)
    {β : ClosedRealOneOneForm (m + 1) X} {v : X → EReal}
    (hv : IsThetaPshPotential β.val v) (E : MeteredEffectiveQDivisor (m + 1) X)
    {c : ℝ} (hc : 0 ≤ c) :
    let hw := TranscendentalLifting.isThetaPshPotential_weight E
    let hcu := isThetaPshPotential_nonneg_smul hw hc
    let hsum := isThetaPshPotential_add_from_positive_sum hv hcu
    iVolume (β + c • E.curvature)
      (LocalPotentials.closedRealOneOne_hasLocalPotentials (β + c • E.curvature))
      (fun x => v x + (c : EReal) * E.weight x) hsum =
      iVolume β (LocalPotentials.closedRealOneOne_hasLocalPotentials β) v hv := by
  let hw := TranscendentalLifting.isThetaPshPotential_weight E
  let A := thetaPotentialCurrent E.curvature.val E.weight hw
  let hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hw
  let R := SGPT.PSH.BookCurrent.thetaPositiveCurrent β v hv
  let hR := SGPT.Siu.isClosedPositiveCurrent_bookCurrent R
  let S := SGPT.Siu.toBookCurrent (R.current + c • A) (hR.add (hA.smul hc))
  obtain ⟨hcu, hscale⟩ := exists_thetaPotentialCurrent_nonneg_smul hw hc
  obtain ⟨hsum, hadd⟩ := exists_thetaPotentialCurrent_add hv hcu
  rw [hscale] at hadd
  have hS : S = SGPT.PSH.BookCurrent.thetaPositiveCurrent (β + c • E.curvature)
      (fun x => v x + (c : EReal) * E.weight x) hsum := by
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    exact hadd.symm
  have hvol := currentIVolumeAny_add_weight ω R E hc
  change currentIVolumeAny (ofBookCurrent S) = currentIVolumeAny (ofBookCurrent R) at hvol
  rw [hS, currentIVolumeAny_thetaPositiveCurrent ω, currentIVolumeAny_thetaPositiveCurrent ω] at hvol
  exact hvol

end SGPT.Okounkov.SourceLexmin
