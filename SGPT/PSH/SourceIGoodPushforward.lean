import SGPT.PSH.SourceMixedIVolumePushforward
import SGPT.Hodge.SourceDSContinuity
import SGPT.PSH.SourceIGoodBackground
import SGPT.Foundations.Analysis.Pending.BigClassIGoodMassCriterion
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceIGoodPushDraft
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.LocalCurrents
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.NPP
  SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourcePushforwardDraft
  SGPT.Hodge.BDivChain.SourcePushforwardAnyDraft

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [ConnectedSpace X] [ConnectedSpace Y]

/-- The source singleton I-volume is preserved for every genuine pair of
presentations of the actual current pushforward, including zero original mass. -/
theorem sourceIVolume_pushforward_presentations {π : Y → X}
    (hπ : IsAnalyticModification (n := m+1) π)
    (ωX : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    (θ : ClosedRealOneOneForm (m+1) Y) (u : Y → EReal)
    (hu : IsThetaPshPotential θ.val u)
    (σ : ClosedRealOneOneForm (m+1) X) (v : X → EReal)
    (hv : IsThetaPshPotential σ.val v)
    (hpush : currentPushforward hπ.1 (thetaPotentialCurrent θ.val u hu) =
      thetaPotentialCurrent σ.val v hv) :
    sourceIVolume (nativeClosedFormToAtlas σ) v (isThetaPSH_nativeClosedFormToAtlas hv) =
      sourceIVolume (nativeClosedFormToAtlas θ) u (isThetaPSH_nativeClosedFormToAtlas hu) := by
  let T := thetaPotentialCurrent θ.val u hu
  have hp := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent θ.val u hu
  have hpp := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hp
  have h := sourceCurrentMixedIVolume_modification_pushforward hπ ωX ωY
    (fun _ => T) (fun _ => hp.1) (fun _ => hp.2.1) (fun _ => hp.2.2)
  have hs := sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation ωY
    T hp.1 hp.2.1 hp.2.2 θ u hu rfl
  have ht := sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation ωX
    (currentPushforward hπ.1 T) hpp.1 hpp.2.1 hpp.2.2 σ v hv hpush
  exact ht.symm.trans (h.trans hs)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The original zero-potential current is literally the smooth-form current. -/
theorem zeroPotentialCurrent_eq_smooth
    (σ : ClosedRealOneOneForm (m+1) X)
    (hu : IsThetaPshPotential σ.val (fun _ : X => (0 : EReal))) :
    thetaPotentialCurrent σ.val (fun _ => 0) hu =
      GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m+1))
        (k := degreeTwo (Nat.succ_pos m)) σ.val := by
  have hz : globalDDC (canonicalBasis (m+1)) (Nat.succ_pos m) (fun _ => 0)
      hu.quasiPshPotential = 0 := by
    apply globalCurrent_ext (canonicalBasis (m+1))
    intro e
    rw [globalDDC_coefficients, GlobalCurrent.coefficients_zero]
    have hreg : regularDistribution (canonicalBasis (m+1)).addHaar
        (fun z => (chartFunction (fun _ : X => (0 : EReal)) e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m+1))
          (Nat.succ_pos m) (fun _ => 0) hu.quasiPshPotential e) = 0 := by
      ext φ
      simp [regularDistribution_apply,chartFunction]
    change ddC _ = 0
    rw [hreg]
    ext w : 1
    have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
    rw [hw,ddC_apply]
    simp
  rw [thetaPotentialCurrent,hz,add_zero]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Exact current identity for the SAME potential after a semipositive smooth shift. -/
theorem thetaPotentialCurrent_semipositive_add
    (θ σ : ClosedRealOneOneForm (m+1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hσ : σ.val.IsSemipositive) :
    thetaPotentialCurrent (θ+σ).val u
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hu hσ) =
      thetaPotentialCurrent θ.val u hu +
        GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m+1))
          (k := degreeTwo (Nat.succ_pos m)) σ.val := by
  have hz := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  obtain ⟨hs,hr⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hz
  have he : (fun x => u x+(0 : EReal)) = u := by funext x; simp
  simpa only [he,zeroPotentialCurrent_eq_smooth σ hz] using hr

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [ConnectedSpace X] [ConnectedSpace Y] in
/-- The original Kähler enlargement commutes with pushforward using its actual
semipositive pullback, without claiming that pullback to be Kähler. -/
theorem enlarged_current_pushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m+1) π)
    (ω : KahlerBackground (m+1) X)
    (θ : ClosedRealOneOneForm (m+1) Y) (u : Y → EReal)
    (hu : IsThetaPshPotential θ.val u)
    (σ : ClosedRealOneOneForm (m+1) X) (v : X → EReal)
    (hv : IsThetaPshPotential σ.val v)
    (hpush : currentPushforward hπ.1 (thetaPotentialCurrent θ.val u hu) =
      thetaPotentialCurrent σ.val v hv) :
    currentPushforward hπ.1
      (thetaPotentialCurrent (θ+ClosedRealOneOneForm.pullback hπ.1 ω.form).val u
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hu
          (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ω.isSemipositive))) =
      thetaPotentialCurrent (σ+ω.form).val v
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hv ω.isSemipositive) := by
  rw [thetaPotentialCurrent_semipositive_add θ _ u hu
      (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ω.isSemipositive)]
  have hadd := (currentPushforwardLM hπ.1).map_add
    (thetaPotentialCurrent θ.val u hu)
    (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m+1))
      (k := degreeTwo (Nat.succ_pos m)) (ClosedRealOneOneForm.pullback hπ.1 ω.form).val)
  change currentPushforward hπ.1 _ = currentPushforward hπ.1 _ +
    currentPushforward hπ.1 _ at hadd
  have hsm : currentPushforward hπ.1
      (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m+1))
        (k := degreeTwo (Nat.succ_pos m)) (ClosedRealOneOneForm.pullback hπ.1 ω.form).val) =
      GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m+1))
        (k := degreeTwo (Nat.succ_pos m)) ω.form.val := by
    simpa only [ClosedRealOneOneForm.pullback_val] using
      (currentPushforward_smoothGlobalCurrent_pullback hπ
        (k := degreeTwo (Nat.succ_pos m)) ω.form.val)
  rw [hadd,hpush,hsm,
    thetaPotentialCurrent_semipositive_add σ ω.form v hv ω.isSemipositive]

/-- Whole original potential goodness is preserved by actual current pushforward.
The original presentation may have ZERO mass. All positivity and bigness used
by the mass criterion are produced internally after a genuine smooth shift. -/
theorem sourceIGood_pushforward_presentations {π : Y → X}
    (hπ : IsAnalyticModification (n := m+1) π)
    (ωX : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    (θ : ClosedRealOneOneForm (m+1) Y) (u : Y → EReal)
    (hu : IsThetaPshPotential θ.val u)
    (σ : ClosedRealOneOneForm (m+1) X) (v : X → EReal)
    (hv : IsThetaPshPotential σ.val v)
    (hpush : currentPushforward hπ.1 (thetaPotentialCurrent θ.val u hu) =
      thetaPotentialCurrent σ.val v hv)
    (hgood : sourceIGood (n := m+1) u) : sourceIGood (n := m+1) v := by
  let θE := θ+ClosedRealOneOneForm.pullback hπ.1 ωX.form
  let σE := σ+ωX.form
  have huE : IsThetaPshPotential θE.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ωX.isSemipositive)
  have hvE : IsThetaPshPotential σE.val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv ωX.isSemipositive
  have hpushE : currentPushforward hπ.1 (thetaPotentialCurrent θE.val u huE) =
      thetaPotentialCurrent σE.val v hvE :=
    enlarged_current_pushforward hπ ωX θ u hu σ v hv hpush
  have hmass : diagonalPotentialMass σE v hvE = diagonalPotentialMass θE u huE :=
    SGPT.NPP.MassPushforward.globalMixedMeasure_univ_pushforward hπ
      (fun _ => θE) (fun _ => u) (fun _ => huE)
      (fun _ => σE) (fun _ => v) (fun _ => hvE) (fun _ => hpushE)
  have hposX : HasPositivePotentialMass σE v hvE := by
    have h := sourcePositiveMass_add_kahler ωX (isThetaPSH_nativeClosedFormToAtlas hv)
    simpa only [HasPositivePotentialMass,diagonalPotentialMass,σE,
      sourcePotentialNonPluripolarMeasure,sourceNativeClosedForm_add,
      sourceNativeAtlasForm_roundTrip] using h
  have hposY : HasPositivePotentialMass θE u huE := by
    change 0 < diagonalPotentialMass θE u huE
    rw [← hmass]
    exact hposX
  have hposYs : 0 < sourcePotentialNonPluripolarMeasure (nativeClosedFormToAtlas θE) u
      (isThetaPSH_nativeClosedFormToAtlas huE) univ := by
    simpa only [HasPositivePotentialMass,diagonalPotentialMass,
      sourcePotentialNonPluripolarMeasure,sourceNativeAtlasForm_roundTrip] using hposY
  have hgYs := (sourceIGood_iff_with_positive_background ωY
    (isThetaPSH_nativeClosedFormToAtlas huE) hposYs).mp hgood
  have hgY : IGoodWith θE u huE := by
    have h := (sourceIGoodWith_iff_native (nativeClosedFormToAtlas θE) u
      (isThetaPSH_nativeClosedFormToAtlas huE)).mp hgYs
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  have hbigY := BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
    (Nat.succ_pos m) ωY θE huE hposY
  have hbigX := BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
    (Nat.succ_pos m) ωX σE hvE hposX
  have hcritY := BigClassIGoodMassCriterion.iGoodWith_iff_actual_mass_eq_iVolume
    ωY θE hbigY huE hposY
  have hcritX := BigClassIGoodMassCriterion.iGoodWith_iff_actual_mass_eq_iVolume
    ωX σE hbigX hvE hposX
  have hI := sourceIVolume_pushforward_presentations hπ ωX ωY θE u huE σE v hvE hpushE
  have hIY := sourceIVolume_eq_native (nativeClosedFormToAtlas θE) u
    (isThetaPSH_nativeClosedFormToAtlas huE)
    (by simpa only [sourceNativeAtlasForm_roundTrip] using huE.1.hasSmoothLocalPotentials)
  have hIX := sourceIVolume_eq_native (nativeClosedFormToAtlas σE) v
    (isThetaPSH_nativeClosedFormToAtlas hvE)
    (by simpa only [sourceNativeAtlasForm_roundTrip] using hvE.1.hasSmoothLocalPotentials)
  rw [hIX,hIY] at hI
  simp only [sourceNativeAtlasForm_roundTrip] at hI
  have hgX : IGoodWith σE v hvE := hcritX.mpr (hmass.trans ((hcritY.mp hgY).trans hI.symm))
  apply (sourceIGood_iff_native v).mpr
  exact ⟨σE,hvE,hgX⟩

end SGPT.Hodge.BDivChain.SourceIGoodPushDraft

namespace SGPT.Hodge.BDivChain.SourceIGoodPushAnyDraft
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.NPP
  SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourcePushforwardDraft
  SGPT.Hodge.BDivChain.SourcePushforwardAnyDraft
  SGPT.Hodge.BDivChain.SourceIGoodPushDraft

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [ConnectedSpace X] [ConnectedSpace Y]

/-- Original current I-goodness: an actual theta+ddc(u) presentation whose
potential satisfies the source definition. The presentation's mass may be zero. -/
def currentIGoodAny (T : ClosedPositive (n := n) (X := X)) : Prop :=
  ∃ (θ : ClosedRealOneOneForm n X) (u : X → EReal),
    IsPresentationAny T θ u ∧ sourceIGood (n := n) u

/-- Every genuine degree-two chart current in dimension0 has an internally
constructed genuine I-good source presentation. -/
theorem currentIGoodAny_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    (T : ClosedPositive (n := 0) (X := M)) : currentIGoodAny T := by
  let θ := nativeClosedFormToAtlas (0 : ClosedRealOneOneForm 0 M)
  have h0 : (ofFixedModel 0 M).IsThetaPSH θ (fun _ => (0 : EReal)) :=
    SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0
  let u := sourceIEnvelope θ (fun _ => (0 : EReal))
  have hu : (ofFixedModel 0 M).IsThetaPSH θ u := isThetaPSH_sourceIEnvelope h0
  refine ⟨atlasClosedFormToNative θ,u,?_,(sourceIEnvelope_iGood_of_dim_zero θ _ h0).iGood⟩
  exact (isPresentationAny_iff_zero T _ u).mpr
    (isPresentationZero_of_isThetaPshPotential T _
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu))

/-- All original dimensions, all original proper analytic modifications, all
original I-good currents, including zero original presentation mass. -/
theorem currentIGoodAny_pushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (T : ClosedPositive (n := n) (X := Y)) (hgood : currentIGoodAny T) :
    currentIGoodAny (pushCurrentAny hπ T) := by
  cases n with
  | zero => exact currentIGoodAny_zero _
  | succ m =>
    obtain ⟨θ,u,hT,hgu⟩ := hgood
    let S := pushCurrentAny hπ T
    let σ := atlasClosedFormToNative (currentPresentationBackground S)
    let v := currentPresentationPotential S
    have hS : IsPresentationAny S σ v := currentPresentation_isPresentation S
    obtain ⟨hu,hTr⟩ := (isPresentationAny_iff_book T θ u).mp hT
    obtain ⟨hv,hSr⟩ := (isPresentationAny_iff_book S σ v).mp hS
    have hraw : currentPushforward hπ.1 (toBookCurrent T).current =
        (toBookCurrent S).current := by
      change currentPushforward hπ.1 (toBookCurrent T).current =
        (toBookCurrent (pushCurrentAny hπ T)).current
      rw [pushCurrentAny_pos,toBookCurrent_ofBookCurrent]
      rfl
    have hpush : currentPushforward hπ.1 (thetaPotentialCurrent θ.val u hu) =
        thetaPotentialCurrent σ.val v hv := by
      rw [← hTr, hraw, hSr]
    exact ⟨σ,v,hS,sourceIGood_pushforward_presentations hπ ωX ωY θ u hu σ v hv hpush hgu⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- WHOLE original cor:Igoodpush. Target compactness and connectedness are
produced from the original source and actual map, not caller assumptions. -/
theorem source_Igoodpush {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (T : ClosedPositive (n := n) (X := Y)) (hgood : currentIGoodAny T) :
    letI : CompactSpace X := compact_target_of_original_modification hπ
    letI : ConnectedSpace X := connected_target_of_original_modification hπ
    currentIGoodAny (pushCurrentAny hπ T) := by
  let : CompactSpace X := compact_target_of_original_modification hπ
  let : ConnectedSpace X := connected_target_of_original_modification hπ
  exact currentIGoodAny_pushforward hπ ωX ωY T hgood

end SGPT.Hodge.BDivChain.SourceIGoodPushAnyDraft
