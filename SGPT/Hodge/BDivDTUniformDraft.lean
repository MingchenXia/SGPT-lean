import SGPT.Hodge.BDivChainZeroSourceEndpointsDraft
import SGPT.Hodge.BDivChainDTVolume
import SGPT.Hodge.BDivVolumeNetRealDraft

/-!
# `thm:DT`: original currents in all dimensions

The input is the actual chart-compatible closed positive degree-two current.
Both dimension branches keep that same current, actual model family, form,
and potential; source volume is the I-envelope mass, not ordinary mass.
-/

set_option autoImplicit false
noncomputable section
universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain.NativeDraft.DTUniformDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [ConnectedSpace X]

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- Every actual closed positive current has a genuine native θ-psh
presentation with all the chart coefficients of that same current. -/
theorem exists_native_presentation (T : ClosedPositive (n := n) (X := X)) :
    ∃ (θ : ClosedRealOneOneForm n X) (u : X → EReal), IsPresentationAny T θ u := by
  cases n with
  | zero =>
    obtain ⟨θ, u, h⟩ := exists_presentation_zero T
    exact ⟨θ, u, (isPresentationAny_iff_zero T θ u).mpr h⟩
  | succ m =>
    obtain ⟨θ, u, h⟩ := SGPT.PSH.BookCurrent.exists_presentation (toBookCurrent T)
    exact ⟨θ, u, (isPresentationAny_iff_book T θ u).mpr h⟩

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- The same presentation as an actual source atlas closed form and the same
original extended-real potential. -/
theorem exists_source_presentation (T : ClosedPositive (n := n) (X := X)) :
    ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal),
      IsPresentationAny T (atlasClosedFormToNative θ) u := by
  obtain ⟨θ, u, h⟩ := exists_native_presentation T
  refine ⟨nativeClosedFormToAtlas θ, u, ?_⟩
  simpa only [sourceNativeAtlasForm_roundTrip] using h

/-- `thm:DT`, nef clause, for the same actual positive current in every
dimension and over the book's finite smooth-centre blowup models. -/
theorem currentBDivisorAnyOn_isNef (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X)) :
    IsNefAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) := by
  cases n with
  | zero => exact currentBDivisorAnyOn_isNef_zero _ T
  | succ m =>
    apply (isNefAny_iff_existing (Nat.succ_pos m) _).mpr
    rw [currentBDivisorAnyOn_eq_existing]
    exact SGPT.Hodge.BDivChain.currentBDivisor_isNef ω (toBookCurrent T)

/-- `thm:DT`, volume clause, for every actual source presentation of the
same current. The right side is the book's I-envelope volume. -/
theorem currentBDivisorAnyOn_vol_eq_sourceIVolume (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X))
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal)
    (hpres : IsPresentationAny T (atlasClosedFormToNative θ) u) :
    volumeAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) =
      sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hpres.choose) := by
  cases n with
  | zero => exact currentBDivisorAnyOn_vol_eq_sourceIVolume_zero _ T θ u hpres
  | succ m =>
    have hp : SGPT.PSH.BookCurrent.IsPresentation (toBookCurrent T)
        (atlasClosedFormToNative θ) u := (isPresentationAny_iff_book T _ _).mp hpres
    rw [volumeAny_eq_existing (Nat.succ_pos m), currentBDivisorAnyOn_eq_existing]
    change (currentBDivisor (toBookCurrent T)).vol = _
    rw [SGPT.Hodge.BDivChain.currentBDivisor_vol ω (toBookCurrent T) hp]
    symm
    exact sourceIVolume_eq_native θ u _
      (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ))

/-- Any two actual presentations of the same original current give the
same original source I-volume. -/
theorem sourceIVolume_eq_of_presentations (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X))
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u v : X → EReal)
    (hu : IsPresentationAny T (atlasClosedFormToNative θ) u)
    (hv : IsPresentationAny T (atlasClosedFormToNative σ) v) :
    sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hu.choose) =
      sourceIVolume σ v ((isThetaPSH_iff_nativeThetaPotential σ v).mpr hv.choose) :=
  (currentBDivisorAnyOn_vol_eq_sourceIVolume ω T θ u hu).symm.trans
    (currentBDivisorAnyOn_vol_eq_sourceIVolume ω T σ v hv)

/-- The complete conjunction includes presentation existence and preserves
the volume identity for EVERY actual presentation, not a selected witness. -/
theorem currentBDivisorAnyOn_DT (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X)) :
    IsNefAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) ∧
      (∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal),
        IsPresentationAny T (atlasClosedFormToNative θ) u) ∧
      (∀ (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal)
        (hpres : IsPresentationAny T (atlasClosedFormToNative θ) u),
        volumeAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) =
          sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hpres.choose)) :=
  ⟨currentBDivisorAnyOn_isNef ω T, exists_source_presentation T,
    fun θ u hpres => currentBDivisorAnyOn_vol_eq_sourceIVolume ω T θ u hpres⟩

/-- The source I-envelope volume of every actual presentation is finite. -/
theorem sourceIVolume_lt_top_of_presentation (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X))
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal)
    (hpres : IsPresentationAny T (atlasClosedFormToNative θ) u) :
    sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hpres.choose) < ⊤ := by
  rw [← currentBDivisorAnyOn_vol_eq_sourceIVolume ω T θ u hpres]
  exact volumeAny_lt_top_blowup ⟨ω⟩ _

/-- Real-valued reading of the same all-presentation identity. -/
theorem currentBDivisorAnyOn_realVol_eq_sourceIVolume (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X))
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : X → EReal)
    (hpres : IsPresentationAny T (atlasClosedFormToNative θ) u) :
    volumeRealAny (currentBDivisorAnyOn (ModelSystem.blowup n X) T) =
      (sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hpres.choose)).toReal :=
  congrArg ENNReal.toReal (currentBDivisorAnyOn_vol_eq_sourceIVolume ω T θ u hpres)

end SGPT.Hodge.BDivChain.NativeDraft.DTUniformDraft
