import SGPT.Hodge.SourceRegMixedIVolume
import SGPT.PSH.SourceBimeromorphicMixedIVolume
import SGPT.NPP.MassPushforwardInvariance

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourcePushforwardDraft
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.BDivisor SGPT.BDivisor.PrimePushforward

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]
  [CompactSpace X] [CompactSpace Y]
local notation "CurX" => GlobalCurrent (m+1) X (degreeTwo (Nat.succ_pos m))
local notation "CurY" => GlobalCurrent (m+1) Y (degreeTwo (Nat.succ_pos m))

/-- Pushforward of the ACTUAL full divisorial part of every original positive current. -/
theorem currentPushforward_siuDivisorialPart
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    currentPushforward hπ.1 (SGPT.Siu.siuDivisorialPart T hT) =
      SGPT.Siu.siuDivisorialPart (currentPushforward hπ.1 T)
        (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT) := by
  classical
  have hP := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hP
  intro d η
  have h1 := hasSum_currentPushforward_inChart hπ.1
    (A := fun D' : SGPT.PSH.GeometricPrimeCarrier (m+1) Y =>
      (SGPT.Siu.currentGenericLelong T hT D').toReal • SGPT.Siu.primeDivisorCurrent D')
    (B := SGPT.Siu.siuDivisorialPart T hT)
    (fun e η => SGPT.Siu.hasSum_siuDivisorialPart hT e η) d η
  have hzero : ∀ D' ∉ Set.range (SGPT.Siu.strictTransformPrime hπ),
      (currentPushforward hπ.1
        ((SGPT.Siu.currentGenericLelong T hT D').toReal •
          SGPT.Siu.primeDivisorCurrent D')).inChart d η = 0 := by
    intro D' hD'
    have hexc : D'.val ⊆ exceptionalLocus (m+1) π := by
      by_contra h
      obtain ⟨D, hD⟩ := exists_eq_strictTransformPrime hπ D' h
      exact hD' ⟨D,hD⟩
    rw [currentPushforward_smul, currentPushforward_primeDivisorCurrent_eq_zero hπ D' hexc,
      smul_zero]
    rfl
  rw [← (strictTransformPrime_injective hπ).hasSum_iff hzero] at h1
  convert h1 using 1
  funext D
  simp only [Function.comp_apply]
  rw [currentPushforward_smul, currentPushforward_primeDivisorCurrent_strictTransformPrime,
    SGPT.Siu.currentGenericLelong_currentPushforward hπ hT]

/-- Actual full-current Reg commutes with pushforward, with no nondivisorial input. -/
theorem currentPushforward_siuRegularPart
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    currentPushforward hπ.1 (SGPT.Siu.siuRegularPart T hT) =
      SGPT.Siu.siuRegularPart (currentPushforward hπ.1 T)
        (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT) := by
  unfold SGPT.Siu.siuRegularPart
  rw [currentPushforward_sub,currentPushforward_siuDivisorialPart hπ hT]

/-- The ACTUAL regular part of pull-push is RegT for EVERY positive T.
The required nondivisoriality of RegT is produced, not a source hypothesis. -/
theorem siuRegularPart_pullPush_any
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    SGPT.Siu.siuRegularPart (Modification4.pullPush hπ T hT)
      (Modification4.isClosedPositiveCurrent_pullPush hπ hT) =
      SGPT.Siu.siuRegularPart T hT := by
  let hP := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT
  let R := SGPT.Siu.siuRegularPart T hT
  let hR := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hT
  let P := SGPT.Siu.toBookCurrent (currentPushforward hπ.1 T) hP
  let M : Modification (m+1) X :=
    { carrier := Y, map := π, isAnalyticModification := hπ }
  have hnd : SGPT.Siu.IsNonDivisorial R hR :=
    (SGPT.Siu.isNonDivisorial_iff hR).mpr (SGPT.Siu.currentGenericLelong_siuRegularPart hT)
  have hA := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hR
  have hB := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hP
  have hC := SGPT.Hodge.BDivChain.SourceReg.regPull_congr M hA hB
    (currentPushforward_siuRegularPart hπ hT)
  have hF := SGPT.Hodge.BDivChain.SourceReg.regPull_regular_eq M P
  have hI := SGPT.Hodge.BDivChain.siuRegularPart_pullPush hπ hR hnd
  exact (hC.trans hF).symm.trans hI

/-- The genuine actual original pushforward on the existing whole-current carrier. -/
def bookPush {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  SGPT.Siu.toBookCurrent (currentPushforward hπ.1 T.current)
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))

/-- The same original actual pull-push, as a positive current; no representative is supplied. -/
def bookPullPush {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y :=
  SGPT.Siu.toBookCurrent (Modification4.pullPush hπ T.current
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
    (Modification4.isClosedPositiveCurrent_pullPush hπ
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))

/-- Exact whole-current regularity readback for every original source representative. -/
theorem bookPullPush_regular
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y) :
    SGPT.Siu.bookSiuRegularPart (bookPullPush hπ T) = SGPT.Siu.bookSiuRegularPart T :=
  SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    (siuRegularPart_pullPush_any hπ (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y]

/-- The previously accepted actual mixed pullback theorem reads this exact pull-push tuple. -/
theorem mixed_bookPullPush_eq_push
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ωX : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    (T : Fin (m+1) → SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y) :
    SGPT.Hodge.BDivChain.SourceRegCone.mixed ωY (fun i => bookPullPush hπ (T i)) =
      SGPT.Hodge.BDivChain.SourceRegCone.mixed ωX (fun i => bookPush hπ (T i)) := by
  rw [SGPT.Hodge.BDivChain.SourceRegCone.mixed_eq_existing,
    SGPT.Hodge.BDivChain.SourceRegCone.mixed_eq_existing]
  simpa only [bookPullPush,bookPush,Modification4.pullPush,
    SGPT.Siu.toBookCurrent,SGPT.PSH.BookCurrent.ClosedPositiveCurrent.current] using
    SGPT.PSH.VariableComplexAtlas.sourceCurrentMixedIVolume_modification_pullback hπ ωX ωY
      (fun i => (bookPush hπ (T i)).current)
      (fun i => (bookPush hπ (T i)).isClosed)
      (fun i => (bookPush hπ (T i)).isTypeOneOne)
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (bookPush hπ (T i))).2.2)

/-- The literal original mixed I-volume is invariant under pushforward for EVERY input current. -/
theorem mixed_bookPush_eq
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ωX : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    (T : Fin (m+1) → SGPT.PSH.BookCurrent.ClosedPositiveCurrent m Y) :
    SGPT.Hodge.BDivChain.SourceRegCone.mixed ωX (fun i => bookPush hπ (T i)) =
      SGPT.Hodge.BDivChain.SourceRegCone.mixed ωY T := by
  calc
    _ = SGPT.Hodge.BDivChain.SourceRegCone.mixed ωY (fun i => bookPullPush hπ (T i)) :=
      (mixed_bookPullPush_eq_push hπ ωX ωY T).symm
    _ = SGPT.Hodge.BDivChain.SourceRegCone.mixed ωY
        (fun i => SGPT.Hodge.BDivChain.SourceRegCone.regular (bookPullPush hπ (T i))) :=
      (SGPT.Hodge.BDivChain.SourceRegCone.mixed_regular ωY _).symm
    _ = SGPT.Hodge.BDivChain.SourceRegCone.mixed ωY
        (fun i => SGPT.Hodge.BDivChain.SourceRegCone.regular (T i)) := by
      congr 1
      funext i
      exact bookPullPush_regular hπ (T i)
    _ = _ := SGPT.Hodge.BDivChain.SourceRegCone.mixed_regular ωY T

/-- Whole positive-dimensional cor:vol_inv_push on the ORIGINAL raw current tuple.
No selected potentials, I-goodness, mass positivity or nondivisoriality are inputs. -/
theorem sourceCurrentMixedIVolume_modification_pushforward
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ωX : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    (T : Fin (m+1) → CurY)
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m+1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hp : ∀ i, GlobalPositiveCurrentACRestriction.IsFullPositive (T i)) :
    SGPT.PSH.VariableComplexAtlas.sourceCurrentMixedIVolume ωX
      (fun i => currentPushforward hπ.1 (T i))
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1
        ⟨hc i,h11 i,hp i⟩).1)
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1
        ⟨hc i,h11 i,hp i⟩).2.1)
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1
        ⟨hc i,h11 i,hp i⟩).2.2) =
      SGPT.PSH.VariableComplexAtlas.sourceCurrentMixedIVolume ωY T hc h11 hp := by
  let B i := SGPT.Siu.toBookCurrent (T i) ⟨hc i,h11 i,hp i⟩
  have h := mixed_bookPush_eq hπ ωX ωY B
  rw [SGPT.Hodge.BDivChain.SourceRegCone.mixed_eq_existing,
    SGPT.Hodge.BDivChain.SourceRegCone.mixed_eq_existing] at h
  exact h

end SGPT.Hodge.BDivChain.SourcePushforwardDraft

namespace SGPT.Hodge.BDivChain.SourcePushforwardAnyDraft
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourcePushforwardDraft SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [CompactSpace X] [CompactSpace Y]

/-- The actual original current pushforward, including the unique genuine degree-two
current in dimension0. Positive dimensions use the original distributional pushforward. -/
def pushCurrentAny {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (T : ClosedPositive (n := n) (X := Y)) : ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact closedPositiveZeroDim
  | succ m => exact ofBookCurrent (bookPush hπ (toBookCurrent T))

/-- Exact positive-dimensional readback, without supplied current representatives. -/
theorem pushCurrentAny_pos {d : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel (d+1)) M] [IsComplexManifold (d+1) M]
    [ChartedSpace (ComplexModel (d+1)) N] [IsComplexManifold (d+1) N]
    [CompactSpace M] [CompactSpace N] {π : N → M}
    (hπ : IsAnalyticModification (n := d+1) π) (T : ClosedPositive (n := d+1) (X := N)) :
    pushCurrentAny hπ T = ofBookCurrent (bookPush hπ (toBookCurrent T)) := rfl

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y]

/-- WHOLE all-dimensional source mixed pushforward identity, including actual empty tuples. -/
theorem currentMixedIVolumeAny_modification_pushforward
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (T : Fin n → ClosedPositive (n := n) (X := Y)) :
    currentMixedIVolumeAny ωX (fun i => pushCurrentAny hπ (T i)) =
      currentMixedIVolumeAny ωY T := by
  cases n with
  | zero =>
    let θ : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 X) :=
      fun i => currentPresentationBackground (pushCurrentAny hπ (T i))
    let v : Fin 0 → X → EReal := fun i => currentPresentationPotential (pushCurrentAny hπ (T i))
    have hv i : (ofFixedModel 0 X).IsThetaPSH (θ i) (v i) :=
      presentationPSH (pushCurrentAny hπ (T i))
    have h := sourceGeneralMixedIVolume_modification_pullback hπ ωX ωY θ v hv
    have hθ : (fun i => nativeClosedFormToAtlas
        (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ i)))) =
        (fun i => currentPresentationBackground (T i)) := funext fun i => Fin.elim0 i
    have hvv : (fun i => v i ∘ π) = (fun i => currentPresentationPotential (T i)) :=
      funext fun i => Fin.elim0 i
    symm
    simpa only [currentMixedIVolumeAny,hθ,hvv,θ,v] using h
  | succ m =>
    simpa only [SGPT.Hodge.BDivChain.SourceRegCone.mixed,pushCurrentAny_pos,
      ofBookCurrent_toBookCurrent] using
      mixed_bookPush_eq hπ ωX ωY (fun i => toBookCurrent (T i))

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- Target compactness is produced from the ORIGINAL compact source and actual surjectivity. -/
theorem compact_target_of_original_modification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) : CompactSpace X := by
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  constructor
  rw [← hsurj.range_eq]
  exact isCompact_range hπ.1.continuous

omit [CompactSpace X] [CompactSpace Y] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- Target connectedness is likewise an OUTPUT of the original proper bimeromorphic data. -/
theorem connected_target_of_original_modification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) : ConnectedSpace X :=
  (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ).connectedSpace
    hπ.1.continuous

omit [CompactSpace X] [ConnectedSpace X] in
/-- WHOLE cor:vol_inv_push, without imposing compactness or connectedness on the original
Kähler TARGET as extra caller assumptions. They are internally produced from the source. -/
theorem source_vol_inv_push
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (T : Fin n → ClosedPositive (n := n) (X := Y)) :
    letI : CompactSpace X := compact_target_of_original_modification hπ
    letI : ConnectedSpace X := connected_target_of_original_modification hπ
    currentMixedIVolumeAny ωX (fun i => pushCurrentAny hπ (T i)) =
      currentMixedIVolumeAny ωY T := by
  let : CompactSpace X := compact_target_of_original_modification hπ
  let : ConnectedSpace X := connected_target_of_original_modification hπ
  exact currentMixedIVolumeAny_modification_pushforward hπ ωX ωY T

end SGPT.Hodge.BDivChain.SourcePushforwardAnyDraft
