import SGPT.Hodge.SourceBigNefIntersection

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceReg
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X]

/-- Equality transport keeps both actual current positivity witnesses internal to the reader. -/
theorem regPull_congr (π : Modification (m+1) X)
    {A B : GlobalCurrent (m+1) X (degreeTwo (Nat.succ_pos m))}
    (hA : SGPT.Siu.IsClosedPositiveCurrent A) (hB : SGPT.Siu.IsClosedPositiveCurrent B)
    (h : A = B) : π.regPull A hA = π.regPull B hB := by
  subst B
  rfl

/-- Reg of the actual pullback is unchanged when the original current is replaced by Reg. -/
theorem regPull_regular_eq (π : Modification (m+1) X)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    π.regPull (SGPT.Siu.bookSiuRegularPart T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (SGPT.Siu.bookSiuRegularPart T)) =
    π.regPull T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T) := by
  let hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  let P := Modification4.pull π.isAnalyticModification T.current hT
  let hP := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT
  let R := SGPT.Siu.siuRegularPart P hP
  let hR := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hP
  have hnd : SGPT.Siu.IsNonDivisorial R hR :=
    (SGPT.Siu.isNonDivisorial_iff hR).mpr (SGPT.Siu.currentGenericLelong_siuRegularPart hP)
  have hpush : currentPushforward π.isAnalyticModification.1 R =
      SGPT.Siu.siuRegularPart T.current hT :=
    PrimePushforward.currentPushforward_siuRegularPart_pull π.isAnalyticModification hT
  have h := SGPT.Hodge.BDivChain.siuRegularPart_pullPush π.isAnalyticModification hR hnd
  have hA := SGPT.Siu.isClosedPositiveCurrent_currentPushforward π.isAnalyticModification.1 hR
  have hp := regPull_congr π hA (SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hT) hpush
  exact hp.symm.trans h


/-- The SAME complete original model family, not a selected-trace or volume proxy. -/
theorem currentBDivisor_regular_eq (S : ModelSystem (m+1) X)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    currentBDivisorOn S (SGPT.Siu.bookSiuRegularPart T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (SGPT.Siu.bookSiuRegularPart T)) =
    currentBDivisorOn S T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T) := by
  ext π
  change π.1.regPullClass _ _ = π.1.regPullClass _ _
  apply SGPT.Hodge.BDivChain.bottChernClass_congr
  exact regPull_regular_eq π.1 T

section Uniform
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Entire original book-model family is unchanged, all dimensions included. -/
theorem currentBDivisorAnyOn_regular_eq
    (T : ClosedPositive (n := n) (X := M)) :
    currentBDivisorAnyOn (ModelSystem.blowup n M) (regularCurrentAny T) =
      currentBDivisorAnyOn (ModelSystem.blowup n M) T := by
  cases n with
  | zero => rfl
  | succ d =>
    apply family_eq_of_toExisting_eq (Nat.succ_pos d)
    rw [currentBDivisorAnyOn_eq_existing, currentBDivisorAnyOn_eq_existing,
      regularCurrentAny_pos]
    exact currentBDivisor_regular_eq _ (toBookCurrent T)

variable [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
/-- Actual independent original I-volume, not a value defined by this desired equality. -/
theorem currentIVolumeAny_regular_eq (ω : KahlerBackground n M)
    (T : ClosedPositive (n := n) (X := M)) :
    currentIVolumeAny (regularCurrentAny T) = currentIVolumeAny T := by
  rw [currentIVolumeAny_eq_bdivisorVolume ω, currentIVolumeAny_eq_bdivisorVolume ω,
    currentBDivisorAnyOn_regular_eq]
end Uniform

end SGPT.Hodge.BDivChain.SourceReg
