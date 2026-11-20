import SGPT.Hodge.BDivChainReal
import SGPT.Hodge.ExceptionalNegativity
import SGPT.Hodge.BDivDTUniformDraft

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.BDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- Nondivisoriality is produced from the actual class/root equality, never assumed. -/
theorem isNonDivisorial_of_root_eq_currentClass
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (hroot : (currentBDivisor T).root = SGPT.PSH.BookCurrent.currentClass T) :
    SGPT.Siu.IsNonDivisorial T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T) := by
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  have hR := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hT
  have hD := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT
  let R : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    ⟨SGPT.Siu.siuRegularPart T.current hT, hR.1, hR.2.1⟩
  let D : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    ⟨SGPT.Siu.siuDivisorialPart T.current hT, hD.1, hD.2.1⟩
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) R =
      SGPT.PSH.BookCurrent.currentClass T :=
    (currentBDivisorOn_root (ModelSystem.blowup (m + 1) X) hT).symm.trans hroot
  have hsum : T.val = R + D := by
    apply Subtype.ext
    exact (SGPT.Siu.siu_decomposition hT).1
  have hz : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) D = 0 := by
    have hc : SGPT.PSH.BookCurrent.currentClass T =
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) R +
          bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) D := by
      change bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T.val = _
      rw [hsum, bottChernClass_add']
    rw [hclass] at hc
    exact add_left_cancel (hc.symm.trans (add_zero _).symm)
  have hzero : SGPT.Siu.siuDivisorialPart T.current hT = 0 :=
    SGPT.Hodge.Exceptional.eq_zero_of_bottChernClass_eq_zero hD hz
  change T.current = SGPT.Siu.siuRegularPart T.current hT
  unfold SGPT.Siu.siuRegularPart
  rw [hzero]
  apply GlobalCurrent.ext
  intro e η
  change T.current.inChart e η = T.current.inChart e η - 0
  exact (sub_zero _).symm

end SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

namespace SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [CompactSpace Y] [ConnectedSpace Y]

/-- The original T=RegT conclusion is produced on the actual all-dimensional current carrier. -/
theorem current_eq_regular_of_root_eq_class (T : ClosedPositive (n := n) (X := Y))
    (hroot : (currentBDivisorAnyOn (ModelSystem.blowup n Y) T).val ModelSystem.Model.root =
      currentClassAny T) : T = regularCurrentAny T := by
  cases n with
  | zero => rfl
  | succ m =>
    have he := congrArg (fun D : BlowupWeilBDivisor (m + 1) Y (Nat.succ_pos m) => D.root)
      (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) Y) T)
    have hr : (currentBDivisor (toBookCurrent T)).root =
        SGPT.PSH.BookCurrent.currentClass (toBookCurrent T) := he.symm.trans hroot
    have hnd := isNonDivisorial_of_root_eq_currentClass (toBookCurrent T) hr
    have hbook : toBookCurrent T = SGPT.Siu.bookSiuRegularPart (toBookCurrent T) :=
      SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext hnd
    calc T = ofBookCurrent (toBookCurrent T) := (ofBookCurrent_toBookCurrent T).symm
      _ = ofBookCurrent (SGPT.Siu.bookSiuRegularPart (toBookCurrent T)) :=
        congrArg ofBookCurrent hbook
      _ = regularCurrentAny T := rfl

end SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
