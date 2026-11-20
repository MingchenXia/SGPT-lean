import SGPT.Hodge.SourceSiuClassSeries
import SGPT.Hodge.SourceDivisorCoefficientRealization
import SGPT.Hodge.SourceRegFamily
import SGPT.Hodge.SourceCurrentCorrespondence
import SGPT.Hodge.SourceCurrentSmoothShift

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The same actual cohomology class of the actual geometric prime. In dimension
zero the original prime carrier is genuinely empty. -/
def primeDivisorClassAny (D : SGPT.PSH.GeometricPrimeCarrier n X) : RealBottChern n X := by
  cases n with
  | zero => exact isEmptyElim D
  | succ m => exact primeDivisorClass D

def HasDivisorClassSumAny (c : SGPT.PSH.GeometricPrimeCarrier n X → ℝ)
    (α : RealBottChern n X) : Prop :=
  letI := SGPT.BDivisor.euclideanTopology (RealBottChern n X)
  HasSum (fun D => c D • primeDivisorClassAny D) α

theorem hasDivisorClassSumAny_pos {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]
    (c : SGPT.PSH.GeometricPrimeCarrier (m+1) M → ℝ) (α : RealBottChern (m+1) M) :
    HasDivisorClassSumAny c α ↔ HasDivisorClassSum c α := Iff.rfl

/-- Actual generic Lelong coefficient of the actual source current. -/
def currentCoefficientAny (T : ClosedPositive (n := n) (X := X))
    (D : SGPT.PSH.GeometricPrimeCarrier n X) : ℝ := by
  cases n with
  | zero => exact isEmptyElim D
  | succ m => exact (SGPT.Siu.bookGenericLelong (toBookCurrent T) D).toReal

theorem currentCoefficientAny_nonneg (T : ClosedPositive (n := n) (X := X))
    (D : SGPT.PSH.GeometricPrimeCarrier n X) : 0 ≤ currentCoefficientAny T D := by
  cases n with
  | zero => exact isEmptyElim D
  | succ m => exact ENNReal.toReal_nonneg

/-- Literal actual current addition, retaining the source distribution carrier. -/
def addCurrentAny (T S : ClosedPositive (n := n) (X := X)) : ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact T
  | succ m =>
    exact ofBookCurrent (SGPT.Siu.toBookCurrent ((toBookCurrent T).current+(toBookCurrent S).current)
      ((SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)).add
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent S))))

theorem toBookCurrent_addCurrentAny {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]
    (T S : ClosedPositive (n := m+1) (X := M)) :
    (toBookCurrent (addCurrentAny T S)).current = (toBookCurrent T).current+(toBookCurrent S).current := by
  simp only [addCurrentAny,toBookCurrent_ofBookCurrent,SGPT.Siu.toBookCurrent_current]

theorem addCurrentAny_class (T S : ClosedPositive (n := n) (X := X)) :
    currentClassAny (addCurrentAny T S)=currentClassAny T+currentClassAny S := by
  cases n with
  | zero => change (0 : RealBottChern 0 X)=0+0; simp
  | succ m =>
    change SGPT.PSH.BookCurrent.currentClass (toBookCurrent (addCurrentAny T S)) = _
    unfold SGPT.PSH.BookCurrent.currentClass
    have he : (toBookCurrent (addCurrentAny T S)).val =
        (toBookCurrent T).val+(toBookCurrent S).val :=
      Subtype.ext (toBookCurrent_addCurrentAny T S)
    rw [he,bottChernClass_add']
    rfl

/-- Actual full divisorial current, rather than just its coefficient list. -/
def divisorCurrentAny (T : ClosedPositive (n := n) (X := X)) : ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact closedPositiveZeroDim
  | succ m =>
    exact ofBookCurrent (SGPT.Siu.toBookCurrent
      (SGPT.Siu.siuDivisorialPart (toBookCurrent T).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)))
      (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))))

theorem toBookCurrent_divisorCurrentAny {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]
    (T : ClosedPositive (n := m+1) (X := M)) :
    (toBookCurrent (divisorCurrentAny T)).current = SGPT.Siu.siuDivisorialPart (toBookCurrent T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) := by
  simp only [divisorCurrentAny,toBookCurrent_ofBookCurrent,SGPT.Siu.toBookCurrent_current]

theorem current_decomposition_any (T : ClosedPositive (n := n) (X := X)) :
    T = addCurrentAny (regularCurrentAny T) (divisorCurrentAny T) := by
  cases n with
  | zero => rfl
  | succ m =>
    apply (fun h => (ofBookCurrent_toBookCurrent T).symm.trans
      ((congrArg ofBookCurrent h).trans (ofBookCurrent_toBookCurrent _)))
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    rw [toBookCurrent_addCurrentAny,toBookCurrent_divisorCurrentAny,regularCurrentAny_pos]
    exact (SGPT.Siu.siu_decomposition
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))).1

variable [ConnectedSpace X]

/-- Original Siu class series converges on the entire geometric prime index,
in every natural dimension, with no supplied enumeration or limit certificate. -/
theorem hasDivisorClassSumAny_divisorCurrent (ω : KahlerBackground n X)
    (T : ClosedPositive (n := n) (X := X)) :
    HasDivisorClassSumAny (currentCoefficientAny T) (currentClassAny (divisorCurrentAny T)) := by
  cases n with
  | zero =>
    let := SGPT.BDivisor.euclideanTopology (RealBottChern 0 X)
    change HasSum (fun D : SGPT.PSH.GeometricPrimeCarrier 0 X => _)
      (0 : RealBottChern 0 X)
    exact hasSum_empty
  | succ m =>
    change HasDivisorClassSum (fun D => (SGPT.Siu.bookGenericLelong (toBookCurrent T) D).toReal) _
    simp_rw [SGPT.Siu.bookGenericLelong_eq]
    have h := hasDivisorClassSum_siuDivisorialPart ω
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))
    have he : (toBookCurrent (divisorCurrentAny T)).val =
        ⟨SGPT.Siu.siuDivisorialPart (toBookCurrent T).current
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)),
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))).1,
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart
            (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))).2.1⟩ :=
      Subtype.ext (toBookCurrent_divisorCurrentAny T)
    change HasDivisorClassSum _ (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
      (toBookCurrent (divisorCurrentAny T)).val)
    rw [he]
    exact h

omit [ConnectedSpace X] in
/-- The sum in the literal source decomposition computes the original current class. -/
theorem currentClassAny_decomposition (T : ClosedPositive (n := n) (X := X)) :
    currentClassAny T = currentClassAny (regularCurrentAny T)+currentClassAny (divisorCurrentAny T) := by
  calc currentClassAny T = currentClassAny (addCurrentAny (regularCurrentAny T) (divisorCurrentAny T)) :=
      congrArg currentClassAny (current_decomposition_any T)
    _ = _ := addCurrentAny_class _ _

omit [ConnectedSpace X] in
/-- The actual regular current is nondivisorial, internally. -/
theorem regularCurrentAny_idempotent (T : ClosedPositive (n := n) (X := X)) :
    regularCurrentAny T = regularCurrentAny (regularCurrentAny T) := by
  cases n with
  | zero => rfl
  | succ m =>
    apply (fun h => (ofBookCurrent_toBookCurrent _).symm.trans
      ((congrArg ofBookCurrent h).trans (ofBookCurrent_toBookCurrent _)))
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    simp only [regularCurrentAny_pos]
    exact (SGPT.Siu.isNonDivisorial_iff
      (SGPT.Siu.isClosedPositiveCurrent_siuRegularPart
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)))).mpr
      (SGPT.Siu.currentGenericLelong_siuRegularPart
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)))

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
