import SGPT.Hodge.SourceCurrentObjects

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

/-- Actual current nondivisoriality agrees with the original native current condition. -/
theorem nonDivisorial_toBookCurrent {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y]
    (T : ClosedPositive (n := m + 1) (X := Y)) (hT : T = regularCurrentAny T) :
    SGPT.Siu.IsNonDivisorial (toBookCurrent T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) :=
  congrArg SGPT.PSH.BookCurrent.ClosedPositiveCurrent.current
    ((congrArg toBookCurrent hT).trans (regularCurrentAny_pos T))

omit [ConnectedSpace X] in
/-- The actual regular-current root formula in every natural dimension. -/
theorem currentBDivisorAnyOn_root_of_regular (T : ClosedPositive (n := n) (X := X))
    (hT : T = regularCurrentAny T) :
    (currentBDivisorAnyOn (ModelSystem.blowup n X) T).val ModelSystem.Model.root = currentClassAny T := by
  cases n with
  | zero => rfl
  | succ m =>
    have he := congrArg (fun D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m) => D.root)
      (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) T)
    exact he.trans (currentBDivisorOn_root_of_nonDivisorial (ModelSystem.blowup (m + 1) X)
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))
      (nonDivisorial_toBookCurrent T hT))

omit [ConnectedSpace X] in
/-- Descent of the SAME actual entire family under the original two current I-orders. -/
theorem currentBDivisorAnyOn_eq_of_currentIEquivalent
    {T S : ClosedPositive (n := n) (X := X)} (hclass : currentClassAny T = currentClassAny S)
    (hTS : currentIOrderAny T S) (hST : currentIOrderAny S T) :
    currentBDivisorAnyOn (ModelSystem.blowup n X) T =
      currentBDivisorAnyOn (ModelSystem.blowup n X) S := by
  cases n with
  | zero => exact (weilFamily_eq_zero_of_dim_zero _).trans (weilFamily_eq_zero_of_dim_zero _).symm
  | succ m =>
    have hEq := currentBDivisorOn_eq_of_iEquivalent (ModelSystem.blowup (m + 1) X)
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent S)) hclass
      ((currentIOrderAny_iff_existing T S).mp hTS) ((currentIOrderAny_iff_existing S T).mp hST)
    have he := (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) T).trans
      (hEq.trans (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) S).symm)
    apply Subtype.ext
    funext π
    exact congrArg (fun D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m) => D.onModel π) he

omit [ConnectedSpace X] in
/-- Original injectivity in all dimensions, on the WHOLE nondivisorial current carrier. -/
theorem currentIEquivalent_of_currentBDivisorAnyOn_eq
    {T S : ClosedPositive (n := n) (X := X)}
    (hT : T = regularCurrentAny T) (hS : S = regularCurrentAny S)
    (hclass : currentClassAny T = currentClassAny S)
    (heq : currentBDivisorAnyOn (ModelSystem.blowup n X) T =
      currentBDivisorAnyOn (ModelSystem.blowup n X) S) :
    currentIOrderAny T S ∧ currentIOrderAny S T := by
  cases n with
  | zero =>
    have h : T = S := (closedPositive_eq_zeroDim T).trans (closedPositive_eq_zeroDim S).symm
    subst S
    exact ⟨currentIOrderAny_refl T, currentIOrderAny_refl T⟩
  | succ m =>
    have he : currentBDivisor (toBookCurrent T) = currentBDivisor (toBookCurrent S) :=
      (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) T).symm.trans
        ((congrArg (toExisting (ModelSystem.blowup (m + 1) X) (Nat.succ_pos m)) heq).trans
          (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) S))
    have hI := SGPT.Hodge.Exceptional.currentBDivisor_injective
      (nonDivisorial_toBookCurrent T hT) (nonDivisorial_toBookCurrent S hS) hclass he
    exact ⟨(currentIOrderAny_iff_existing T S).mpr hI.1,
      (currentIOrderAny_iff_existing S T).mpr hI.2⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- The literal natural source map, with target positivity/nefness/root properties produced. -/
def gCurrentToBigNefRoot (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : GCurrent α) : BigNefRoot α :=
  ⟨currentBDivisorAnyOn (ModelSystem.blowup n X) T.val,
    (currentIVolumeAny_eq_bdivisorVolume ω T.val) ▸ T.property.2.2,
    DTUniformDraft.currentBDivisorAnyOn_isNef ω T.val,
    (currentBDivisorAnyOn_root_of_regular T.val T.property.2.1).trans T.property.1⟩

/-- The actual map descends to the literal current I-equivalence quotient. -/
def quotientToBigNefRoot (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Quotient (gCurrentISetoid ω α) → BigNefRoot α :=
  Quotient.lift (gCurrentToBigNefRoot ω α) (by
    intro T S h
    apply Subtype.ext
    exact currentBDivisorAnyOn_eq_of_currentIEquivalent
      (T.property.1.trans S.property.1.symm) h.1 h.2)

/-- Exact forward readback is D(T), on the original whole compatible family. -/
theorem quotientToBigNefRoot_mk (ω : KahlerBackground n X) (α : RealBottChern n X)
    (T : GCurrent α) :
    (quotientToBigNefRoot ω α (Quotient.mk _ T)).val =
      currentBDivisorAnyOn (ModelSystem.blowup n X) T.val := rfl

/-- No restricted class or selected presentation enters quotient injectivity. -/
theorem quotientToBigNefRoot_injective (ω : KahlerBackground n X) (α : RealBottChern n X) :
    Function.Injective (quotientToBigNefRoot ω α) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro T S h
  apply Quotient.sound
  exact currentIEquivalent_of_currentBDivisorAnyOn_eq T.property.2.1 S.property.2.1
    (T.property.1.trans S.property.1.symm) (congrArg Subtype.val h)

end SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
