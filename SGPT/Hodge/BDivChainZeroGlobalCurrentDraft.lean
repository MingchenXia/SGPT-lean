import SGPT.Hodge.BDivChainZeroNativeDraft
import SGPT.PSH.BookCurrentSpace
import SGPT.Foundations.Analysis.Pending.CurrentPairing

/-!
# Actual degree-two distribution chart families in all dimensions

The chart entries are actual distribution-valued
alternating 2-forms.  In positive dimension, compatibility is exactly the
existing global current's overlap equation after the existing complementary
pairing.  In dimension zero, all chart entries vanish by alternation, so no
nonzero transition data are omitted. This file alone does not prove a current
b-divisor theorem; the later modules construct and compare that family.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual distribution-valued alternating 2-form coefficients on every
complex chart, including when the dimension is zero. -/
abbrev ChartDistributionTwo :=
  (e : ComplexChart n X) → DistributionForm (chartTarget e) 2

/-- Positive-dimensional overlap is the pre-existing genuine complementary-test
overlap relation. At dimension zero all the chart coefficients are zero. -/
def ChartDistributionTwoCompatible (A : ChartDistributionTwo (n := n) (X := X)) : Prop :=
  ∀ hn : 0 < n, CurrentFamilyCompatible (fun e =>
    toLocalCurrent (canonicalBasis n) (degreeTwo hn) (A e))

/-- Degree-two global distributional currents, carried by actual chart
coefficients and their genuine overlap condition. -/
def GlobalDistributionTwo :=
  {A : ChartDistributionTwo (n := n) (X := X) // ChartDistributionTwoCompatible A}

namespace GlobalDistributionTwo

/-- In positive dimension the existing chartwise pairing produces the original
native global current. -/
def toGlobal (hn : 0 < n) (A : GlobalDistributionTwo (n := n) (X := X)) :
    GlobalCurrent n X (degreeTwo hn) :=
  ⟨fun e => toLocalCurrent (canonicalBasis n) (degreeTwo hn) (A.val e), A.property hn⟩

/-- Extract the original current's actual distribution coefficients. -/
def ofGlobal (hn : 0 < n) (T : GlobalCurrent n X (degreeTwo hn)) :
    GlobalDistributionTwo (n := n) (X := X) := by
  refine ⟨fun e => fromLocalCurrent (canonicalBasis n) (degreeTwo hn) (T.inChart e), ?_⟩
  intro hn'
  have hT : CurrentFamilyCompatible (fun e => T.inChart e) := by
    change CurrentFamilyCompatible T.val
    exact T.property
  simpa only [CurrentPairing.toLocalCurrent_fromLocalCurrent] using hT

/-- The inverse identities are the existing local pairing inverse theorems,
combined with the literal existing overlap equation. -/
def equivGlobal (hn : 0 < n) :
    GlobalDistributionTwo (n := n) (X := X) ≃ GlobalCurrent n X (degreeTwo hn) where
  toFun := toGlobal hn
  invFun := ofGlobal hn
  left_inv A := by
    apply Subtype.ext
    funext e
    exact CurrentPairing.fromLocalCurrent_toLocalCurrent (canonicalBasis n) (degreeTwo hn)
      (A.val e)
  right_inv T := by
    apply GlobalCurrent.ext
    intro e η
    change toLocalCurrent (canonicalBasis n) (degreeTwo hn)
      (fromLocalCurrent (canonicalBasis n) (degreeTwo hn) (T.inChart e)) η = T.inChart e η
    rw [CurrentPairing.toLocalCurrent_fromLocalCurrent]

/-- Closedness and type (1,1) use the actual coefficient predicates in every
chart, exactly as the existing positive-dimensional global current does. -/
def IsClosed (A : GlobalDistributionTwo (n := n) (X := X)) : Prop :=
  ∀ e, LocalCurrents.IsClosed (A.val e)

def IsTypeOneOne (A : GlobalDistributionTwo (n := n) (X := X)) : Prop :=
  ∀ e, LocalCurrents.IsOneOne (A.val e)

/-- Source weak positivity. The first disjunct is the book's `1 > n` clause;
the second uses the actual complementary-test positivity in positive dimension.
This does not identify square positivity with the full source condition. -/
def IsPositive (A : GlobalDistributionTwo (n := n) (X := X)) : Prop :=
  n < 1 ∨ ∀ hn : 0 < n,
    SGPT.PSH.BookCurrent.IsPositiveCurrent 1 rfl (A.toGlobal hn)

/-- Closedness agrees with the original global-current definition in every
positive dimension. The only non-definitional step is the actual local pairing
inverse; no compatibility certificate is assumed. -/
theorem isClosed_iff_toGlobal (hn : 0 < n)
    (A : GlobalDistributionTwo (n := n) (X := X)) :
    A.IsClosed ↔ (A.toGlobal hn).IsClosed (canonicalBasis n) := by
  unfold IsClosed GlobalCurrent.IsClosed
  apply forall_congr'
  intro e
  change LocalCurrents.IsClosed (A.val e) ↔
    LocalCurrents.IsClosed (fromLocalCurrent (canonicalBasis n) (degreeTwo hn)
      (toLocalCurrent (canonicalBasis n) (degreeTwo hn) (A.val e)))
  rw [CurrentPairing.fromLocalCurrent_toLocalCurrent]

/-- The same coefficient comparison identifies the actual `(1,1)` predicate. -/
theorem isTypeOneOne_iff_toGlobal (hn : 0 < n)
    (A : GlobalDistributionTwo (n := n) (X := X)) :
    A.IsTypeOneOne ↔ (A.toGlobal hn).IsTypeOneOne (canonicalBasis n) hn := by
  unfold IsTypeOneOne GlobalCurrent.IsTypeOneOne
  apply forall_congr'
  intro e
  change LocalCurrents.IsOneOne (A.val e) ↔
    LocalCurrents.IsOneOne (fromLocalCurrent (canonicalBasis n) (degreeTwo hn)
      (toLocalCurrent (canonicalBasis n) (degreeTwo hn) (A.val e)))
  rw [CurrentPairing.fromLocalCurrent_toLocalCurrent]

/-- Source weak positivity agrees with the book's existing test-form cone in
positive dimension. -/
theorem isPositive_iff_toGlobal (hn : 0 < n)
    (A : GlobalDistributionTwo (n := n) (X := X)) :
    A.IsPositive ↔ SGPT.PSH.BookCurrent.IsPositiveCurrent 1 rfl (A.toGlobal hn) := by
  constructor
  · intro h
    rcases h with hdim | hpos
    · omega
    · exact hpos hn
  · intro h
    right
    intro hn'
    simpa using h

/-- Closed positive `(1,1)` currents retain the actual distribution-valued
chart family as their underlying object. -/
def ClosedPositive := {A : GlobalDistributionTwo (n := n) (X := X) //
  A.IsClosed ∧ A.IsTypeOneOne ∧ A.IsPositive}

end GlobalDistributionTwo

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X]

omit [IsComplexManifold 0 X] in
/-- The zero-dimensional charts contain actual zero distributional 2-forms. -/
theorem chart_eq_zero (A : GlobalDistributionTwo (n := 0) (X := X))
    (e : ComplexChart 0 X) : A.val e = 0 :=
  localDistributionTwo_eq_zero (chartTarget e) (A.val e)

omit [IsComplexManifold 0 X] in
/-- Any two dimension-zero objects have identical actual coefficients. -/
theorem eq_of_dim_zero (A B : GlobalDistributionTwo (n := 0) (X := X)) : A = B := by
  apply Subtype.ext
  funext e
  rw [chart_eq_zero A e, chart_eq_zero B e]

/-- The genuine zero chart family exists without a proxy carrier. -/
def zeroDim : GlobalDistributionTwo (n := 0) (X := X) := by
  refine ⟨fun _ => 0, ?_⟩
  intro hn
  omega

omit [IsComplexManifold 0 X] in
/-- All actual degree-two chart families are the genuine zero current. -/
theorem eq_zeroDim (A : GlobalDistributionTwo (n := 0) (X := X)) : A = zeroDim :=
  eq_of_dim_zero A zeroDim

omit [IsComplexManifold 0 X] in
/-- Zero is closed as a distributional form, including in degree three. -/
theorem isClosed_zeroDim : (zeroDim (X := X)).IsClosed := by
  intro e
  unfold LocalCurrents.IsClosed
  change exteriorDerivative (0 : DistributionForm (chartTarget e) 2) = 0
  ext v φ
  simp [exteriorDerivative_apply]

omit [IsComplexManifold 0 X] in
/-- Zero satisfies the actual complex type condition. -/
theorem isTypeOneOne_zeroDim : (zeroDim (X := X)).IsTypeOneOne := by
  intro e v w
  rfl

/-- The source's `1 > 0` clause supplies weak positivity in dimension zero. -/
theorem isPositive_of_dim_zero (A : GlobalDistributionTwo (n := 0) (X := X)) :
    A.IsPositive := Or.inl (by decide)

/-- The actual source closed positive zero current on a zero-dimensional
manifold. -/
def closedPositiveZeroDim : ClosedPositive (n := 0) (X := X) :=
  ⟨zeroDim, isClosed_zeroDim, isTypeOneOne_zeroDim, isPositive_of_dim_zero zeroDim⟩

end SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

namespace SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- In positive dimension the new source closed-positive object maps to the
existing literal book current with the same underlying global current. -/
def toBookCurrent (T : ClosedPositive (n := m + 1) (X := X)) :
    SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X :=
  ⟨⟨T.val.toGlobal (Nat.succ_pos m),
      (isClosed_iff_toGlobal (Nat.succ_pos m) T.val).mp T.property.1,
      (isTypeOneOne_iff_toGlobal (Nat.succ_pos m) T.val).mp T.property.2.1⟩,
    (isPositive_iff_toGlobal (Nat.succ_pos m) T.val).mp T.property.2.2⟩

/-- In positive dimension extract the original book current's actual chart
coefficients and all three original properties. -/
def ofBookCurrent (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    ClosedPositive (n := m + 1) (X := X) := by
  let A := ofGlobal (Nat.succ_pos m) T.current
  have hA : A.toGlobal (Nat.succ_pos m) = T.current :=
    (equivGlobal (Nat.succ_pos m)).right_inv T.current
  refine ⟨A, ?_, ?_, ?_⟩
  · apply (isClosed_iff_toGlobal (Nat.succ_pos m) A).mpr
    rw [hA]
    exact T.isClosed
  · apply (isTypeOneOne_iff_toGlobal (Nat.succ_pos m) A).mpr
    rw [hA]
    exact T.isTypeOneOne
  · apply (isPositive_iff_toGlobal (Nat.succ_pos m) A).mpr
    rw [hA]
    exact T.isPositive

/-- The constructions really recover the original positive current. -/
theorem toBookCurrent_ofBookCurrent (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) :
    toBookCurrent (ofBookCurrent T) = T := by
  apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
  exact (equivGlobal (Nat.succ_pos m)).right_inv T.current

/-- Conversely they recover every original actual chart coefficient. -/
theorem ofBookCurrent_toBookCurrent (T : ClosedPositive (n := m + 1) (X := X)) :
    ofBookCurrent (toBookCurrent T) = T := by
  apply Subtype.ext
  exact (equivGlobal (Nat.succ_pos m)).left_inv T.val

end SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
