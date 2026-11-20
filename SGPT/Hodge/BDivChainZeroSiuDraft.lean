import SGPT.Hodge.BDivChainZeroCurrentBDivDraft

/-!
# Dimension-uniform Siu decomposition: separate dimensional statements

Both summands are actual distribution-chart currents. The positive
branch is the existing book Siu decomposition; the zero-dimensional prime
index is actually empty and the actual current and both summands have zero
chart coefficients. A single all-dimensional topology/weak-sum statement and
source integration still require proof.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Actual Siu divisorial current: in dimension zero its actual prime index is
empty; in positive dimension it is the existing book divisorial part. -/
def divisorialCurrentAny (T : ClosedPositive (n := n) (X := X)) :
    ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact closedPositiveZeroDim
  | succ m => exact ofBookCurrent (SGPT.Siu.bookSiuDivisorialPart (toBookCurrent T))

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- The positive-dimensional part is the literal existing Siu decomposition
of the literal original book current. -/
theorem siu_decomposition_pos (T : ClosedPositive (n := m + 1) (X := X)) :
    (toBookCurrent T).current =
      (toBookCurrent (regularCurrentAny T)).current +
        (toBookCurrent (divisorialCurrentAny T)).current := by
  rw [regularCurrentAny_pos]
  change (toBookCurrent T).current =
    (SGPT.Siu.bookSiuRegularPart (toBookCurrent T)).current +
      (toBookCurrent (ofBookCurrent (SGPT.Siu.bookSiuDivisorialPart (toBookCurrent T)))).current
  rw [toBookCurrent_ofBookCurrent]
  exact (SGPT.Siu.book_siu_decomposition (toBookCurrent T)).1

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

/-- Zero-dimensional Siu equality in every actual distribution chart. The
index of actual prime divisors is empty, not an assumed empty proxy. -/
theorem siu_decomposition_zero_chart (T : ClosedPositive (n := 0) (X := X))
    (e : ComplexChart 0 X) :
    T.val.val e = (regularCurrentAny T).val.val e + (divisorialCurrentAny T).val.val e := by
  rw [chart_eq_zero T.val e, chart_eq_zero (regularCurrentAny T).val e,
    chart_eq_zero (divisorialCurrentAny T).val e]
  exact (zero_add (0 : _)).symm

end SGPT.Hodge.BDivChain.NativeDraft
