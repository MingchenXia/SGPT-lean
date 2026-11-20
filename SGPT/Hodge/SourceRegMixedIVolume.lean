import SGPT.Hodge.SourceRegPositiveCone

/-! Actual original mixed I-volume is invariant under simultaneous Siu Reg,
including the genuine empty tuple in dimension zero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceReg
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.BDivisor SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceIntersection

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- WHOLE original Reg clause: every actual original positive-current tuple.
Finite domination and all diagonal/divisorial cancellation are proved internally. -/
theorem currentMixedIVolumeAny_regular_eq (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) :
    currentMixedIVolumeAny ω (fun i => regularCurrentAny (T i)) =
      currentMixedIVolumeAny ω T := by
  cases n with
  | zero => rfl
  | succ m =>
    simpa only [SourceRegCone.mixed,SourceRegCone.regular,
      ofBookCurrent_toBookCurrent,regularCurrentAny] using
      SourceRegCone.mixed_regular ω (fun i => toBookCurrent (T i))

end SGPT.Hodge.BDivChain.SourceReg
