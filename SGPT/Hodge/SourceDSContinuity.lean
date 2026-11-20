import SGPT.Hodge.SourceDSCurrent
import SGPT.Hodge.BDivDTUniformDraft

set_option autoImplicit false
noncomputable section
universe u

open Filter Set
open scoped Topology

namespace SGPT.Hodge.BDivChain.SourceDSDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The actual source θ+ddᶜu as a distribution-chart current in every dimension. -/
def sourcePotentialCurrentAny (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (u : SourceThetaPotentialL1 θ) : ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact sourcePotentialCurrentZero θ u
  | succ m => exact ofBookCurrent (sourcePotentialCurrent θ u)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The same original θ and u genuinely present this internally constructed current. -/
theorem sourcePotentialCurrentAny_isPresentation
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : SourceThetaPotentialL1 θ) :
    IsPresentationAny (sourcePotentialCurrentAny θ u) (atlasClosedFormToNative θ) u.val := by
  cases n with
  | zero => exact sourcePotentialCurrentZero_isPresentation θ u
  | succ m =>
    apply (isPresentationAny_iff_book _ _ _).mpr
    change SGPT.PSH.BookCurrent.IsPresentation
      (toBookCurrent (ofBookCurrent (sourcePotentialCurrent θ u))) _ _
    rw [toBookCurrent_ofBookCurrent]
    exact SGPT.PSH.BookCurrent.isPresentation_thetaPositiveCurrent _ _ _

/-- In positive dimension the whole family is exactly the original production construction. -/
theorem sourcePotentialCurrentAny_bdivisor_pos {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y)) (u : SourceThetaPotentialL1 θ) :
    toExisting (ModelSystem.blowup (m + 1) Y) (Nat.succ_pos m)
        (currentBDivisorAnyOn (ModelSystem.blowup (m + 1) Y) (sourcePotentialCurrentAny θ u)) =
      currentBDivisor (sourcePotentialCurrent θ u) := by
  simpa only [sourcePotentialCurrentAny, toBookCurrent_ofBookCurrent, currentBDivisor] using
    (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) Y)
      (sourcePotentialCurrentAny θ u))

/-- WHOLE original prop:dscontbdiv on arbitrary original θ and arbitrary filters,
with unindexed convergence in any genuine big reference and all original model traces.
No original-θ bigness, original positive mass or desired convergence certificate is added. -/
theorem source_dscontbdiv (ω : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : unindexedDSTendsto ω θ F w v) :
    ConvergesAny F
      (fun i => currentBDivisorAnyOn (ModelSystem.blowup n X) (sourcePotentialCurrentAny θ (w i)))
      (currentBDivisorAnyOn (ModelSystem.blowup n X) (sourcePotentialCurrentAny θ v)) := by
  cases n with
  | zero => exact currentBDivisorAnyOn_converges_zero _ F _ _
  | succ m =>
    have hconv := currentBDivisor_converges_of_unindexedDS ω θ F w v hlim
    intro π
    have he (a : SourceThetaPotentialL1 θ) :
        (currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X)
            (sourcePotentialCurrentAny θ a)).val π =
          (currentBDivisor (sourcePotentialCurrent θ a)).onModel π := by
      exact congrArg (fun D : BlowupWeilBDivisor (m + 1) X (Nat.succ_pos m) => D.onModel π)
        (sourcePotentialCurrentAny_bdivisor_pos θ a)
    simpa only [he] using hconv π

end SGPT.Hodge.BDivChain.SourceDSDraft
