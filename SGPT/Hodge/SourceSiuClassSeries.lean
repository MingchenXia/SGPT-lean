import SGPT.Hodge.SourceDivisorCurrentSeries
import SGPT.Hodge.SourceWeakClassNets

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
open SGPT.BDivisor
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
  [CompactSpace M] [ConnectedSpace M]
local notation "Cur" => GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))

/-- The ORIGINAL Siu coefficient family has an actual cohomology-class HasSum
on the whole original prime index, produced from its actual full-test weak sum. -/
theorem hasDivisorClassSum_siuDivisorialPart (ω : KahlerBackground (m+1) M)
    {T : Cur} (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    HasDivisorClassSum (fun D => (SGPT.Siu.currentGenericLelong T hT D).toReal)
      (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
        ⟨SGPT.Siu.siuDivisorialPart T hT,
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT).1,
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT).2.1⟩) := by
  let c := fun D => (SGPT.Siu.currentGenericLelong T hT D).toReal
  let S := SGPT.Siu.siuDivisorialPart T hT
  have hS := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT
  have hweak : ∀ e η, Tendsto (fun F => (divisorPartial c F).inChart e η) atTop
      (𝓝 (S.inChart e η)) := (SGPT.Siu.siuDivisorialPart_spec hT).2.2.2
  have hc := class_tendsto_of_weak_net ω (divisorPartialClosed c (fun _ => ENNReal.toReal_nonneg))
    ⟨S,hS.1,hS.2.1⟩ (fun F => (divisorPartial_positive c (fun _ => ENNReal.toReal_nonneg) F).2.2)
    hweak
  simp_rw [divisorPartial_class] at hc
  exact hc

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
