import SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema

set_option autoImplicit false

/-! # Actual global and fixed P-orders for a positive right reference -/

open Set

namespace SGPT.Foundations.Analysis.Pending.PositiveReferenceGlobalPOrder

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularGlobalPOrder SingularGlobalPEnvelopeBridge PositiveGlobalPEnvelopeSuprema

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Control of every actual normalized additive-singularity competitor,
using only positive original mass of the right reference. -/
theorem pOrderWith_of_sourcePOrder_of_positive_right_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (hvpos : HasPositivePotentialMass θ v hv)
    (huv : SourcePOrder (n := n) u v) : POrderWith θ u v := by
  apply (singularityEnvelope_le_iff
    (upperSemicontinuous_singularityEnvelope θ.val v)).mpr
  intro w hw hw0 hwu
  have hwuP := sourcePOrder_of_moreSingularOn omega θ θ hw hu hwu
  exact le_singularityEnvelope_of_sourcePOrder_of_nonpositive
    omega θ hv hvpos hw hw0 (hwuP.trans omega huv)

/-- The actual source and fixed-background orders agree when the right
reference has positive original mass.  The left mass may vanish. -/
theorem sourcePOrder_iff_pOrderWith_of_positive_right_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (hvpos : HasPositivePotentialMass θ v hv) :
    SourcePOrder (n := n) u v ↔ POrderWith θ u v := by
  exact ⟨pOrderWith_of_sourcePOrder_of_positive_right_mass omega θ hu hv hvpos,
    sourcePOrder_of_pOrderWith omega θ hu hv⟩

end

end SGPT.Foundations.Analysis.Pending.PositiveReferenceGlobalPOrder
