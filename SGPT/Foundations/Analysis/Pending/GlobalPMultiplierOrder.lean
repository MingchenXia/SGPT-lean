import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
import SGPT.Foundations.Analysis.Pending.TraceFoundationsEnvelopes

set_option autoImplicit false

/-! # Actual global source P-witnesses imply actual multiplier order -/

namespace SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

open FirstPass FirstPass.IEnvelope SingularGlobalPOrder TraceFoundationsEnvelopes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- A true existential source P-witness internally supplies the fixed
background for every actual positive-level multiplier inclusion. -/
theorem iOrderOnManifold_of_sourcePOrder {u v : M → EReal}
    (huv : SourcePOrder (n := n) u v) : IOrderOnManifold (n := n) u v := by
  obtain ⟨θ, hu, hv, _, _, hfixed⟩ := huv
  exact iOrderOnManifold_of_pOrderWith θ hu hv hfixed

/-- Opposite actual global source comparisons give equality of all
actual local holomorphic-germ multiplier ideals. -/
theorem iEquivalentOnManifold_of_sourcePEquivalent {u v : M → EReal}
    (huv : SourcePEquivalent (n := n) u v) : IEquivalentOnManifold (n := n) u v :=
  ⟨iOrderOnManifold_of_sourcePOrder huv.1, iOrderOnManifold_of_sourcePOrder huv.2⟩

end

end SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
