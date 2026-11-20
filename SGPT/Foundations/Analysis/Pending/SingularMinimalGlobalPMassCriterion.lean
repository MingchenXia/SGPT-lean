import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassCriterion
import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay

set_option autoImplicit false

/-! # The literal minimal-reference source global P-mass criterion -/

namespace SGPT.Foundations.Analysis.Pending.SingularMinimalGlobalPMassCriterion

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  SingularMinimalCanonicalRay SingularGlobalPOrder SingularGlobalPMixedMassCriterion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual bigness internally produces the literal minimal reference and
its positive mass, so the complete source mixed-mass criterion applies to
all genuine input potentials, including zero original diagonal masses. -/
theorem sourcePEquivalent_iff_minimal_endpointMixedMass_eq
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (huv : SourcePOrder (n := n) u v) :
    SourcePEquivalent (n := n) u v ↔
      ∀ j : Fin (n + 1),
        endpointMixedMass θ (thetaPshSupremum θ.val) u
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hu j =
        endpointMixedMass θ (thetaPshSupremum θ.val) v
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic hv j := by
  exact sourcePEquivalent_iff_endpointMixedMass_eq_of_sourcePOrder omega hu hv
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
    (isModelPotential_thetaPshSupremum omega θ hbig).positive_mass huv

end

end SGPT.Foundations.Analysis.Pending.SingularMinimalGlobalPMassCriterion
