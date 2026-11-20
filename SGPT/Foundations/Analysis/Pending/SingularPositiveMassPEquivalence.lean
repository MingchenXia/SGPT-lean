import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope
import SGPT.Foundations.Analysis.FirstPass.POrder

set_option autoImplicit false

/-! # Actual fixed-background P-equivalence and positive diagonal mass -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPositiveMassPEquivalence

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine regularity and actual envelope mass preservation internally transport fixed-background envelope equality to equality of the actual diagonal masses, without a positive-mass premise. -/
theorem diagonalPotentialMass_eq_of_pEquivalentWith (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (huv : PEquivalentWith θ u v) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ v hv := by
  have hlocal := hu.1.hasSmoothLocalPotentials
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hlocal u hu
  have hQ := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hlocal v hv
  calc
    diagonalPotentialMass θ u hu =
        diagonalPotentialMass θ (singularityEnvelope θ.val u) hP :=
      (singularityEnvelopeMassPreserving omega θ u hu hP).symm
    _ = diagonalPotentialMass θ (singularityEnvelope θ.val v) hQ :=
      diagonalPotentialMass_congr (pEquivalentWith_iff_envelope_eq.1 huv) hP hQ
    _ = diagonalPotentialMass θ v hv := singularityEnvelopeMassPreserving omega θ v hv hQ

/-- Actual equal-mass comparison applied directly to the genuine input and the second actual envelope produces the positive-mass fixed-background P-equivalence criterion, with no idempotence assumption. -/
theorem pEquivalentWith_iff_diagonalPotentialMass_eq_of_pOrderWith
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hpos : HasPositivePotentialMass θ u hu)
    (huv : POrderWith θ u v) :
    PEquivalentWith θ u v ↔ diagonalPotentialMass θ u hu = diagonalPotentialMass θ v hv := by
  constructor
  · exact diagonalPotentialMass_eq_of_pEquivalentWith omega θ hu hv
  · intro hmass
    have hQ := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
      θ.property.2 hu.1.hasSmoothLocalPotentials v hv
    have hQmass := singularityEnvelopeMassPreserving omega θ v hv hQ
    have hmore : MoreSingularOn u (singularityEnvelope θ.val v) univ :=
      (moreSingularOn_singularityEnvelope hu).trans (MoreSingularOn.of_le fun x _ => huv x)
    exact ⟨huv, equalMassLeSingularityEnvelope omega θ u _ hu hQ hpos
      (singularityEnvelope_le_zero θ.val v) hmore (hmass.trans hQmass.symm)⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPositiveMassPEquivalence
