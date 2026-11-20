import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope

set_option autoImplicit false

namespace SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotence

open FirstPass FirstPass.PositiveClasses DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] [ConnectedSpace M]

/-- The positive-mass case of Xia's P-envelope idempotence, derived from the
already formalized mass-preservation and equal-mass comparison theorems. -/
theorem singularityEnvelope_idempotent_of_positive_mass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hpositive : HasPositivePotentialMass theta phi hphi) :
    singularityEnvelope theta.val (singularityEnvelope theta.val phi) =
      singularityEnvelope theta.val phi := by
  have hlocal := hphi.1.hasSmoothLocalPotentials
  have hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hlocal phi hphi
  have hPP : IsThetaPshPotential theta.val
      (singularityEnvelope theta.val (singularityEnvelope theta.val phi)) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hlocal (singularityEnvelope theta.val phi) hP
  have hP_le_PP : singularityEnvelope theta.val phi ≤
      singularityEnvelope theta.val (singularityEnvelope theta.val phi) :=
    self_le_singularityEnvelope hP (singularityEnvelope_le_zero theta.val phi)
  have hmore : MoreSingularOn phi
      (singularityEnvelope theta.val (singularityEnvelope theta.val phi)) Set.univ :=
    (moreSingularOn_singularityEnvelope hphi).trans
      (MoreSingularOn.of_le fun x _ => hP_le_PP x)
  have hmass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta
      (singularityEnvelope theta.val (singularityEnvelope theta.val phi)) hPP := by
    calc
      diagonalPotentialMass theta phi hphi =
          diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP :=
        (singularityEnvelopeMassPreserving omega theta phi hphi hP).symm
      _ = diagonalPotentialMass theta
          (singularityEnvelope theta.val (singularityEnvelope theta.val phi)) hPP :=
        (singularityEnvelopeMassPreserving omega theta
          (singularityEnvelope theta.val phi) hP hPP).symm
  apply le_antisymm
  · exact equalMassLeSingularityEnvelope omega theta phi _ hphi hPP hpositive
      (singularityEnvelope_le_zero theta.val _) hmore hmass
  · exact hP_le_PP

end

end SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotence
