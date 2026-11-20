import SGPT.Foundations.Analysis.Pending.IGoodBasic
import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope

set_option autoImplicit false

/-!
# I-goodness and the I-volume

Xia, Theorem 7.1.1, `(2) ⇔ (3)` (`xia-sgpt:page-0250` and `xia-sgpt:page-0251`),
for the definitions of `Pending.IGoodBasic`.  The signature retains a supplied
Kahler background, the project's actual potential-based bigness predicate, positive
actual mass, compactness, nonemptiness, connectedness and smooth local potentials.
Equivalence between `BigWithRespectToViaPotentials` and the source's full
cohomological big-class condition remains a separate bridge.

The proof is `iGoodWith_iff_mass_eq_iVolume_of_envelopeMass` with strong openness
(proved, `Pending.StrongOpennessRegularRoute`), Proposition 3.1.3
(`Pending.SingularityEnvelopeMassProof`) and Theorem 3.1.2
(`Pending.EqualMassEnvelope`).  Its remaining analytic inputs are the named
interfaces of `Pending.IncreasingTruncationLimit` and `Pending.DominationPrinciple`.
-/

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass
open FirstPass.IEnvelope
open FirstPass.PositiveClasses
open DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- **Xia, Theorem 7.1.1, `(2) ⇔ (3)`.** Under an actual
potential-based big background and positive actual mass, equality of the
ordinary mass with the actual I-volume is equivalent to I-goodness in that
background.  The separate cohomological-big bridge is not assumed here.
Connectedness is the source's standing assumption and is needed: on a
disconnected manifold, positive total mass allows a zero-mass component on
which the two conditions differ. -/
theorem iGoodWith_iff_mass_eq_iVolume [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (hlocal : HasSmoothLocalPotentials theta.val) (phi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpositive : HasPositivePotentialMass theta phi hphi) :
    IGoodWith theta phi hphi ↔
      diagonalPotentialMass theta phi hphi = iVolume theta hlocal phi hphi :=
  iGoodWith_iff_mass_eq_iVolume_of_envelopeMass (increasingStrongOpenness_ofRegularRoute n)
    omega theta hbig (singularityEnvelopeMassPreserving omega theta)
    (equalMassLeSingularityEnvelope omega theta) hlocal phi hphi hpositive

end

end SGPT.Foundations.Analysis.Pending
