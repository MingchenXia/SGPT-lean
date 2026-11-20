import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.DiagonalMass

set_option autoImplicit false

/-!
# I-good potentials and their actual I-volume: definitions

This file encodes Xia, Definition 7.1.1 (`xia-sgpt:page-0252`) using the
project's genuine locally nondegenerate theta-PSH potentials, concrete
ordinary and multiplier-ideal envelopes, and actual diagonal global
non-pluripolar mass.

The mass/volume characterization of Theorem 7.1.1 (`xia-sgpt:page-0250` and
`xia-sgpt:page-0251`) is in `Pending.IGood`, which imports its proof.

The dS characterization and independence of the background in Definition
7.1.1 are deliberately not asserted in this module.
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

/-- The actual I-volume of a genuine theta-PSH potential: the actual diagonal
non-pluripolar mass of its multiplier-ideal envelope.  Closedness and type
`(1,1)` are carried by `theta`; the smooth-local-potential witness is explicit
because the proof of I-envelope regularity uses it. -/
def iVolume (theta : ClosedRealOneOneForm n M)
    (hlocal : HasSmoothLocalPotentials theta.val) (phi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi) : ENNReal :=
  diagonalPotentialMass theta (iSingularityEnvelope theta.val phi)
    (iSingularityEnvelope_isThetaPshPotential theta.val
      theta.property.1 theta.property.2 hlocal phi hphi)

omit [BorelSpace M] in
/-- Actual I-volume is independent of the proof witnesses for local potentials
and theta-plurisubharmonicity. -/
theorem iVolume_proof_independent (theta : ClosedRealOneOneForm n M)
    (hlocal hlocal' : HasSmoothLocalPotentials theta.val) (phi : M → EReal)
    (hphi hphi' : IsThetaPshPotential theta.val phi) :
    iVolume theta hlocal phi hphi = iVolume theta hlocal' phi hphi' := by
  unfold iVolume
  exact diagonalPotentialMass_proof_independent
    (iSingularityEnvelope_isThetaPshPotential theta.val
      theta.property.1 theta.property.2 hlocal phi hphi)
    (iSingularityEnvelope_isThetaPshPotential theta.val
      theta.property.1 theta.property.2 hlocal' phi hphi')

/-- I-goodness relative to one actual background: positive actual mass and
equality of the ordinary P-envelope with the multiplier-ideal envelope. -/
def IGoodWith (theta : ClosedRealOneOneForm n M) (phi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi) : Prop :=
  HasPositivePotentialMass theta phi hphi ∧
    singularityEnvelope theta.val phi = iSingularityEnvelope theta.val phi

omit [BorelSpace M] [Nonempty M] in
/-- Relative I-goodness is independent of the chosen proof of the genuine
theta-PSH condition. -/
theorem iGoodWith_proof_independent (theta : ClosedRealOneOneForm n M)
    (phi : M → EReal) (hphi hphi' : IsThetaPshPotential theta.val phi) :
    IGoodWith theta phi hphi ↔ IGoodWith theta phi hphi' := by
  unfold IGoodWith
  exact and_congr
    (hasPositivePotentialMass_proof_independent hphi hphi') Iff.rfl

omit [BorelSpace M] [Nonempty M] in
theorem IGoodWith.positiveMass {theta : ClosedRealOneOneForm n M}
    {phi : M → EReal} {hphi : IsThetaPshPotential theta.val phi}
    (h : IGoodWith theta phi hphi) :
    HasPositivePotentialMass theta phi hphi :=
  h.1

omit [BorelSpace M] [Nonempty M] in
theorem IGoodWith.envelope_eq {theta : ClosedRealOneOneForm n M}
    {phi : M → EReal} {hphi : IsThetaPshPotential theta.val phi}
    (h : IGoodWith theta phi hphi) :
    singularityEnvelope theta.val phi = iSingularityEnvelope theta.val phi :=
  h.2

/-- Background-existential I-goodness, faithfully following Definition 7.1.1:
there is a smooth closed real `(1,1)` background in which `phi` is a genuine
positive-mass theta-PSH potential and its P- and I-envelopes agree. -/
def IGood (phi : M → EReal) : Prop :=
  ∃ (theta : ClosedRealOneOneForm n M)
    (hphi : IsThetaPshPotential theta.val phi), IGoodWith theta phi hphi

omit [BorelSpace M] [Nonempty M] in
theorem IGoodWith.iGood {theta : ClosedRealOneOneForm n M}
    {phi : M → EReal} {hphi : IsThetaPshPotential theta.val phi}
    (h : IGoodWith theta phi hphi) : IGood (n := n) phi :=
  ⟨theta, hphi, h⟩

omit [BorelSpace M] [Nonempty M] in
theorem IGood.exists_background {phi : M → EReal} (h : IGood (n := n) phi) :
    ∃ (theta : ClosedRealOneOneForm n M)
      (hphi : IsThetaPshPotential theta.val phi), IGoodWith theta phi hphi :=
  h

end

end SGPT.Foundations.Analysis.Pending
