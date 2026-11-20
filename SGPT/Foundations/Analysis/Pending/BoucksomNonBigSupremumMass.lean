import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

set_option autoImplicit false

/-!
# Boucksom's non-big canonical mass (formerly a named input; PROVED from Boucksom 4.8)

This module isolates the one classical ingredient in the non-big branch of
Xia's Corollary 2.4.4.  Its consumer is
`Pending.NonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`;
that consumer only combines this input with a dimension/bigness trichotomy and
measure monotonicity.

The input packages two literature facts in the precise form needed here:

* Boucksom's Grauert--Riemenschneider criterion says that a pseudoeffective
  `(1,1)` class on a compact Kähler manifold is big exactly when its volume is
  positive (`bou02-volume:4.8`, Theorem 4.7; the definition of volume is
  `bou02-volume:1.3`);
* the non-pluripolar top mass of a theta-PSH potential is bounded by that
  volume (BEGZ, *Monge--Ampère equations in big cohomology classes*, discussion
  of the non-pluripolar product comparison).

Here `hV` supplies pseudoeffectivity of the representative class.  The explicit
Kähler background is essential: Boucksom's cited criterion is a compact Kähler
statement.  The positive-dimensional hypothesis is carried from the consuming
big-class branch; dimension zero is discharged constructively in
`Pending.NonBigSupremumMass`.

No source currently formalized in this workspace supplies either the volume
comparison or the volume criterion, so this is a deliberately narrow,
source-anchored classical interface rather than a restatement of the contact-set
consumer: its conclusion is about the total mass and mentions no sublevel set.

PROVED (TN-CLASSICAL run 0159, I-0902 item 1): Boucksom 4.8 is now proved in place
(`UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`, using Hironaka's
`RelativePrincipalization.exists_factorizationData` and Yau's theorem, both since proved in place), and a
potential of positive non-pluripolar mass makes its class big
(`BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos`, the Copy-4 `it:bigness` step); the
statement below is its contrapositive for the potential `thetaPshSupremum`.  The volume comparison
of BEGZ is not needed.  The statement is unchanged.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.BoucksomNonBigSupremumMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- **Boucksom's criterion, non-big branch** (formerly an external classical input; PROVED as
the contrapositive of Boucksom 4.8).  On a compact connected Kähler manifold and in positive
complex dimension, the canonical theta-PSH reference of a non-big class has
zero total non-pluripolar mass.  The source decomposition is documented in the
module header, with anchors `bou02-volume:1.3`, `bou02-volume:4.8`, and BEGZ's
non-pluripolar-product comparison. -/
theorem diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hnb : ¬ IsBigClass (RealBottChern.ofRepresentative theta)) :
    diagonalPotentialMass theta (thetaPshSupremum theta.val) hV = 0 := by
  exact BoucksomMassBigness.diagonalPotentialMass_eq_zero_of_not_isBigClass hn omega theta hV hnb

end

end SGPT.Foundations.Analysis.Pending.BoucksomNonBigSupremumMass
