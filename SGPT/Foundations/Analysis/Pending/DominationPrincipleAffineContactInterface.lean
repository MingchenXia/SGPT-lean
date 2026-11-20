import SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactProof

set_option autoImplicit false

/-!
# The affine-obstacle instance of Xia's envelope concentration theorem

This module states the instance of Xia's Theorem 2.4.4 (`xia-sgpt:page-0079`,
equation (2.23)) needed by the ordered case of Xia's domination principle: the
theorem applied to the affine obstacle `a φ + (1-a) ψ`. Its proof is on
`xia-sgpt:page-0080`--`page-0082`, using quasi-continuity, capacity estimates,
and the decreasing-reference-truncation passage.

It is no longer a named input of its own.  The affine obstacle need not be upper
semicontinuous (`1-a < 0`); its quasi-continuity is
`Pending.RooftopAffineObstacleQuasiContinuity` and the theorem is proved in
`Pending.DominationPrincipleAffineContactProof`
(`xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le`), to which the
declaration below reduces; that proof still rests, through classes that are not
big, on the named published input `UniformAmbientVolumeBigness` (Boucksom 4.8), so
`#print axioms` shows `sorryAx`.  It keeps its name and statement for its
consumers; the hypotheses `hpos` and `hmass` (those of Theorem 2.4.5) are not used.

The module imports only what its own statement needs.  In particular it does
*not* import `Pending.RooftopConvexCombBarrier`: that module sits above
`Pending.ConvexCombEnvelopeMass`, whose Step 1 is one of this interface's
consumers (through Xia's Step 1.3), so importing it here would make the
dependency graph circular.  Consumers that need both import both.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia, SGPT, Theorem 2.4.4** (`xia-sgpt:page-0079`, equation (2.23); proof
`xia-sgpt:page-0080`--`page-0082`), specialised to the affine obstacle in the
proof of Theorem 2.4.5; reduced to
`DominationPrincipleAffineContactProof.xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le`
(which rests only on Boucksom 4.8 for non-big classes). -/
theorem xiaTheorem244_affineObstacle_noncontact_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hmass : diagonalPotentialMass theta phi hphi =
      diagonalPotentialMass theta psi hpsi)
    {a : ℝ} (ha : 1 < a)
    (heta : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (convexComb a phi psi))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (convexComb a phi psi)) heta
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x <
        convexComb a phi psi x} = 0 := by
  -- Theorem 2.4.4 itself uses neither `hpos` nor `hmass` (hypotheses of Theorem 2.4.5).
  have _ := hpos; have _ := hmass
  exact DominationPrincipleAffineContactProof.xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le
    omega theta hphi hpsi hle ha heta

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain
