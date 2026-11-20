import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility

set_option autoImplicit false

/-!
# Xia's Lemma 2.4.4 in the equal-mass case of Corollary 2.4.3

`Pending.ConvexCombEnvelopeMass` proves Xia's (2.30) and (2.31) for every
*admissible* weight `a` (its interval (2.28)): the Perron envelope
`P_θ(a φ + (1 - a) ψ)` is a genuine `θ`-PSH potential and satisfies (2.29).
This file records the specialisation Corollary 2.4.3 uses, where `φ` and `ψ`
have the **same** mass and the admissible interval is therefore all of
`(1, ∞)` — `ConvexCombEnvelopeMass.isAdmissibleWeight_of_eq`.

## History, because it explains the shape of the file

Two statements in this workspace once encoded the same source lemma:
`RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier` (Corollary
2.4.3, `xia-sgpt:page-0087`) and the envelope form recorded here and in
`Pending.DominationPrincipleMiddleStage`.  Both were interfaces, so the source
was counted twice, and this file removed the duplication by deriving the
envelope form *from* the `ε`-barrier.

Run 0050 closed the loop from the other side: the `ε`-barrier is now **proved**
from `ConvexCombEnvelopeMass`, which rests on Step 1 of Lemma 2.4.4
(`xia-sgpt:page-0084`--`xia-sgpt:page-0086`).  Deriving the envelope form from
the `ε`-barrier would therefore be a round trip through a corollary of itself:
correct, and acyclic in Lean, but it would hide where the cone actually bottoms
out.  So the derivation below now goes to `ConvexCombEnvelopeMass` directly.
The statement is unchanged, and the `ε`-barrier keeps its own consumers
(`Pending.DominationPrincipleContactChain`, `Pending.RelativeFullMass`).

The single named form of this source material is
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`.

The `ERealAlgebra` section below is the home of the whole pointwise family for
`convexComb a A B = a A + (1 - a) B` with `a > 1`: besides the two lemmas this
file itself uses, it carries the reverse rearrangement and the cancellation
that `Pending.DominationPrincipleContactChain` needs to identify Xia's contact
set `D_a`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
open SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra

noncomputable section

-- The pointwise algebra of Xia's affine obstacle now lives in
-- `Pending.ConvexCombObstacleAlgebra`, so that the envelope construction of
-- `Pending.ConvexCombEnvelopeMass` can use it without importing this module.
-- The four names below, and their statements, are unchanged.
export ConvexCombObstacleAlgebra (convexCombValue_le_left convexCombValue_le_iff
  le_convexCombValue_of_convexCombValue_le eq_of_convexCombValue_eq)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia, SGPT, Lemma 2.4.4 in the explicit envelope form of Corollary 2.4.3.**
For `phi ≤ psi` of the same positive non-pluripolar mass and any `a > 1`, the
Perron envelope `P_theta (a phi + (1 - a) psi)` is a genuine `theta`-PSH
potential and satisfies (2.29).

Equal masses make every `a > 1` admissible in Xia's sense (his interval (2.28)
is then all of `(1, ∞)`, the fraction being read as `∞`), so this is the
equal-mass instance of
`ConvexCombEnvelopeMass.isThetaPshPotential_rooftopEnvelope_convexComb` and
nothing more.  The only source input is Step 1 of Lemma 2.4.4,
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`. -/
theorem isThetaPshPotential_rooftopEnvelope_convexComb
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hmass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta psi hpsi)
    {a : ℝ} (ha : 1 < a) :
    IsThetaPshPotential theta.val
        (rooftopEnvelope theta.val (convexComb a phi psi)) ∧
      convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi ≤ phi := by
  refine ConvexCombEnvelopeMass.isThetaPshPotential_rooftopEnvelope_convexComb
    omega theta hphi hpsi hle hpos ?_
  rw [← hmass]
  exact ConvexCombEnvelopeMass.isAdmissibleWeight_of_eq hpos ha

end

end SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier
