import SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier
import SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain

set_option autoImplicit false

/-!
# The analytic middle stage of Xia's domination principle

The two ends of Xia's Theorem 2.4.5 are proved in
`Pending.DominationPrincipleReduction`, and two of the four properties of the
Perron barrier family `eta a = P_theta (a phi + (1 - a) psi)` are proved in
`Pending.DominationPrincipleBarrier`.  What is left is the analytic middle,
which this file records as two named source theorems.

1. `isThetaPshPotential_rooftopEnvelope_convexComb` is **Xia's Lemma 2.4.4**
   (`xia-sgpt:page-0083`, inequality (2.29)) read through the explicit envelope
   of **Corollary 2.4.3** (`xia-sgpt:page-0087`, "in fact, we can take
   `eta = P_theta(eps⁻¹ phi + (1 - eps⁻¹) psi)`").  With equal masses the
   admissible range (2.28) of `a` is all of `(1, ∞)`, because the fraction
   there is then read as `∞`.  It is **no longer an interface**: it is derived
   in `Pending.RooftopConvexCombBarrier` from the `ε`-barrier of Corollary
   2.4.3 (`RelativeFullMassEpsilonBarrier`).  The derivation runs only in that
   direction: the `ε`-barrier also carries the mass clause (Xia's estimate
   (2.38)), which the statement below does not assert.  Since run 0050 the
   `ε`-barrier is proved too, from Step 1 of Lemma 2.4.4, so the single named
   form of this source material is
   `ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`.

2. `diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero` is the
   **measure chain on `xia-sgpt:page-0088`**: from the contact-set
   concentration of the envelope's Monge--Ampere measure (Theorem 2.4.4,
   `xia-sgpt:page-0079`), the contact comparison (Lemma 2.4.2,
   `xia-sgpt:page-0076`), multilinearity of the non-pluripolar product and
   hypothesis (2.40), Xia derives `theta^n_{eta a} = 1_{eta a = phi}
   theta^n_phi`; since `eta a <= phi` that is exactly the statement below.
   It is **no longer an interface** either: the chain is carried out in
   `Pending.DominationPrincipleContactChain`, where Lemma 2.4.2 is the proved
   `RooftopContactConcentration.measure_le_of_subset_contact` and the two
   inputs the workspace still lacks have been isolated as the named
   interfaces `diagonalPotentialMeasure_rooftopEnvelope_convexComb_noncontact_eq_zero`
   (Theorem 2.4.4 for this obstacle) and
   `Pending.NonPluripolarConvexCombLower` (BEGZ multilinearity).

Neither statement follows from Theorem 2.4.5 by instantiation: the first is a
`PSH` membership plus an explicit barrier inequality, the second is an
assertion about a measure.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleMiddleStage

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia, SGPT, Lemma 2.4.4 (`xia-sgpt:page-0083`) in the explicit envelope
form of Corollary 2.4.3 (`xia-sgpt:page-0087`).**  For `phi ≤ psi` of the same
positive non-pluripolar mass and any `a > 1`, the Perron envelope
`P_theta (a phi + (1 - a) psi)` is a genuine `theta`-PSH potential and
satisfies (2.29).

This is no longer an interface: it is derived in
`Pending.RooftopConvexCombBarrier` from the `ε`-barrier
`RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier`, itself proved
since run 0050 from Step 1 of Lemma 2.4.4,
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`, which is the single
named form of the same source result.  The statement is unchanged. -/
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
      convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi ≤ phi :=
  SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrier.isThetaPshPotential_rooftopEnvelope_convexComb
    omega theta hphi hpsi hle hpos hmass ha

/-- **Xia, SGPT, the measure chain in the proof of Theorem 2.4.5,
`xia-sgpt:page-0088`.**  Under the hypotheses of the ordered case, including
(2.40), the Perron barrier meets the reference off a `theta^n_phi`-null set.
This is Xia's `theta^n_{eta_a} = 1_{eta_a = phi} theta^n_phi`, read through
`eta_a ≤ phi`.

This is no longer an interface: it is proved in
`Pending.DominationPrincipleContactChain` from the envelope concentration
theorem 2.4.4 for the obstacle `a phi + (1 - a) psi` and the multilinearity
bound of `Pending.NonPluripolarConvexCombLower`.  The statement is
unchanged. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hmass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta psi hpsi)
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0)
    {a : ℝ} (ha : 1 < a) :
    diagonalPotentialMeasure theta phi hphi
      {x | rooftopEnvelope theta.val (convexComb a phi psi) x < phi x} = 0 :=
  SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain.diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero
    omega theta hphi hpsi hle hpos hmass hzero ha

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleMiddleStage
