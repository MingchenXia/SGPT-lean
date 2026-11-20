import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope

set_option autoImplicit false

/-!
# Xia's Step 1 reduction for the rooftop mass diamond

The finite-truncation argument in `Pending.RooftopMassDiamondModel` proves
Xia's Theorem 3.1.3 for model potentials.  This file separates the preceding
reduction step from that argument.

There are two parts to Step 1 on `xia-sgpt:page-0108`.

* If either input has zero non-pluripolar mass, the diamond follows immediately
  from monotonicity.  This elementary branch is proved below.
* For positive masses, Proposition 3.1.3 preserves the masses of the two
  inputs under `P_theta`; that proposition is already proved in
  `Pending.SingularityEnvelopeMassProof`.  The remaining assertion is that the
  maximum and rooftop terms retain their masses after both inputs are replaced
  by their `P`-envelopes.  The source derives the maximum equality from the
  almost-everywhere limit of the truncations and Corollary 2.4.1, and the
  rooftop equality from Lemma 3.1.2.  Those two analytic passages are packaged
  as the single source-anchored interface
  `EnvelopeLatticeMassReduction`.

Consequently `mass_diamond_of_singularityEnvelope_diamond` is a concrete,
kernel-checked reduction: a model-potential diamond plus this one interface
implies the arbitrary-potential diamond.  It does not hide any use of the
still-open Step 1 limit arguments.
-/

open Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondReduction

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The exact residual input in Step 1 of Xia's Theorem 3.1.3
(`xia-sgpt:page-0108`).

For the maximum, the source uses the almost-everywhere convergence of
`((phi + C) /\\ V_theta) \\/ ((psi + C) /\\ V_theta)` to
`P_theta[phi] \\/ P_theta[psi]`, followed by Corollary 2.4.1 and Theorem
2.4.3.  For the rooftop, it invokes Lemma 3.1.2 after Proposition 3.1.3.
Both conclusions are kept together because they are exactly the unreplayed
analytic content needed by the formal reduction.
-/
def EnvelopeLatticeMassReduction (_omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) : Prop :=
  ∀ (phi psi : M → EReal)
    (_hphi : IsThetaPshPotential theta.val phi)
    (_hpsi : IsThetaPshPotential theta.val psi)
    (_hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi))
    (_hQ : IsThetaPshPotential theta.val (singularityEnvelope theta.val psi))
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hmaxP : IsThetaPshPotential theta.val
      (fun x => max (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hroofP : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)))),
    diagonalPotentialMass theta
        (fun x => max (singularityEnvelope theta.val phi x)
          (singularityEnvelope theta.val psi x)) hmaxP =
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax ∧
    diagonalPotentialMass theta
        (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
          (singularityEnvelope theta.val psi x))) hroofP =
      diagonalPotentialMass theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof

/-- The zero-mass branch at the beginning of Xia's proof of Theorem 3.1.3.
If `phi` has zero mass, the mass of `psi` is at most that of `phi \/ psi` by
monotonicity, so the rooftop term is not needed. -/
theorem mass_diamond_of_left_mass_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hphiMass : diagonalPotentialMass theta phi hphi = 0) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  have hpsiMax : diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax :=
    diagonalPotentialMass_mono_of_kahler omega hpsi hmax
      (MoreSingularOn.of_le fun x _ => le_max_right _ _)
  calc
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi
        = diagonalPotentialMass theta psi hpsi := by rw [hphiMass, zero_add]
    _ ≤ diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax := hpsiMax
    _ ≤ diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof :=
      le_add_of_nonneg_right bot_le

/-- The symmetric zero-mass branch at the beginning of Xia's proof. -/
theorem mass_diamond_of_right_mass_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hpsiMass : diagonalPotentialMass theta psi hpsi = 0) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  have hphiMax : diagonalPotentialMass theta phi hphi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax :=
    diagonalPotentialMass_mono_of_kahler omega hphi hmax
      (MoreSingularOn.of_le fun x _ => le_max_left _ _)
  calc
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi
        = diagonalPotentialMass theta phi hphi := by rw [hpsiMass, add_zero]
    _ ≤ diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax := hphiMax
    _ ≤ diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof :=
      le_add_of_nonneg_right bot_le

/-- **Xia, Theorem 3.1.3, Step 1 (`xia-sgpt:page-0108`).**  Once the diamond
is known for `P_theta[phi]` and `P_theta[psi]`, the one interface above reduces
it to `phi` and `psi` themselves. -/
theorem mass_diamond_of_singularityEnvelope_diamond
    [Nonempty M] (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi))
    (hQ : IsThetaPshPotential theta.val (singularityEnvelope theta.val psi))
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hmaxP : IsThetaPshPotential theta.val
      (fun x => max (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hroofP : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x))))
    (hprojection : EnvelopeLatticeMassReduction omega theta)
    (hmodelDiamond :
      diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP +
          diagonalPotentialMass theta (singularityEnvelope theta.val psi) hQ ≤
        diagonalPotentialMass theta
            (fun x => max (singularityEnvelope theta.val phi x)
              (singularityEnvelope theta.val psi x)) hmaxP +
          diagonalPotentialMass theta
            (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
              (singularityEnvelope theta.val psi x))) hroofP) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  obtain ⟨hmaxMass, hroofMass⟩ := hprojection phi psi hphi hpsi hP hQ hmax hmaxP hroof hroofP
  have hphiMass := singularityEnvelopeMassPreserving omega theta phi hphi hP
  have hpsiMass := singularityEnvelopeMassPreserving omega theta psi hpsi hQ
  calc
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi
        = diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP +
            diagonalPotentialMass theta (singularityEnvelope theta.val psi) hQ := by
          rw [hphiMass, hpsiMass]
    _ ≤ diagonalPotentialMass theta
          (fun x => max (singularityEnvelope theta.val phi x)
            (singularityEnvelope theta.val psi x)) hmaxP +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
            (singularityEnvelope theta.val psi x))) hroofP := hmodelDiamond
    _ = diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
      rw [hmaxMass, hroofMass]

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondReduction
