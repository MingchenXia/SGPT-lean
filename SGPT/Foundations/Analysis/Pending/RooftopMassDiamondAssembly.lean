import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondReduction
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge

set_option autoImplicit false

/-!
# Final assembly of Xia's rooftop mass diamond

The three preceding modules isolate the three logical stages of Xia's proof of
Theorem 3.1.3:

* `RooftopMassDiamondReduction` reduces arbitrary potentials to their
  `P_theta`-envelopes (Step 1 on `xia-sgpt:page-0108`);
* `RooftopMassDiamondModel` proves the finite truncation estimate for model
  potentials (Step 2 on `xia-sgpt:page-0108`--`page-0109`);
* `RooftopMassDiamondLimit` passes that finite estimate to the ordinary rooftop;
* `RooftopMassDiamondTruncationBridge` proves the required truncation convergence
  in chart-local `L¹`.

This file performs the remaining *formal* composition, without adding an
analytic axiom.  Its hypotheses display the residual facts precisely:

1. the two `P_theta`-envelopes are model (idempotence);
2. Xia's Step 1 lattice-mass comparison, represented by
   `EnvelopeLatticeMassReduction`.

In particular, the theta-PSH/nonpositivity/`L¹` package needed by Corollary
2.4.2 is no longer a hypothesis of this assembly: it is consumed directly from
`RooftopMassDiamondTruncationBridge`.

Source: Xia, *Singularities in Global Pluripotential Theory*, Theorem 3.1.3,
`xia-sgpt:page-0108`--`page-0109`.
-/

open Filter Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondAssembly

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondReduction
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The model-potential conclusion of Xia's final `C → ∞` passage.  The
truncation data are obtained from the checked decreasing-rooftop bridge. -/
theorem model_mass_diamond_of_truncation_bridge
    [Nonempty M] [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x))
        (SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hphi hpsi) +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  have hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hphi hpsi
  obtain ⟨htrunc, htrunc0, hL1⟩ :=
    modelTruncationRooftopData_limit_bridge theta hphi hpsi hphimodel hpsimodel hmax hroof
  exact model_mass_diamond_of_truncation_limit omega theta hphi hpsi
    hphimodel hpsimodel hmax hroof htrunc htrunc0 hL1

/-- **Xia, Theorem 3.1.3 (`xia-sgpt:page-0108`--`page-0109`), assembled.**

The proof is entirely the composition of the checked Step 1 reduction and the
checked model-potential endpoint.  The hypotheses are the still-visible
analytic inputs named in the module documentation; no new interface is added.
-/
theorem mass_diamond_of_envelope_model_limit
    [Nonempty M] [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hPmodel : singularityEnvelope theta.val phi =
      singularityEnvelope theta.val (singularityEnvelope theta.val phi))
    (hQmodel : singularityEnvelope theta.val psi =
      singularityEnvelope theta.val (singularityEnvelope theta.val psi))
    (hprojection : EnvelopeLatticeMassReduction omega theta) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x))
        (SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hphi hpsi) +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  have hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hphi.1.hasSmoothLocalPotentials phi hphi
  have hQ : IsThetaPshPotential theta.val (singularityEnvelope theta.val psi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hpsi.1.hasSmoothLocalPotentials psi hpsi
  have hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hphi hpsi
  have hmaxP : IsThetaPshPotential theta.val
      (fun x => max (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hP hQ
  have hrooflephi : rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ phi := by
    intro x
    have h := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    simpa only [EReal.coe_zero, add_zero] using h.1 x
  have hrooflepsi : rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ psi := by
    intro x
    have h := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    simpa only [EReal.coe_zero, add_zero] using h.2 x
  have hR : IsThetaPshPotential theta.val
      (singularityEnvelope theta.val
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hroof.1.hasSmoothLocalPotentials _ hroof
  have hRleP : singularityEnvelope theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) ≤
      singularityEnvelope theta.val phi :=
    singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hrooflephi x)
  have hRleQ : singularityEnvelope theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) ≤
      singularityEnvelope theta.val psi :=
    singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hrooflepsi x)
  have hroofP : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x))) := by
    apply isThetaPshPotential_rooftop_of_nonempty
    · refine ⟨singularityEnvelope theta.val
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))), hR, ?_⟩
      exact quasiEverywhere_of_forall fun x => le_min (hRleP x) (hRleQ x)
    · simpa only [EReal.coe_zero, add_zero] using
        (rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta
          (singularityEnvelope theta.val phi) (singularityEnvelope theta.val psi) hP 0)
  have hmodelDiamond :
      diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP +
          diagonalPotentialMass theta (singularityEnvelope theta.val psi) hQ ≤
        diagonalPotentialMass theta
            (fun x => max (singularityEnvelope theta.val phi x)
              (singularityEnvelope theta.val psi x)) hmaxP +
          diagonalPotentialMass theta
            (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
              (singularityEnvelope theta.val psi x))) hroofP :=
    model_mass_diamond_of_truncation_bridge omega theta hP hQ hPmodel hQmodel hroofP
  exact mass_diamond_of_singularityEnvelope_diamond omega theta hphi hpsi hP hQ
    hmax hmaxP hroof hroofP hprojection hmodelDiamond

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondAssembly
