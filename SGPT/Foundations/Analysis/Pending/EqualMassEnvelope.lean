import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.DominationPrinciple

set_option autoImplicit false

/-!
# Equal mass and the P-envelope

Xia, Theorem 3.1.2, the `≥` direction of (3.8) (`xia-sgpt:page-0101`): if `φ` has
positive mass, `ψ ≤ 0`, `φ ≼ ψ` and `∫ θ_φ^n = ∫ θ_ψ^n`, then `ψ ≤ P_θ[φ]`.

This is a strengthening of (3.8) as printed, which takes the pointwise order
`φ ≤ ψ`; the singularity preorder `φ ≼ ψ` (`MoreSingularOn phi psi univ`, i.e.
`φ ≤ ψ + C` for some constant `C`) is weaker.  It is justified because the envelope
depends only on the singularity type
(`FirstPass.singularityEnvelope_eq_of_sameSingularityType`): `φ - C ≤ ψ` pointwise,
and `φ - C` has the mass and the P-envelope of `φ`, so (3.8) for `φ - C` gives the
claim.  The proof below uses `φ ≼ ψ` only through `P_θ[φ] ≤ P_θ[ψ]`.

The proof is the source's.  `θ^n_{P_θ[φ]}` does not charge `{P_θ[φ] < 0}`, which
contains `{P_θ[φ] < ψ}`.  Both `P_θ[φ]` and `ψ` are more singular than `P_θ[ψ]`, and all
of `φ`, `P_θ[φ]`, `ψ`, `P_θ[ψ]` have the same mass by Proposition 3.1.3, so the
domination principle gives `ψ ≤ P_θ[φ]`.  The remaining analytic inputs are the
interfaces of `Pending.DominationPrinciple`; Proposition 3.1.3 is proved.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass FirstPass.PositiveClasses DiagonalMass DominationPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- Xia, Theorem 3.1.2, the `≥` direction of (3.8), on a connected compact Kähler
manifold. -/
theorem equalMassLeSingularityEnvelope [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) : EqualMassLeSingularityEnvelope theta := by
  intro phi psi hphi hpsi hpos hpsi0 hmore hmass
  have hlocal := hphi.1.hasSmoothLocalPotentials
  have hP := singularityEnvelope_isThetaPshPotential theta.val theta.property.1
    theta.property.2 hlocal phi hphi
  have hQ := singularityEnvelope_isThetaPshPotential theta.val theta.property.1
    theta.property.2 hlocal psi hpsi
  have hPmass := singularityEnvelopeMassPreserving omega theta phi hphi hP
  have hQmass := singularityEnvelopeMassPreserving omega theta psi hpsi hQ
  refine le_of_diagonalPotentialMeasure_lt_eq_zero omega theta hP hpsi hQ
    (by unfold HasPositivePotentialMass; rwa [hPmass])
    (by unfold HasPositivePotentialMass; rwa [← hmass])
    (MoreSingularOn.of_le fun x _ => singularityEnvelope_mono hmore x)
    (moreSingularOn_singularityEnvelope hpsi)
    (by rw [hPmass, hQmass, hmass]) hQmass.symm ?_
  refine measure_mono_null (fun x hx => ?_)
    (diagonalPotentialMeasure_singularityEnvelope_lt_zero omega theta hphi hP)
  exact lt_of_lt_of_le hx (hpsi0 x)

end

end SGPT.Foundations.Analysis.Pending
