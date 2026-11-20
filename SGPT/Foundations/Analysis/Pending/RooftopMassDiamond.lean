import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondAssembly
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-!
# The rooftop mass diamond

Xia, SGPT, Theorem 3.1.3 (`xia-sgpt:page-0108`): for `φ, ψ ∈ PSH(X, θ)` whose
rooftop `φ ∧ ψ` is again in `PSH(X, θ)`,

  `∫ θ_φ^n + ∫ θ_ψ^n ≤ ∫ θ_{φ ∨ ψ}^n + ∫ θ_{φ ∧ ψ}^n`.   (3.19)

The source proof reduces to the model potentials `P_θ[φ]`, `P_θ[ψ]` using
Proposition 3.1.3, Corollary 2.4.1, Theorem 2.4.3 and Lemma 3.1.2, then runs a
partial-mass comparison on the truncations.  The checked assembly now carries
out that composition.  Its only still-external Step 1 input is displayed
explicitly below as `EnvelopeLatticeMassReduction`.  The two zero-mass cases
are direct monotonicity arguments, while in the remaining positive-mass case
ordinary P-envelope idempotence is proved in
`RooftopEnvelopeIdempotencePositive` from mass preservation and the checked
equal-mass comparison theorem.  Thus this theorem does not consume the
separate zero-mass P-envelope interface.

It is the *only* thing separating the relative full-mass rooftop from its
mass statement: once the rooftop of two relative full-mass potentials is known
to be `θ`-PSH (which `Pending.isThetaPshPotential_rooftop_add_const` now
proves), the diamond plus mixed-mass monotonicity gives that rooftop the
reference mass, because both `∫θ_φ^n` and `∫θ_ψ^n` equal the reference mass
and `φ ∨ ψ` is squeezed between `φ` and a finite translate of the reference.

The hypothesis `hmax` is not an extra assumption: the maximum of two `θ`-PSH
potentials is `θ`-PSH.  It is taken as an argument only to keep this module
upstream of the modules where that closure property is proved.

The standing hypotheses of Xia's Chapters 2--3 are kept: `M` is a connected
compact Kähler manifold, the Kähler background being `omega`.  The source
proof runs through the monotonicity theorem 2.4.3, which is the Kähler
statement, and without `omega` the masses appearing here are not known to be
finite.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamond

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, SGPT, Theorem 3.1.3, equation (3.19)**
(`xia-sgpt:page-0108`--`xia-sgpt:page-0109`).  This is the checked final
assembly, conditional only on the exact Step 1 lattice-mass input isolated in
`RooftopMassDiamondReduction.EnvelopeLatticeMassReduction`. -/
theorem mass_add_mass_le_mass_max_add_mass_rooftop [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))))
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    diagonalPotentialMass theta u hu + diagonalPotentialMass theta v hv ≤
    diagonalPotentialMass theta (fun x => max (u x) (v x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hroof := by
  by_cases hu0 : diagonalPotentialMass theta u hu = 0
  · exact RooftopMassDiamondReduction.mass_diamond_of_left_mass_eq_zero
      omega theta hu hv hmax hroof hu0
  by_cases hv0 : diagonalPotentialMass theta v hv = 0
  · exact RooftopMassDiamondReduction.mass_diamond_of_right_mass_eq_zero
      omega theta hu hv hmax hroof hv0
  have hupos : HasPositivePotentialMass theta u hu := by
    unfold HasPositivePotentialMass
    exact (pos_iff_ne_zero).mpr hu0
  have hvpos : HasPositivePotentialMass theta v hv := by
    unfold HasPositivePotentialMass
    exact (pos_iff_ne_zero).mpr hv0
  exact RooftopMassDiamondAssembly.mass_diamond_of_envelope_model_limit omega theta
    hu hv hroof
    (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega theta u hu hupos).symm
    (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega theta v hv hvpos).symm
    hprojection

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamond
