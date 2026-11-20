import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamond
import SGPT.Foundations.Analysis.Pending.FiniteGeodesics

set_option autoImplicit false

/-!
# The rooftop mass diamond and its consumers without the lattice-mass hypothesis

Xia's Theorem 3.1.3 (`RooftopMassDiamond.mass_add_mass_le_mass_max_add_mass_rooftop`)
and its consumers in `RelativeFullMass`, `RelativeFullMassEnergyRooftopClosure` and
`FiniteGeodesics` carry the hypothesis
`hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta`,
the two mass identities of Step 1 of the source proof.  That hypothesis is now
a theorem on every connected compact Kähler manifold
(`RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction`), so each of them has
a form without it, recorded here.  The original statements are unchanged.

Every theorem below is its source statement instantiated at
`envelopeLatticeMassReduction omega theta`; the remaining analytic inputs are
those of the original theorem.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondUnconditional

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia, Theorem 3.1.3, (3.19) (`xia-sgpt:page-0108`--`page-0109`)**, on a
connected compact Kähler manifold, with no further hypothesis:
`∫ θ^n_φ + ∫ θ^n_ψ ≤ ∫ θ^n_{φ∨ψ} + ∫ θ^n_{φ∧ψ}` whenever `φ ∧ ψ` is `θ`-PSH. -/
theorem mass_add_mass_le_mass_max_add_mass_rooftop
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hmax : IsThetaPshPotential theta.val (fun x => max (u x) (v x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x)))) :
    diagonalPotentialMass theta u hu + diagonalPotentialMass theta v hv ≤
    diagonalPotentialMass theta (fun x => max (u x) (v x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hroof :=
  RooftopMassDiamond.mass_add_mass_le_mass_max_add_mass_rooftop omega theta hu hv hmax hroof
    (envelopeLatticeMassReduction omega theta)

/-- **Full mass is closed under (shifted) rooftops** (Xia, Proposition 3.1.21,
`E(X, θ; φ)` case), without the lattice-mass hypothesis. -/
theorem relativeFullMass_rooftop_add_const
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    let w := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFullMass theta phi w hphi ∧
      w ≤ u ∧ w ≤ fun x => v x + (C : EReal) :=
  Pending.relativeFullMass_rooftop_add_const hn omega theta phi u v hphi hu hv C
    (envelopeLatticeMassReduction omega theta)

/-- **Finite energy is closed under rooftops** (Xia, Proposition 3.1.21, `E¹`
case), without the lattice-mass hypothesis. -/
theorem relativeFiniteEnergy_rooftop
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : RelativeFiniteEnergy theta phi v hphi) :
    RelativeFiniteEnergy theta phi
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hphi :=
  RelativeFiniteEnergy.rooftop_of_kahler hn omega theta phi u v hphi hu hv
    (envelopeLatticeMassReduction omega theta)

/-- **Xia, Proposition 4.2.1, `E(X, θ; φ)` case**: the interior slices of the
finite geodesic between relative full-mass endpoints have relative full mass,
without the lattice-mass hypothesis. -/
theorem relativeFullMass_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  Pending.relativeFullMass_finiteGeodesic hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁
    (envelopeLatticeMassReduction omega theta) t ht

/-- **Xia, Proposition 4.2.1, `E¹(X, θ; φ)` case**: the interior slices of the
finite geodesic between relative finite-energy endpoints have relative finite
energy, without the lattice-mass hypothesis. -/
theorem relativeFiniteEnergy_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  Pending.relativeFiniteEnergy_finiteGeodesic hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁
    (envelopeLatticeMassReduction omega theta) t ht

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondUnconditional
