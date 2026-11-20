import SGPT.Foundations.Analysis.Pending.IGoodBasic
import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope

set_option autoImplicit false

/-!
# I-goodness and I-volume from the P-envelope mass theory

The equivalence `(2) ⇔ (3)` of Xia, Theorem 7.1.1 (`xia-sgpt:page-0250`,
`xia-sgpt:page-0251`) uses exactly three analytic inputs:

1. Proposition 3.1.3: `∫ θ_{P_θ[φ]}^n = ∫ θ_φ^n`;
2. Theorem 3.1.2, the `≥` direction of (3.8): if `φ` has positive mass,
   `ψ ≤ 0`, `φ ≼ ψ` and `∫ θ_φ^n = ∫ θ_ψ^n`, then `ψ ≤ P_θ[φ]`;
3. Proposition 3.2.9, `P_θ[φ] ≤ P_θ[φ]_I`, here obtained from strong openness
   (`Pending.StrongOpennessEnvelope`).

The first two are recorded below as explicit propositions about one background
form, and the equivalence is derived from them.  They are proved in
`Pending.SingularityEnvelopeMassProof` (`singularityEnvelopeMassPreserving`) and
`Pending.EqualMassEnvelope` (`equalMassLeSingularityEnvelope`), which discharge
`Pending.IGood.iGoodWith_iff_mass_eq_iVolume`.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass
open FirstPass.IEnvelope
open FirstPass.PositiveClasses
open DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- Xia, Proposition 3.1.3 (diagonal case) in one background: the P-envelope
has the same non-pluripolar mass as the potential. -/
def SingularityEnvelopeMassPreserving (theta : ClosedRealOneOneForm n M) :
    Prop :=
  ∀ (phi : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi)),
    diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP =
      diagonalPotentialMass theta phi hphi

/-- Xia, Theorem 3.1.2, the `≥` direction of (3.8) in one background: a
normalized less singular potential with the same positive mass lies below the
P-envelope.

This strengthens (3.8) as printed (`xia-sgpt:page-0101`), where the supremum runs
over `ψ` with the pointwise order `φ ≤ ψ`.  Here the hypothesis is only the
singularity preorder `MoreSingularOn phi psi univ` (`φ ≼ ψ`, i.e. `φ ≤ ψ + C` for
some constant `C`), which is weaker.  The strengthening is justified because the
envelope depends only on the singularity type
(`FirstPass.singularityEnvelope_eq_of_sameSingularityType`,
`FirstPass.singularityEnvelope_add_const`).  If `φ ≤ ψ + C`, then `φ - C ≤ ψ`
pointwise, and `φ - C` has the mass and the P-envelope of `φ`, so (3.8) for
`φ - C` gives `ψ ≤ P_θ[φ - C] = P_θ[φ]`. -/
def EqualMassLeSingularityEnvelope (theta : ClosedRealOneOneForm n M) : Prop :=
  ∀ (phi psi : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi),
    HasPositivePotentialMass theta phi hphi → psi ≤ 0 →
    MoreSingularOn phi psi univ →
    diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta psi hpsi →
    psi ≤ singularityEnvelope theta.val phi

omit [BorelSpace M] [Nonempty M] in
/-- The diagonal mass only depends on the potential. -/
theorem diagonalPotentialMass_congr {theta : ClosedRealOneOneForm n M}
    {u v : M → EReal} (huv : u = v) (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) :
    diagonalPotentialMass theta u hu = diagonalPotentialMass theta v hv := by
  subst huv
  exact diagonalPotentialMass_proof_independent hu hv

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine theta-PSH potential is more singular than its I-envelope. -/
theorem moreSingularOn_iSingularityEnvelope {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : IsThetaPshPotential θ φ) :
    MoreSingularOn φ (iSingularityEnvelope θ φ) univ := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_sub_const
  have hle := le_iSingularityEnvelope hC.1 hC.2 (iEquivalentOnManifold_sub_const φ C)
  refine ⟨C, fun x _ => ?_⟩
  calc φ x = (φ x - (C : EReal)) + (C : EReal) := by
        rw [EReal.sub_add_cancel]
    _ ≤ iSingularityEnvelope θ φ x + (C : EReal) := add_le_add_left (hle x) _

omit [BorelSpace M] in
/-- Xia, Theorem 7.1.1, `(2) ⇔ (3)`, from strong openness and the P-envelope
mass theory (Proposition 3.1.3 and Theorem 3.1.2) in the given background. -/
theorem iGoodWith_iff_mass_eq_iVolume_of_envelopeMass
    [ConnectedSpace M] (hSO : IncreasingStrongOpenness n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (_hbig : BigWithRespectToViaPotentials omega theta)
    (hPmass : SingularityEnvelopeMassPreserving theta)
    (hdom : EqualMassLeSingularityEnvelope theta)
    (hlocal : HasSmoothLocalPotentials theta.val) (phi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpositive : HasPositivePotentialMass theta phi hphi) :
    IGoodWith theta phi hphi ↔
      diagonalPotentialMass theta phi hphi = iVolume theta hlocal phi hphi := by
  have hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hlocal phi hphi
  have hI : IsThetaPshPotential theta.val (iSingularityEnvelope theta.val phi) :=
    iSingularityEnvelope_isThetaPshPotential theta.val theta.property.1
      theta.property.2 hlocal phi hphi
  constructor
  · rintro ⟨-, heq⟩
    unfold iVolume
    rw [← diagonalPotentialMass_congr heq hP hI, hPmass phi hphi hP]
  · intro hmass
    refine ⟨hpositive, le_antisymm ?_ ?_⟩
    · exact le_iSingularityEnvelope hP (singularityEnvelope_le_zero _ _)
        (iEquivalent_singularityEnvelope_of_strongOpenness hSO theta.val
          theta.property.1 theta.property.2 hlocal phi hphi).symm
    · exact hdom phi _ hphi hI hpositive (iSingularityEnvelope_le_zero _ _)
        (moreSingularOn_iSingularityEnvelope hphi) hmass

end

end SGPT.Foundations.Analysis.Pending
