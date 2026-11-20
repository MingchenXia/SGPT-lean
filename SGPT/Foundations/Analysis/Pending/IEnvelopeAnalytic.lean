import SGPT.Foundations.Analysis.FirstPass.IEnvelope
import SGPT.Foundations.Analysis.Pending.Envelopes
import SGPT.Foundations.Analysis.Pending.IEnvelopeCompetitors
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.IEquivalentMax

set_option autoImplicit false

/-!
# Pending analytic properties of the I-envelope

The upper envelope defining `P_θ[φ]_I` is a genuine locally nondegenerate
`θ`-PSH potential on a compact nonempty complex manifold
(`Pending.IEnvelopeCompetitors`).  Two analytic properties are recorded here:

1. `φ` and `P_θ[φ]_I` have the same multiplier-ideal germs at every positive
   exponent (Xia, Proposition 3.2.6, `xia-sgpt:page-0140` and
   `xia-sgpt:page-0141`);
2. `φ` and its ordinary P-envelope `P_θ[φ]` have the same multiplier-ideal
   germs at every positive exponent (Xia, Proposition 3.2.9,
   `xia-sgpt:page-0142`).

Property 2 is proved from strong openness for increasing sequences
(`Pending.StrongOpennessEnvelope`), which is proved from the Ohsawa--Takegoshi theorem
(`Pending.StrongOpennessRegularRoute`, no `sorry`).  Property 1 is proved from strong
openness and max-closure of I-equivalence (`Pending.IEnvelopeStrongOpenness`); max-closure
is proved in `Pending.IEquivalentMax` from strong openness and Demailly's approximation
theorem `Pending.DemaillyApproximation.exists_weightedL2_generators` (both proved).

All other theorems below are consequences of these two analytic boundaries,
the already pending ordinary-envelope regularity theorem, and the checked
order-theoretic envelope API.  In particular, idempotence and the comparisons
are not stored as fields of an auxiliary theory structure.

Closedness, type `(1,1)`, smooth local potentials, compactness, nonemptiness,
and the genuine `θ`-PSH condition on the reference potential remain explicit
in every public signature.
-/

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass
open FirstPass.IEnvelope

/-- The multiplier-ideal envelope of a
genuine `θ`-PSH potential is again a genuine `θ`-PSH potential.  This is the
PSH-envelope regularity underlying Xia, Definition 3.2.2 and Proposition
3.2.6 (`xia-sgpt:page-0139`--`xia-sgpt:page-0141`). -/
theorem iSingularityEnvelope_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (_hclosed : θ.IsClosed) (_h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IsThetaPshPotential θ (iSingularityEnvelope θ φ) :=
  iSingularityEnvelope_isThetaPshPotential_of_potential hlocal hφ

/-- **Xia, Proposition 3.2.6.** A genuine `θ`-PSH potential is I-equivalent to its
I-envelope.  Equality is required at all positive real exponents, matching the
checked germ-level definition. -/
theorem iEquivalent_iSingularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IEquivalentOnManifold (n := n) φ (iSingularityEnvelope θ φ) := by
  have _ := hclosed
  have _ := h11
  exact iEquivalent_iSingularityEnvelope_of_strongOpenness
    (increasingStrongOpenness_ofRegularRoute n) θ
    (IEquivalentMax.iEquivalentMaxClosed_of_strongOpenness
      (increasingStrongOpenness_ofRegularRoute n) θ) hlocal φ hφ

/-- **Xia, Proposition 3.2.9.** A genuine `θ`-PSH potential is I-equivalent to its
ordinary P-envelope.  Proved from strong openness. -/
theorem iEquivalent_singularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IEquivalentOnManifold (n := n) φ (singularityEnvelope θ φ) :=
  iEquivalent_singularityEnvelope_of_strongOpenness (increasingStrongOpenness_ofRegularRoute n) θ
    hclosed h11 hlocal φ hφ

/-- The I-envelope is idempotent.  This is the formal consequence in the
second assertion of Xia, Proposition 3.2.6. -/
theorem iSingularityEnvelope_idempotent
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    iSingularityEnvelope θ (iSingularityEnvelope θ φ) =
      iSingularityEnvelope θ φ := by
  exact (iSingularityEnvelope_eq_of_iEquivalent
    (iEquivalent_iSingularityEnvelope θ hclosed h11 hlocal φ hφ)).symm

/-- The I-envelope of a genuine potential is an actual I-model potential. -/
theorem iSingularityEnvelope_isIModelPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IsIModelPotential θ (iSingularityEnvelope θ φ) := by
  refine ⟨iSingularityEnvelope_isThetaPshPotential
    θ hclosed h11 hlocal φ hφ, ?_⟩
  exact (iSingularityEnvelope_idempotent
    θ hclosed h11 hlocal φ hφ).symm

/-- The ordinary P-envelope and the I-envelope of the same reference are
I-equivalent. -/
theorem iEquivalent_singularityEnvelope_iSingularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IEquivalentOnManifold (n := n) (singularityEnvelope θ φ)
      (iSingularityEnvelope θ φ) :=
  (iEquivalent_singularityEnvelope θ hclosed h11 hlocal φ hφ).symm.trans
    (iEquivalent_iSingularityEnvelope θ hclosed h11 hlocal φ hφ)

/-- Xia, Proposition 3.2.9: the ordinary P-envelope lies below the
I-envelope. -/
theorem singularityEnvelope_le_iSingularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    singularityEnvelope θ φ ≤ iSingularityEnvelope θ φ := by
  exact le_iSingularityEnvelope
    (singularityEnvelope_isThetaPshPotential θ hclosed h11 hlocal φ hφ)
    (singularityEnvelope_le_zero θ φ)
    (iEquivalent_singularityEnvelope θ hclosed h11 hlocal φ hφ).symm

/-- Equation (3.61) of Xia, Proposition 3.2.9:
`P_θ[P_θ[φ]]_I = P_θ[φ]_I`. -/
theorem iSingularityEnvelope_singularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    iSingularityEnvelope θ (singularityEnvelope θ φ) =
      iSingularityEnvelope θ φ := by
  exact (iSingularityEnvelope_eq_of_iEquivalent
    (iEquivalent_singularityEnvelope θ hclosed h11 hlocal φ hφ)).symm

/-- The I-envelope is also fixed by the ordinary P-envelope.  This follows
from the two envelope comparisons and does not require an additional analytic
boundary. -/
theorem singularityEnvelope_iSingularityEnvelope
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    singularityEnvelope θ (iSingularityEnvelope θ φ) =
      iSingularityEnvelope θ φ := by
  have hI : IsThetaPshPotential θ (iSingularityEnvelope θ φ) :=
    iSingularityEnvelope_isThetaPshPotential θ hclosed h11 hlocal φ hφ
  apply le_antisymm
  · calc
      singularityEnvelope θ (iSingularityEnvelope θ φ) ≤
          iSingularityEnvelope θ (iSingularityEnvelope θ φ) :=
        singularityEnvelope_le_iSingularityEnvelope θ hclosed h11 hlocal
          (iSingularityEnvelope θ φ) hI
      _ = iSingularityEnvelope θ φ :=
        iSingularityEnvelope_idempotent θ hclosed h11 hlocal φ hφ
  · exact self_le_singularityEnvelope hI
      (iSingularityEnvelope_le_zero θ φ)

end

end SGPT.Foundations.Analysis.Pending
