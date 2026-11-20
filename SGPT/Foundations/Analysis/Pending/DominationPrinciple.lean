import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.DominationPrincipleMiddleStage
import SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
import SGPT.Foundations.Analysis.FirstPass.Envelopes
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

/-!
# The domination principle and the contact property of the P-envelope

Two results of non-pluripolar pluripotential theory on a connected compact Kähler
manifold, stated for the actual diagonal non-pluripolar measures:

1. **Contact property of the P-envelope** (Xia, Theorem 3.1.1, `xia-sgpt:page-0100`,
   in the form used for Theorem 3.1.2): `θ^n_{P_θ[φ]} ≤ 1_{P_θ[φ] = 0} θ^n`, hence the
   measure of `P_θ[φ]` does not charge `{P_θ[φ] < 0}`.  The source proof uses the
   concentration of the Monge–Ampère measure of an envelope on its contact set
   (Theorem 2.4.4, a balayage argument) and the semicontinuity theorem for
   increasing sequences.
2. **Domination principle** (Xia, Theorem 2.4.5; Darvas–Di Nezza–Lu): if `φ`, `ψ`
   have positive mass, are both more singular than some `ϕ` of the same mass, and
   `θ^n_φ` does not charge `{φ < ψ}`, then `ψ ≤ φ`.  The source proof uses the
   envelope concentration theorem again and Lemma 2.4.2 on contact sets.

Both rest on the concentration theorem for envelopes of quasi-continuous obstacles,
which needs capacity theory and the Perron–Bremermann balayage on the manifold.
Connectedness is kept as in the source: without it a zero-mass component would
make the domination principle false.

Both items are now **proved**.  Item 2 comes from the two ends of Xia's own
argument (`Pending.DominationPrincipleReduction`), the unconditional
properties of the Perron barrier family
(`Pending.DominationPrincipleBarrier`), and the analytic middle stage
(`Pending.DominationPrincipleMiddleStage`).  Item 1 is proved in
`Pending.SingularityEnvelopeContact` by the source's own route: `P_theta[phi]`
is the regularized limit of the shifted rooftops over `V_theta`, so Corollary
3.1.1 applies to it, and Corollary 2.4.4 turns the contact set
`{P = V_theta}` into `{P = 0}`.  Corollary 2.4.4 itself is proved
for a big class, trivial in dimension `0`, and for a non-big class rests on the
single named classical input
`Pending.NonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`
(Boucksom: a pseudo-effective class is big iff its volume is positive).
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.DominationPrinciple

open FirstPass FirstPass.PositiveClasses DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier
open SGPT.Foundations.Analysis.Pending.DominationPrincipleMiddleStage
open SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] [ConnectedSpace M]

/-- **Xia, Theorem 3.1.1 (`xia-sgpt:page-0100`).** The non-pluripolar measure
of the P-envelope does not charge the set where the envelope is negative.

This is no longer an interface: it is proved in
`Pending.SingularityEnvelopeContact` from Corollary 3.1.1 and Xia's Corollary
2.4.4 (`xia-sgpt:page-0094`), the latter now discharged by the big/non-big
trichotomy of `Pending.NonBigSupremumMass`.  The statement is unchanged. -/
theorem diagonalPotentialMeasure_singularityEnvelope_lt_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi)) :
    diagonalPotentialMeasure theta (singularityEnvelope theta.val phi) hP
      {x | singularityEnvelope theta.val phi x < 0} = 0 :=
  SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
    omega theta hphi hP

omit [BorelSpace M] [Nonempty M] [ConnectedSpace M] in
/-- The contact conclusion is elementary when the envelope is already
normalized pointwise to zero.  The substantive contact theorem above is what
removes this extra normalization hypothesis. -/
theorem diagonalPotentialMeasure_singularityEnvelope_lt_zero_of_eq_zero
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi))
    (henv : singularityEnvelope theta.val phi = 0) :
    diagonalPotentialMeasure theta (singularityEnvelope theta.val phi) hP
      {x | singularityEnvelope theta.val phi x < 0} = 0 := by
  have hlt : {x | singularityEnvelope theta.val phi x < 0} = ∅ := by
    ext x
    simp [henv]
  rw [hlt]
  simp

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] [ConnectedSpace M] in
/-- The standard normalization of a singularity envelope is at most zero.
Consequently, any independent pointwise nonnegativity estimate identifies it
with the zero potential. -/
theorem singularityEnvelope_eq_zero_of_nonneg
    (theta : SmoothRealForm n M 2) (phi : M → EReal)
    (hnonneg : 0 ≤ singularityEnvelope theta phi) :
    singularityEnvelope theta phi = 0 := by
  apply le_antisymm
  · exact singularityEnvelope_le_zero theta phi
  · exact hnonneg

omit [BorelSpace M] [Nonempty M] [ConnectedSpace M] in
/-- A nonnegative normalized envelope has empty negative contact set, so its
diagonal potential measure gives that set zero mass. -/
theorem diagonalPotentialMeasure_singularityEnvelope_lt_zero_of_nonneg
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi))
    (hnonneg : 0 ≤ singularityEnvelope theta.val phi) :
    diagonalPotentialMeasure theta (singularityEnvelope theta.val phi) hP
      {x | singularityEnvelope theta.val phi x < 0} = 0 := by
  apply diagonalPotentialMeasure_singularityEnvelope_lt_zero_of_eq_zero theta hP
  exact singularityEnvelope_eq_zero_of_nonneg theta.val phi hnonneg

-- The source hypotheses `hpsipos` and `hpsimass` turn out to be redundant: the
-- opening reduction derives the mass and positivity of `max phi psi` from
-- `hphipos` and `hphimass` alone.  They are part of an existing statement, so
-- they are kept and the unused-binder linter is switched off here rather than
-- the signature being changed.
set_option linter.unusedVariables false in
/-- **Xia, Theorem 2.4.5, the domination principle** (`xia-sgpt:page-0087`--
`xia-sgpt:page-0089`).  Proved here from the two ends of the source argument
and the two named source theorems of its analytic middle stage; the statement
is unchanged. -/
theorem le_of_diagonalPotentialMeasure_lt_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi eta : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (heta : IsThetaPshPotential theta.val eta)
    (hphipos : HasPositivePotentialMass theta phi hphi)
    (hpsipos : HasPositivePotentialMass theta psi hpsi)
    (hphieta : MoreSingularOn phi eta univ) (hpsieta : MoreSingularOn psi eta univ)
    (hphimass : diagonalPotentialMass theta phi hphi = diagonalPotentialMass theta eta heta)
    (hpsimass : diagonalPotentialMass theta psi hpsi = diagonalPotentialMass theta eta heta)
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0) :
    psi ≤ phi := by
  refine le_of_ordered_case omega hphi hpsi heta hphipos hphieta hpsieta hphimass hzero ?_
  intro chi hchi hlechi hchipos hchieta hchimass hchizero
  have hmasseq : diagonalPotentialMass theta phi hphi =
      diagonalPotentialMass theta chi hchi := by rw [hphimass, hchimass]
  have hchitop : ∀ x, chi x ≠ ⊤ := ne_top_of_isThetaPshPotential hchi
  refine le_of_null_barrier_family
    (eta := fun a => rooftopEnvelope theta.val (convexComb a phi chi))
    theta hphi hchi.1 hphipos (fun a ha => ?_) (fun a b ha hab => ?_)
    (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
  · exact (isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hchi
      hlechi hphipos hmasseq ha).1.1
  · exact rooftopEnvelope_convexComb_antitone hlechi hchitop
      (lt_trans zero_lt_one ha) hab
  · exact rooftopEnvelope_convexComb_le hphi hlechi hchitop ha.le
  · exact (isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hchi
      hlechi hphipos hmasseq ha).2
  · exact diagonalPotentialMeasure_rooftopEnvelope_convexComb_lt_eq_zero omega theta
      hphi hchi hlechi hphipos hmasseq hchizero ha

omit [BorelSpace M] [Nonempty M] [ConnectedSpace M] in
/-- A strict comparison locus which is open cannot be null for an actual
diagonal measure that is positive on nonempty open sets.  Thus in this
full-support branch the measure-zero hypothesis alone gives domination.

This is useful, for example, once separate regularity arguments make
`{x | φ x < ψ x}` open.  It deliberately does not assert that the diagonal
non-pluripolar measure of an arbitrary singular potential has this positivity:
establishing that fact is part of the genuinely analytic domination principle. -/
theorem le_of_diagonalPotentialMeasure_lt_eq_zero_of_isOpen
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    [Measure.IsOpenPosMeasure (diagonalPotentialMeasure theta phi hphi)]
    (hopen : IsOpen {x | phi x < psi x})
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0) :
    psi ≤ phi := by
  have hempty : {x | phi x < psi x} = ∅ := hopen.eq_empty_of_measure_zero hzero
  intro x
  apply le_of_not_gt
  intro hx
  have hxnot : x ∉ {y | phi y < psi y} := by simp [hempty]
  exact hxnot hx

omit [BorelSpace M] [Nonempty M] [ConnectedSpace M] in
/-- On a subsingleton space, positive total mass turns the vanishing of the
strict comparison set into the pointwise domination conclusion.  In general,
the missing analytic content is precisely a comparison principle extending
this implication beyond this degenerate case. -/
theorem le_of_diagonalPotentialMeasure_lt_eq_zero_of_subsingleton
    [Subsingleton M] (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hphipos : HasPositivePotentialMass theta phi hphi)
    (hzero : diagonalPotentialMeasure theta phi hphi {x | phi x < psi x} = 0) :
    psi ≤ phi := by
  intro x
  apply le_of_not_gt
  intro hx
  have hlevel : {y | phi y < psi y} = univ := by
    ext y
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    simpa only [Subsingleton.elim y x] using hx
  have hmass : diagonalPotentialMass theta phi hphi = 0 := by
    change diagonalPotentialMeasure theta phi hphi univ = 0
    simpa only [hlevel] using hzero
  exact (ne_of_gt hphipos) hmass

end

end SGPT.Foundations.Analysis.Pending.DominationPrinciple
