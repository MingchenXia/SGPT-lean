import SGPT.Foundations.Analysis.Pending.NonBigSupremumMass
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit
import SGPT.Foundations.Analysis.Pending.TruncatedSingularityEnvelope
import SGPT.Foundations.Analysis.Pending.Envelopes

set_option autoImplicit false

/-!
# The contact property of the `P`-envelope, from Corollary 3.1.1

Xia, SGPT, Theorem 3.1.1 (`xia-sgpt:page-0100`, equation (3.7)) states
`theta^n_{P_theta[phi]} <= 1_{P_theta[phi] = 0} theta^n`.  Its proof
(`xia-sgpt:page-0101`) is, in the source's own words, *the same proof* as
Corollary 3.1.1 applied with ceiling `V_theta`, followed by "taking Corollary
2.4.4 into consideration".

This module carries out exactly that.  Corollary 3.1.1 is already PROVED in
`Pending.ShiftedRooftopContactProof` (from Lemma 3.1.1, i.e. from the single
concentration interface of `Pending.RooftopContactConcentration`), so what is
missing is the identification of the two envelopes and the last step.

1. **The identification.**  `Pending.singularityEnvelope` is the regularized
   supremum of the normalized potentials more singular than `phi`;
   `Pending.shiftedRooftopLimit theta V_theta phi` is the regularized
   supremum of the shifted rooftops `(phi + C) ∧ V_theta`.  They are equal,
   and at each level already the competitor *sets* coincide: a `theta`-PSH
   potential is `<= V_theta` exactly when it is `<= 0`, and the
   quasi-everywhere comparisons of the rooftop family upgrade to everywhere
   because both obstacles are genuine `theta`-PSH potentials.  This is
   `singularityEnvelope_eq_shiftedRooftopLimit` below, sorry-free.

2. **The last step** is Xia's Corollary 2.4.4 (`xia-sgpt:page-0094`), in its
   "in particular" clause `theta^n_{V_theta} = 1_{V_theta = 0} theta^n`,
   recorded here as the named interface
   `diagonalPotentialMeasure_thetaPshSupremum_lt_zero`.

The trade this module makes is deliberate.  Theorem 3.1.1 quantifies over all
`phi`; Corollary 2.4.4's second clause is its single instance at the canonical
reference `V_theta` (where `P_theta[V_theta] = V_theta`), so the split is not
free by hard rule 3 — it is justified by the proved half, which is the
identification of the two envelope constructions plus the reduction of every
`phi` to that one instance.  In the source the instance is proved from a
different theorem (2.4.7, the `C^{1,1}` regularity of `P_theta(f)`), not from
3.1.1, so the two are genuinely distinct source results.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- At each translation level the two competitor families coincide: the
shifted rooftop with ceiling `V_theta` and the truncated singularity envelope
have the same competitors.  The two differences are both removable — `u ≤ 0`
is the same as `u ≤ V_theta` for a `theta`-PSH `u`, and a quasi-everywhere
comparison with a genuine `theta`-PSH obstacle holds everywhere. -/
theorem rooftopCompetitors_min_thetaPshSupremum_eq
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (C : ℝ) :
    rooftopCompetitors theta.val
        (fun x => min (thetaPshSupremum theta.val x) (phi x + (C : EReal))) =
      truncatedSingularityCompetitors theta.val phi C := by
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨phi, hphi⟩
  have hshift : IsThetaPshPotential theta.val (fun x => phi x + (C : EReal)) :=
    hphi.add_const C
  ext u
  constructor
  · rintro ⟨hu, hqe⟩
    have huV : u ≤ thetaPshSupremum theta.val :=
      hu.1.le_of_quasiEverywhere_le hV.1 (hqe.mono fun x hx => hx.trans (min_le_left _ _))
    have hushift : u ≤ fun x => phi x + (C : EReal) :=
      hu.1.le_of_quasiEverywhere_le hshift.1
        (hqe.mono fun x hx => hx.trans (min_le_right _ _))
    exact ⟨⟨hu, fun x => (huV x).trans (thetaPshSupremum_le_zero theta.val x)⟩,
      fun x => hushift x⟩
  · rintro ⟨⟨hu, hu0⟩, hua⟩
    refine ⟨hu, quasiEverywhere_of_forall fun x => ?_⟩
    exact le_min (le_thetaPshSupremum hu hu0 x) (hua x)

omit [MeasurableSpace M] [BorelSpace M] in
/-- The shifted rooftop with ceiling `V_theta` is the truncated singularity
envelope of the same level. -/
theorem shiftedRooftop_thetaPshSupremum_eq
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (C : ℝ) :
    shiftedRooftop theta (thetaPshSupremum theta.val) phi C =
      truncatedSingularityEnvelope theta.val phi C := by
  simp only [shiftedRooftop, rooftopEnvelope, rooftopSupremum,
    truncatedSingularityEnvelope,
    rooftopCompetitors_min_thetaPshSupremum_eq theta hphi C]

omit [MeasurableSpace M] [BorelSpace M] in
/-- **`P_theta[phi]` is the regularized limit of the shifted rooftops with
ceiling `V_theta`.**  This is Xia's equation (3.4) read through the rooftop
family, and it is what lets Corollary 3.1.1 be applied to the `P`-envelope. -/
theorem singularityEnvelope_eq_shiftedRooftopLimit
    (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) :
    singularityEnvelope theta.val phi =
      shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi := by
  rw [SGPT.Foundations.Analysis.Pending.singularityEnvelope_eq_uscRegularization_iSup_truncated
      theta.val phi 0, shiftedRooftopLimit]
  refine congrArg uscRegularization (iSup_congr fun j => ?_)
  rw [zero_add, shiftedRooftop_thetaPshSupremum_eq theta hphi (j : ℝ)]

/-- **Xia, SGPT, Corollary 2.4.4 (`xia-sgpt:page-0094`), the "in particular"
clause.**  The source states
`theta^n_{V_theta} = 1_{V_theta = 0} theta^n`; since `V_theta ≤ 0`, the set
`{V_theta ≠ 0}` is `{V_theta < 0}`, so the clause says exactly that the
Monge--Ampere measure of the canonical reference gives no mass to
`{V_theta < 0}`.

The source's own hypothesis is `PSH(X, theta) ≠ ∅`, which is carried here by
the `theta`-PSH potential witnessing `hV`.

This is no longer an interface.  `Pending.NonBigSupremumMass` proves it by the
big/non-big trichotomy: dimension `0` outright, a big class by Xia's own
Lemmas 2.4.1 and 2.4.3, and a non-big class from the single named classical
input `diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`
(Boucksom's volume criterion, `bou02-volume:4.8`).  The statement is
unchanged. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
      {x | thetaPshSupremum theta.val x < 0} = 0 :=
  SGPT.Foundations.Analysis.Pending.NonBigSupremumMass.diagonalPotentialMeasure_thetaPshSupremum_lt_zero
    omega theta hV

-- `ConnectedSpace M` is part of the standing data of Xia's Chapters 2--3 and
-- is kept in the statement; the proof routes it through Corollary 3.1.1, which
-- does not need it.
set_option linter.unusedSectionVars false in
/-- **Xia, SGPT, Theorem 3.1.1 (`xia-sgpt:page-0100`, equation (3.7)), in the
null form.**  The non-pluripolar measure of the `P`-envelope gives no mass to
the set where the envelope is negative.

The proof is the source's: identify `P_theta[phi]` with the regularized limit
of the shifted rooftops over `V_theta`, apply Corollary 3.1.1
(`Pending.ShiftedRooftopContactProof`, itself resting on Lemma 3.1.1), and
finish with Corollary 2.4.4.  No analytic input beyond the latter. -/
theorem diagonalPotentialMeasure_singularityEnvelope_lt_zero [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi)) :
    diagonalPotentialMeasure theta (singularityEnvelope theta.val phi) hP
      {x | singularityEnvelope theta.val phi x < 0} = 0 := by
  classical
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨phi, hphi⟩
  have hid : singularityEnvelope theta.val phi =
      shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi :=
    singularityEnvelope_eq_shiftedRooftopLimit theta hphi
  revert hP
  rw [hid]
  intro hPlim
  have hsub : {x : M | shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi x < 0} ∩
      {x : M | shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi x =
        thetaPshSupremum theta.val x} ⊆
      {x : M | thetaPshSupremum theta.val x < 0} := by
    rintro x ⟨hlt, heq⟩
    exact lt_of_eq_of_lt heq.symm hlt
  refine le_antisymm ?_ zero_le
  calc diagonalPotentialMeasure theta
          (shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi) hPlim
        {x | shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi x < 0}
      ≤ diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
          ({x : M | shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi x < 0} ∩
            {x : M | shiftedRooftopLimit theta (thetaPshSupremum theta.val) phi x =
              thetaPshSupremum theta.val x}) :=
        diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_potential omega
          theta hV hphi hPlim _
    _ ≤ diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
          {x : M | thetaPshSupremum theta.val x < 0} := measure_mono hsub
    _ = 0 := diagonalPotentialMeasure_thetaPshSupremum_lt_zero omega theta hV

end

end SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
