import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration

set_option autoImplicit false

/-!
# Xia's Lemma 3.1.1: the rooftop measure is carried by the two contact sets

For `phi, psi ∈ PSH(X, θ)` whose rooftop `phi ∧ psi = P_θ(min {phi, psi})` is
again a genuine potential, Xia's **Lemma 3.1.1** (`xia-sgpt:page-0099`,
inequality (3.2)) states

  `θ^n_{phi ∧ psi} ≤ 1_{phi ∧ psi = phi} θ^n_phi + 1_{phi ∧ psi = psi} θ^n_psi`,

so that the measure of the rooftop is carried by the union of the two contact
sets.  Its proof combines two results of §2.4 which this workspace does not
have:

* **Lemma 2.4.2** (`xia-sgpt:page-0076`, inequality (2.17)):
  `θ^n_{phi ∨ psi} ≥ 1_{phi ≥ psi} θ^n_phi + 1_{phi < psi} θ^n_psi`, whose
  corollary for `phi ≤ psi` is the contact comparison
  `1_{phi = psi} θ^n_phi ≤ 1_{phi = psi} θ^n_psi`.  Its proof, on
  `xia-sgpt:page-0076`--`xia-sgpt:page-0077`, truncates both potentials at
  `V_θ - k`, splits the maximum by the plurifine locality of non-pluripolar
  products (Proposition 2.2.1 (1)), passes `t → 0+` by the semicontinuity
  theorem 2.4.2 and `k → ∞` by the monotonicity theorem 2.4.3.  Neither
  plurifine locality for a general superlevel set nor the monotonicity
  theorem in that form exists in this workspace.
* **Theorem 2.4.4** (`xia-sgpt:page-0079`, equation (2.23)): the Monge--Ampère
  measure of `P_θ(f)` for quasi-continuous `f` is concentrated on the contact
  set `{P_θ(f) = f}`.  Its proof, on `xia-sgpt:page-0080`--`xia-sgpt:page-0082`,
  is the balayage lemma 2.4.3 run over a *plurifine*-open set, enlarged to an
  ordinary open set with small Bedford--Taylor capacity (Example 2.3.1),
  followed by convergence in capacity (Theorem 2.3.3) and, in Step 2, by
  quasi-continuity (Theorem 2.3.2) with Tietze extensions.  The whole §2.3
  capacity stack is absent from this workspace.

Both proof pages are now transcribed, so the cost is known rather than
guessed, and it is a paper-scale one: §2.3 capacity theory, plurifine
locality, and the monotonicity theorem in its net form.  The decision at the
time was therefore to KEEP (3.2) as a named interface rather than start that
development inside this lane.

**Update (run 0041, round 4).**  Two of the three pieces listed above are no
longer missing, and (3.2) is no longer an interface.

* *Plurifine locality* was in fact already available globally, as
  `Pending.GlobalMaxLocality.globalMixedMeasure_restrict_max_eq`.
* *Lemma 2.4.2* is now **proved**, in `Pending.MaxMassDecomposition`, together
  with its contact corollary.  Its proof does not use §2.3 capacity theory and
  does not use the monotonicity theorem in net form: it replaces the source's
  positive shift `t -> 0+` (which needs the decreasing-convergence theorem) by
  a *downward* shift, which is increasing, and so runs on the increasing
  semicontinuity inequality of Corollary 2.4.1 instead.
* *Theorem 2.4.4* is still missing, and is now the only open input.  It is
  isolated, specialised to `f = min {phi, psi}`, as
  `Pending.RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero`,
  and (3.2) is proved from it there.  The §2.3 capacity stack is still the
  cost of that one statement.

Lemma 3.1.1 is recorded here as **one** named interface, because it is the
single statement through which both contact theorems of §3.1 pass: Theorem
3.1.1 (`θ^n_{P_θ[phi]} ≤ 1_{P_θ[phi] = 0} θ^n`) and Corollary 3.1.1
(`θ^n_η ≤ 1_{η = psi} θ^n_psi` for `η = sup*_{C>0} (phi + C) ∧ psi`) are both
obtained from it by the same `C → ∞` limit, which
`Pending.ShiftedRooftopContactProof` carries out with no further input.

The hypothesis that the rooftop is a genuine `theta`-PSH potential is the
source's standing assumption in (3.2) ("assume that `phi ∧ psi ∈ PSH(X, θ)`");
without it the left-hand measure is not defined.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDecomposition

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, SGPT, Lemma 3.1.1, `xia-sgpt:page-0099`, inequality (3.2).**  The
diagonal non-pluripolar measure of the rooftop
`phi ∧ psi = P_theta (min {phi, psi})` is carried by the union of the two
contact sets, with the corresponding pieces of `theta^n_phi` and `theta^n_psi`
as bounds.

**Statement unchanged except for `[ConnectedSpace M]`** (human decision
I-0902 on I-0825).  It is now *proved*, in
`Pending.RooftopContactConcentration`, from the single named interface
`diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero` (Xia's
Theorem 2.4.4 for `f = min {phi, psi}`) together with the contact comparison
of Lemma 2.4.2, which is itself now proved in
`Pending.MaxMassDecomposition.contact_measure_le`.  The module docstring below
describes the situation as it stood before that; see
`Pending.RooftopContactConcentration` for the current frontier. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_min_le [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (B : Set M) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw B ≤
      diagonalPotentialMeasure theta phi hphi
          (B ∩ {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x
            = phi x}) +
        diagonalPotentialMeasure theta psi hpsi
          (B ∩ {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x
            = psi x}) :=
  RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_le
    omega theta hphi hpsi hw B

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDecomposition
