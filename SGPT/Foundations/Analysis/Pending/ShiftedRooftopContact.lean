import SGPT.Foundations.Analysis.Pending.DominationPrinciple
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof

set_option autoImplicit false

/-!
# The contact property of the shifted rooftop limit

Let `u, v ∈ PSH(X, θ)` and let

  `η := sup*_{C > 0} (v + C) ∧ u`

be the regularized limit of the shifted rooftop family, `P_θ[v](u)` in Xia's
notation.  **Corollary 3.1.1** (`xia-sgpt:page-0101`) states that

  `θ^n_η ≤ 1_{η = u} θ^n_u`,

so that the diagonal non-pluripolar measure of `η` is carried by the contact
set where `η` already equals its ceiling.  The source proof is the same
argument as for the contact property of the `P`-envelope, Theorem 3.1.1: the
rooftop measure decomposition **Lemma 3.1.1** (`xia-sgpt:page-0099`,
inequality (3.2)) applied to each `(v + C) ∧ u`, the dominated convergence
theorem for `1_{v + C ≤ u} θ^n_v` and the semicontinuity theorem Corollary
2.4.1 for `θ^n_{(v + C) ∧ u} ⇀ θ^n_η`.

Lemma 3.1.1 rests on Lemma 2.4.2 (`xia-sgpt:page-0076`) and on the envelope
concentration theorem 2.4.4 (`xia-sgpt:page-0079`), neither of which exists in
this workspace; it is recorded as the named interface
`Pending.RooftopMassDecomposition`.  Everything else in the source proof is
now available: `Pending.ShiftedRooftopContactProof` carries out the `C → ∞`
step and PROVES Corollary 3.1.1 for a shifted rooftop family whose members are
genuine `theta`-PSH potentials below the ceiling — which is the situation of
every consumer here.  `shiftedRooftopLimit_eq_of_mass` below uses that proved
form, so it no longer depends on any interface of this file.

The version stated below for a bare `(hu, hv, heta)` is proved too: the
feasibility of the rooftop family, which looked like an extra hypothesis, is
forced by the nondegeneracy of the limit.  If every `(v + C) wedge u` were
`-infinity` then so would be `eta`.

This is not a restatement of the exhaustion theorem it feeds: the
interface is an inequality between two measures, while the consumer
`Pending.RelativeFullMass.relativeFullMass_rooftop_add_const_tendsto` is a
chart-local `L¹` convergence statement, and the passage from the first to the
second runs through the domination principle, the increasing-limit mass
theorem and an almost-everywhere regularization identity.  Neither implies the
other by instantiation.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ShiftedRooftopContact

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DominationPrinciple
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof
open SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

-- `ConnectedSpace M` is part of this statement's standing hypotheses and the
-- proof does not need it; removing it would change the statement, so the
-- unused-section-variable linter is switched off here instead.
set_option linter.unusedSectionVars false in
/-- **Xia, SGPT, Corollary 3.1.1 (`xia-sgpt:page-0101`).**  The diagonal
non-pluripolar measure of `η = sup*_{C > 0} (v + C) ∧ u` is carried by the
contact set `{η = u}`: `θ^n_η ≤ 1_{η = u} θ^n_u`, evaluated here on an
arbitrary set.

Proved in `Pending.ShiftedRooftopContactProof` from Lemma 3.1.1
(`Pending.RooftopMassDecomposition`), which is the one remaining interface on
this route.  The bare hypotheses suffice: nondegeneracy of `η` alone forces
the shifted rooftops to have competitors from some translation on, and every
competitor lies below `u` quasi-everywhere hence everywhere. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_le_contact
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v))
    (B : Set M) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta B ≤
      diagonalPotentialMeasure theta u hu
        (B ∩ {x | shiftedRooftopLimit theta u v x = u x}) :=
  diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_potential omega theta
    hu hv heta B

/-- The null form of Corollary 3.1.1 consumed by the domination principle:
the measure of `η` gives no mass to the set where `η` is strictly below its
ceiling. -/
theorem diagonalPotentialMeasure_shiftedRooftopLimit_lt_eq_zero
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (heta : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v)) :
    diagonalPotentialMeasure theta (shiftedRooftopLimit theta u v) heta
      {x | shiftedRooftopLimit theta u v x < u x} = 0 := by
  have hbound := diagonalPotentialMeasure_shiftedRooftopLimit_le_contact
    omega theta hu hv heta {x | shiftedRooftopLimit theta u v x < u x}
  have hempty : {x | shiftedRooftopLimit theta u v x < u x} ∩
      {x | shiftedRooftopLimit theta u v x = u x} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_and]
    intro hlt heq
    exact absurd heq (ne_of_lt hlt)
  rw [hempty] at hbound
  simpa using hbound

/-- **Xia, Proposition 3.1.24** (`xia-sgpt:page-0134`, proof on
`xia-sgpt:page-0135`), in the relative full-mass situation.  If `u` and every
member of the shifted rooftop family carry the full mass of the model
potential `phi`, then the regularized limit of that family is exactly `u`.

The proof is the source's: the limit is a `theta`-PSH potential below `u` of
the same mass (`Pending.ShiftedRooftopLimit`), Corollary 3.1.1 says its
measure does not charge `{eta < u}`, and the domination principle Theorem
2.4.5 then forces `u ≤ eta`. -/
theorem shiftedRooftopLimit_eq_of_mass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi u v : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hphi0 : phi ≤ 0)
    (hphipos : 0 < diagonalPotentialMass theta phi hphi)
    (hu : IsThetaPshPotential theta.val u) (huphi : u ≤ phi)
    (humass : diagonalPotentialMass theta u hu =
      diagonalPotentialMass theta phi hphi)
    (hv : IsThetaPshPotential theta.val v)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (hwmass : ∀ j : ℕ, diagonalPotentialMass theta
      (shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) =
        diagonalPotentialMass theta phi hphi) :
    shiftedRooftopLimit theta u v = u := by
  have hu0 : u ≤ 0 := huphi.trans hphi0
  have hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u := fun C =>
    (rooftopEnvelope_min_add_const_le_obstacles hu.1 hv.1 C).1
  have hetapsh : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v) :=
    isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0
  have hetale : shiftedRooftopLimit theta u v ≤ u :=
    shiftedRooftopLimit_le theta hu hle
  have hetamass : diagonalPotentialMass theta (shiftedRooftopLimit theta u v)
      hetapsh = diagonalPotentialMass theta phi hphi :=
    diagonalPotentialMass_shiftedRooftopLimit hn omega theta _ hw hle hu0 hwmass
  have hetapos : HasPositivePotentialMass theta (shiftedRooftopLimit theta u v)
      hetapsh := by
    change 0 < diagonalPotentialMass theta (shiftedRooftopLimit theta u v) hetapsh
    rw [hetamass]
    exact hphipos
  have hupos : HasPositivePotentialMass theta u hu := by
    change 0 < diagonalPotentialMass theta u hu
    rw [humass]
    exact hphipos
  have hzero := diagonalPotentialMeasure_shiftedRooftopLimit_lt_eq_zero_of_family
    omega theta hu hv hw hetapsh
  have hge : u ≤ shiftedRooftopLimit theta u v :=
    le_of_diagonalPotentialMeasure_lt_eq_zero omega theta hetapsh hu hphi
      hetapos hupos
      (MoreSingularOn.of_le fun x _ => (hetale x).trans (huphi x))
      (MoreSingularOn.of_le fun x _ => huphi x)
      hetamass humass hzero
  exact le_antisymm hetale hge


end

end SGPT.Foundations.Analysis.Pending.ShiftedRooftopContact
