import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel
import SGPT.Foundations.Analysis.FirstPass.PotentialL1
import SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-!
# The `C → ∞` endpoint of Xia's rooftop mass diamond

`Pending.RooftopMassDiamondModel` proves Xia's Theorem 3.1.3 for every finite
truncation level `C`.  The source concludes its Step 2 by applying Corollary
2.4.2 to the nonpositive truncation rooftops.  This module records that exact
analytic input, and proves the remaining order-theoretic passage to the
untruncated rooftop.

For model potentials `phi`, `psi`, write `gamma = phi \/ psi` and

`w_j = P_theta(min {phi \/ (gamma - (j+1)), psi \/ (gamma - (j+1))})`.

The analytic input is Corollary 2.4.2: if a decreasing sequence of
nonpositive theta-PSH potentials converges in `L¹` to `w`, then the limsup of
its contact masses is bounded by the contact mass of `w`.  We state it with
`ManifoldL1LocallyTendsto`; on a compact manifold this is the chart-local form
of the source's `L¹` hypothesis, and the finite-atlas comparison has not yet
been formalized separately.  It was a named interface until run 0097; it is now
proved in `Pending.DecreasingContactMassLimit`.

Everything after that input is pure `ENNReal` limit bookkeeping plus the
finite-level theorem already proved in `RooftopMassDiamondModel`.  Thus a later
proof that the displayed truncation rooftops converge to
`P_theta(min {phi, psi})` in chart-local `L¹` can invoke
`model_mass_diamond_of_truncation_limit` directly.

Source: Xia, *Singularities in Global Pluripotential Theory*, Corollary 2.4.2
(`xia-sgpt:page-0077`--`xia-sgpt:page-0078`) and the last sentence of the proof
of Theorem 3.1.3 (`xia-sgpt:page-0109`).
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The mass which a potential's diagonal non-pluripolar measure gives to its
zero-contact locus. -/
def contactMass (theta : ClosedRealOneOneForm n M) (u : M → EReal)
    (hu : IsThetaPshPotential theta.val u) : ℝ≥0∞ :=
  diagonalPotentialMeasure theta u hu {x | u x = 0}

/-- Along a pointwise decreasing family of nonpositive potentials, the mass of
the zero-contact set is antitone.  This is the contact comparison of Xia's
Lemma 2.4.2, already proved in `MaxMassDecomposition`: if `u k ≤ u j`, then a
zero of `u k` is also a zero of `u j`, and the comparison applies there. -/
theorem contactMass_antitone_of_antitone
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (hanti : Antitone u) :
    Antitone (fun j => contactMass theta (u j) (hu j)) := by
  intro j k hjk
  set E : Set M := {x | u k x = 0} with hEdef
  set F : Set M := {x | u j x = 0} with hFdef
  have hEmeas : MeasurableSet E := by
    rw [hEdef]
    exact measurableSet_eq_fun
      (hu k).1.quasiPlurisubharmonic.upperSemicontinuous.measurable measurable_const
  have hcontact : E ∩ {x | u k x = u j x} = E := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, le_antisymm (hanti hjk x) ?_⟩
      rw [hEdef] at hx
      rw [hx]
      exact hu0 j x
  have hsub : E ⊆ F := by
    intro x hx
    rw [hEdef] at hx
    rw [hFdef]
    apply le_antisymm (hu0 j x)
    rw [← hx]
    exact hanti hjk x
  have hle := SGPT.Foundations.Analysis.Pending.MaxMassDecomposition.contact_measure_le
    omega (hu k) (hu j) (hanti hjk) hEmeas
  change diagonalPotentialMeasure theta (u k) (hu k) E ≤
    diagonalPotentialMeasure theta (u j) (hu j) F
  calc
    diagonalPotentialMeasure theta (u k) (hu k) E =
        diagonalPotentialMeasure theta (u k) (hu k)
          (E ∩ {x | u k x = u j x}) := by rw [hcontact]
    _ ≤ diagonalPotentialMeasure theta (u j) (hu j)
          (E ∩ {x | u k x = u j x}) := hle
    _ = diagonalPotentialMeasure theta (u j) (hu j) E := by rw [hcontact]
    _ ≤ diagonalPotentialMeasure theta (u j) (hu j) F := measure_mono hsub

/-- **Xia, Corollary 2.4.2 (`xia-sgpt:page-0077`--`page-0078`), in the
antitone sequence form used by Theorem 3.1.3.**  Contact mass is upper
semicontinuous under `L¹` convergence of nonpositive decreasing theta-PSH
potentials.  Xia proves the stronger statement for arbitrary nets; the
endpoint below only consumes this special case.

The source proves it first for sequences and then reduces nets to sequences;
the present endpoint only needs the displayed sequence case.  It is proved in
`Pending.DecreasingContactMassLimit` (run 0097): the `L¹` limit of the
decreasing sequence is its pointwise limit, and the decreasing semicontinuity
theorem (Xia, Theorem 2.4.2, `Pending.DecreasingLimitOpenMeasure`) applies to
the truncations `max (u_j, u_0 - 1)`, which have equal masses. -/
theorem contactMass_limsup_le_of_manifoldL1LocallyTendsto
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (v : M → EReal)
    (hv : IsThetaPshPotential theta.val v)
    (hanti : Antitone u)
    (hL1 : ManifoldL1LocallyTendsto (n := n) u atTop v) :
    limsup (fun j => contactMass theta (u j) (hu j)) atTop ≤
      contactMass theta v hv := by
  exact DecreasingContactMassLimit.contactMeasure_limsup_le_of_manifoldL1LocallyTendsto
    omega theta u hu hu0 v hv hanti hL1

/-- A basic endpoint rule for `ENNReal`: a uniform family of inequalities with
right side `b + c_j` passes to `b + limsup c_j`. -/
theorem le_add_of_forall_le_add_of_limsup_le
    {a b d : ℝ≥0∞} {c : ℕ → ℝ≥0∞}
    (hstage : ∀ j, a ≤ b + c j) (hlim : limsup c atTop ≤ d) :
    a ≤ b + d := by
  by_cases hab : a ≤ b
  · exact hab.trans (le_add_of_nonneg_right bot_le)
  have hba : b ≤ a := le_of_not_ge hab
  have hsub : a - b ≤ limsup c atTop := by
    refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall ?_)
    intro j
    rw [tsub_le_iff_right]
    simpa [add_comm] using hstage j
  calc
    a = b + (a - b) := (add_tsub_cancel_of_le hba).symm
    _ ≤ b + limsup c atTop := add_le_add le_rfl hsub
    _ ≤ b + d := add_le_add le_rfl hlim

/-- The integer truncations in Step 2 of Xia's proof.  The shift by one keeps
all levels strictly positive, exactly as required by the finite-level theorem. -/
def modelTruncationRooftop (theta : ClosedRealOneOneForm n M)
    (phi psi : M → EReal) (j : ℕ) : M → EReal :=
  truncRooftop theta.val (fun x => max (phi x) (psi x)) phi psi ((j : ℝ) + 1)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Truncating at a larger level lowers both obstacles, hence lowers their
rooftop envelope. -/
theorem modelTruncationRooftop_antitone
    (theta : ClosedRealOneOneForm n M) (phi psi : M → EReal) :
    Antitone (modelTruncationRooftop theta phi psi) := by
  intro j k hjk x
  change rooftopEnvelope theta.val
      (fun y => min (truncAt (fun z => max (phi z) (psi z)) ((k : ℝ) + 1) phi y)
        (truncAt (fun z => max (phi z) (psi z)) ((k : ℝ) + 1) psi y)) x ≤
    rooftopEnvelope theta.val
      (fun y => min (truncAt (fun z => max (phi z) (psi z)) ((j : ℝ) + 1) phi y)
        (truncAt (fun z => max (phi z) (psi z)) ((j : ℝ) + 1) psi y)) x
  apply rooftopEnvelope_mono
  intro y
  refine min_le_min ?_ ?_
  · exact max_le_max le_rfl
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
        simpa only [neg_add_rev, neg_le_neg_iff, add_comm] using
          neg_le_neg (add_le_add_right (Nat.cast_le.mpr hjk) (1 : ℝ)))))
  · exact max_le_max le_rfl
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
        simpa only [neg_add_rev, neg_le_neg_iff, add_comm] using
          neg_le_neg (add_le_add_right (Nat.cast_le.mpr hjk) (1 : ℝ)))))

/-- **The `C → ∞` completion of Xia's model-potential Step 2.**

The finite-level estimate is supplied by
`mass_add_mass_le_mass_max_add_contact_of_model`; Corollary 2.4.2 controls its
contact term in the limit.  The hypotheses `htrunc` and `htrunc0` are exactly
what the finite-level construction provides, while `hL1` is the still-open
convergence bridge from the truncation rooftops to the ordinary rooftop.

No reduction from arbitrary potentials to model potentials is asserted here:
that is Xia's Step 1 and needs Proposition 3.1.3 and Lemma 3.1.2. -/
theorem model_mass_diamond_of_truncation_limit
    [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (htrunc : ∀ j, IsThetaPshPotential theta.val
      (modelTruncationRooftop theta phi psi j))
    (htrunc0 : ∀ j x, modelTruncationRooftop theta phi psi j x ≤ 0)
    (hL1 : ManifoldL1LocallyTendsto (n := n)
      (modelTruncationRooftop theta phi psi) atTop
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  have hcontact := contactMass_limsup_le_of_manifoldL1LocallyTendsto
    omega theta (modelTruncationRooftop theta phi psi) htrunc htrunc0
    (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof
    (modelTruncationRooftop_antitone theta phi psi) hL1
  have hstage : ∀ j,
      diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi ≤
        diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax +
          contactMass theta (modelTruncationRooftop theta phi psi j) (htrunc j) := by
    intro j
    simpa only [modelTruncationRooftop, contactMass] using
      (mass_add_mass_le_mass_max_add_contact_of_model (theta := theta) omega
        hphi hpsi hphimodel hpsimodel hmax
        (show 0 < (j : ℝ) + 1 by positivity) (htrunc j))
  have hendpoint := le_add_of_forall_le_add_of_limsup_le hstage hcontact
  refine hendpoint.trans (add_le_add le_rfl ?_)
  change diagonalPotentialMeasure theta
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof
      {x | rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) x = 0} ≤
    diagonalPotentialMeasure theta
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof univ
  exact measure_mono (subset_univ _)

end

end SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit
