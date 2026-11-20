import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
import SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 at the rooftop obstacle `min {phi, psi}`

`Pending.RooftopContactConcentration` reduces Xia's Lemma 3.1.1 (`xia-sgpt:page-0099`,
inequality (3.2)) to one instance of Theorem 2.4.4: the non-pluripolar
Monge--Ampere measure of `P_theta(min {phi, psi})` gives no mass to the set where
the rooftop meets neither obstacle.  This module proves that instance **in
positive dimension**, for arbitrary `theta`-PSH potentials `phi`, `psi` on an
arbitrary pseudo-effective class.

Three reductions and nothing else:

* **Step 1.1** (`xia-sgpt:page-0080`).  `phi` and `psi` are replaced by
  `phi - A`, `psi - A` for one common real `A` bounding both above
  (`FirstPass.IsThetaPshPotential.exists_global_upper_bound` on a compact
  manifold).  The obstacle, the envelope and the non-contact set all translate
  by `-A`, and the measure does not change at all
  (`Pending.DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const`), so
  this is a change of representative and not a restriction.
* **Quasi-continuity.**  The reference truncations of the normalised obstacle are
  `min {phi' \/ (V_theta - C), psi' \/ (V_theta - C)}`, minima of two `theta`-PSH
  potentials bounded wherever `V_theta` is; that is exactly
  `Pending.RooftopTruncatedObstacleConcentration.exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle`.
* **Bigness.**  A class with no Kähler current carries no non-pluripolar mass at
  all (`Pending.NonBigPotentialMass`), so the big case is the only one with
  content.

What is **not** covered is `n = 0`, and that is the only reason the statement
below is not literally
`Pending.RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero`.
Every step of the Section 2.4 chain in this workspace carries `0 < n` — Xia's
Lemma 2.4.1, the nullity of `nK({theta})`, the local balayage lemma and the
existence of the envelope as a genuine potential all do — so `0 < n` is inherited,
not introduced here.  Adding `hn : 0 < n` to the interface would change an
existing statement, which is a human decision.

The `sorryAx` inherited is the big-class reference chain through `IsBigClass`
(Boucksom's Theorem 3.17 via `Pending.KahlerCurrentRegularization`, I-0173);
nothing else is assumed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopMinConcentration

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.NonBigPotentialMass
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
open SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Quasi-continuity of every reference truncation of `min {phi, psi}`.**  The
obstacle hypothesis of `Pending.RooftopTruncationConcentration`, discharged for
the rooftop obstacle of Section 3.1. -/
theorem refTruncationsQuasiContinuous_min {theta : ClosedRealOneOneForm n M}
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hphi0 : ∀ x, phi x ≤ 0) (hpsi0 : ∀ x, psi x ≤ 0) :
    RefTruncationsQuasiContinuous theta (fun x => min (phi x) (psi x)) := by
  intro C hC Omega hOmega hVb K hK hKO eps heps
  exact exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle
    hphi hpsi hV hphi0 hpsi0 hC Omega hOmega hVb K hK hKO heps

/-- Adding a finite real constant to both sides of a strict inequality in
`EReal` is reversible. -/
theorem add_coe_lt_add_coe_iff {a b : EReal} (c : ℝ) :
    a + (c : EReal) < b + (c : EReal) ↔ a < b := by
  refine ⟨fun h => ?_, fun h => EReal.add_lt_add_right_coe h c⟩
  have h' := EReal.add_lt_add_right_coe h (-c)
  rwa [add_coe_add_neg a c, add_coe_add_neg b c] at h'

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) at the
obstacle `min {phi, psi}`, in positive dimension.**  The non-pluripolar
Monge--Ampere measure of the rooftop gives no mass to the set where the rooftop
meets neither obstacle.

This is the statement of
`Pending.RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero`
with `0 < n` added; no normalisation of `phi`, `psi` and no bigness hypothesis. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_of_pos [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw
      {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = 0 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Set.eq_empty_of_isEmpty
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x}]
    exact measure_empty
  by_cases hbig : IsBigClass (RealBottChern.ofRepresentative theta)
  case neg => exact diagonalPotentialMeasure_eq_zero_of_not_isBigClass omega theta hw hbig _
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨_, hphi⟩
  -- the rooftop lies below both obstacles
  have hbelow : rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ phi ∧
      rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) ≤ psi := by
    have hfun : (fun x : M => min (phi x) (psi x + ((0 : ℝ) : EReal))) =
        fun x : M => min (phi x) (psi x) := by
      funext x; simp
    have h := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
    rw [hfun] at h
    exact ⟨h.1, fun x => by simpa using h.2 x⟩
  -- the non-contact set is the strict sublevel set of the obstacle
  have hset : {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
      rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} =
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x)} := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_min (lt_of_le_of_ne (hbelow.1 x) h1) (lt_of_le_of_ne (hbelow.2 x) h2)
    · intro h
      change rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x) at h
      exact ⟨(lt_min_iff.mp h).1.ne, (lt_min_iff.mp h).2.ne⟩
  rw [hset]
  -- Step 1.1: normalise both potentials by one common constant
  obtain ⟨Aphi, hAphi⟩ := hphi.exists_global_upper_bound
  obtain ⟨Apsi, hApsi⟩ := hpsi.exists_global_upper_bound
  have hphiA : ∀ x, phi x ≤ ((max Aphi Apsi : ℝ) : EReal) := fun x =>
    (hAphi x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hpsiA : ∀ x, psi x ≤ ((max Aphi Apsi : ℝ) : EReal) := fun x =>
    (hApsi x).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  set A : ℝ := max Aphi Apsi with hAdef
  have hshift0 : ∀ {v : M → EReal}, (∀ x, v x ≤ (A : EReal)) →
      ∀ x, v x + ((-A : ℝ) : EReal) ≤ 0 := by
    intro v hv x
    calc v x + ((-A : ℝ) : EReal) ≤ (A : EReal) + ((-A : ℝ) : EReal) :=
          add_le_add (hv x) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hphi'pot : IsThetaPshPotential theta.val (fun x => phi x + ((-A : ℝ) : EReal)) :=
    hphi.add_const _
  have hpsi'pot : IsThetaPshPotential theta.val (fun x => psi x + ((-A : ℝ) : EReal)) :=
    hpsi.add_const _
  have hphi'0 : ∀ x, phi x + ((-A : ℝ) : EReal) ≤ 0 := hshift0 hphiA
  have hpsi'0 : ∀ x, psi x + ((-A : ℝ) : EReal) ≤ 0 := hshift0 hpsiA
  -- the shift commutes with the minimum
  have hmin : (fun x : M => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) =
      fun x : M => min (phi x) (psi x) + ((-A : ℝ) : EReal) := by
    funext x
    exact (Monotone.map_min (f := fun t : EReal => t + ((-A : ℝ) : EReal))
      (fun a b h => add_le_add h le_rfl)).symm
  -- the shift commutes with the envelope
  have henv : rooftopEnvelope theta.val
      (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) =
      fun x => rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x +
        ((-A : ℝ) : EReal) := by
    rw [hmin]
    exact rooftopEnvelope_add_const theta.val (fun y => min (phi y) (psi y)) (-A)
  have hwshift : IsThetaPshPotential theta.val
      (fun x => rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x +
        ((-A : ℝ) : EReal)) := hw.add_const _
  have hw' : IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal)))) := by
    rw [henv]; exact hwshift
  -- Theorem 2.4.4 for the normalised obstacle
  have hzero := diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_nonpos hn hbig hV
    (upperSemicontinuous_min hphi'pot.1.quasiPlurisubharmonic.upperSemicontinuous
      hpsi'pot.1.quasiPlurisubharmonic.upperSemicontinuous)
    (fun x => (min_le_left _ _).trans (hphi'0 x))
    (refTruncationsQuasiContinuous_min hphi'pot hpsi'pot hV hphi'0 hpsi'0) hw'
  -- transport the measure back
  have hmeaseq : diagonalPotentialMeasure theta (rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal)))) hw' =
      diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun y => min (phi y) (psi y))) hw := by
    rw [diagonalPotentialMeasure_congr hw' hwshift henv]
    exact diagonalPotentialMeasure_add_const theta hw (-A) hwshift
  -- transport the set back
  have hseteq : {y : M | rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) y <
        min (phi y + ((-A : ℝ) : EReal)) (psi y + ((-A : ℝ) : EReal))} =
      {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x <
        min (phi x) (psi x)} := by
    ext y
    show rooftopEnvelope theta.val
        (fun x => min (phi x + ((-A : ℝ) : EReal)) (psi x + ((-A : ℝ) : EReal))) y <
        min (phi y + ((-A : ℝ) : EReal)) (psi y + ((-A : ℝ) : EReal)) ↔ _
    rw [congrFun henv y, congrFun hmin y]
    exact add_coe_lt_add_coe_iff (-A)
  rw [← hmeaseq, ← hseteq]
  exact hzero

end

end SGPT.Foundations.Analysis.Pending.RooftopMinConcentration
