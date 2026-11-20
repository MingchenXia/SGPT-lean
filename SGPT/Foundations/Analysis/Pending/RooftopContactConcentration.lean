import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.RooftopMinConcentration
import SGPT.Foundations.Analysis.Pending.RooftopDimZero
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# Xia's Lemma 3.1.1 from the contact concentration of the rooftop measure

Xia, SGPT, Lemma 3.1.1 (`xia-sgpt:page-0099`, inequality (3.2)) states, for
`phi, psi` in `PSH(X, theta)` whose rooftop `w = phi ∧ psi = P_theta(min)` is
again a genuine potential,

  `theta^n_w <= 1_{w = phi} theta^n_phi + 1_{w = psi} theta^n_psi`.

Its proof in the source combines exactly two facts:

1. **Lemma 2.4.2** (`xia-sgpt:page-0076`), in its contact form: for `w <= phi`,
   `1_{w = phi} theta^n_w <= 1_{w = phi} theta^n_phi`.  This is now **proved**
   in `Pending.MaxMassDecomposition.contact_measure_le`.
2. **Theorem 2.4.4** (`xia-sgpt:page-0079`, equation (2.23)): the Monge--Ampere
   measure of `P_theta(f)` is carried by the contact set `{P_theta(f) = f}`.
   Its proof (`xia-sgpt:page-0080`--`xia-sgpt:page-0082`) runs the balayage
   lemma 2.4.3 over a plurifine-open set, enlarges it to an ordinary open set
   of small Bedford--Taylor capacity (Example 2.3.1), and concludes by
   convergence in capacity (Theorem 2.3.3) and quasi-continuity (Theorem
   2.3.2) with Tietze extensions.  This is now **proved** at `f = min {phi, psi}`,
   in two halves glued by the dimension:

   * `0 < n`: `Pending.RooftopMinConcentration`, which carries out Xia's Step
     1.1 (normalisation by one common constant) and Step 1.2 (the limit along
     the reference truncations `min {phi \/ (V_theta - C), psi \/ (V_theta - C)}`)
     on an arbitrary pseudo-effective class;
   * `n = 0`: `Pending.RooftopDimZero`, where the model is a point, `min {phi,
     psi}` is itself a potential, the rooftop equals the obstacle and the
     non-contact set is empty.

   Neither half assumes bigness, nonemptiness or positivity of the dimension in
   its consumer-facing form, so the statement below is unchanged from the one
   that recorded it as an interface.

The reduction is not formal.  It is true that, read on the complement of the
two contact sets, (3.2) *implies* the concentration statement; but the converse
needs (1).  Both are now proved, so the whole of (3.2) is a theorem.

No measurability of `B` is assumed: the passage from a measurable test set to
an arbitrary one uses only the measurable hull `toMeasurable`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopContactConcentration

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The rooftop of two potentials lies below both of them.  This is the
`C = 0` case of `FirstPass.rooftopEnvelope_min_add_const_le_obstacles`, with
the trailing `+ 0` removed. -/
theorem rooftopEnvelope_min_le_obstacles {theta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic theta u)
    (hv : ThetaPlurisubharmonic theta v) :
    rooftopEnvelope theta (fun x => min (u x) (v x)) ≤ u ∧
      rooftopEnvelope theta (fun x => min (u x) (v x)) ≤ v := by
  have hfun : (fun x : M => min (u x) (v x + ((0 : ℝ) : EReal))) =
      fun x : M => min (u x) (v x) := by
    funext x
    simp
  have h := rooftopEnvelope_min_add_const_le_obstacles hu hv 0
  rw [hfun] at h
  refine ⟨h.1, fun x => ?_⟩
  simpa using h.2 x

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)),
specialised to `f = min {phi, psi}`.**  The non-pluripolar Monge--Ampere measure
of the rooftop gives no mass to the set where the rooftop meets neither
obstacle.

Proved by the dimension dichotomy: `Pending.RooftopMinConcentration` in positive
dimension (Xia's Steps 1.1 and 1.2 over an arbitrary pseudo-effective class) and
`Pending.RooftopDimZero` in dimension `0` (where the non-contact set is empty).
The statement is the one this module recorded as an interface, with
`[ConnectedSpace M]` added (human decision I-0902 on I-0825: the non-big branch
rests on Boucksom's volume criterion, a statement about connected compact
Kähler manifolds; on a disconnected `M` it would be needed componentwise). -/
theorem diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw
      {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact RooftopDimZero.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_of_dim_zero
      hn theta hphi hpsi hw
  · exact RooftopMinConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_of_pos
      hn omega theta hphi hpsi hw

/-- The contact comparison of Lemma 2.4.2, applied on an arbitrary (possibly
non-measurable) subset of a contact set. -/
theorem measure_le_of_subset_contact (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {w p : M → EReal}
    (hw : IsThetaPshPotential theta.val w) (hp : IsThetaPshPotential theta.val p)
    (hwp : w ≤ p) (S : Set M) (hS : S ⊆ {x : M | w x = p x}) :
    diagonalPotentialMeasure theta w hw S ≤ diagonalPotentialMeasure theta p hp S := by
  set nu := diagonalPotentialMeasure theta p hp with hnu
  calc diagonalPotentialMeasure theta w hw S
      ≤ diagonalPotentialMeasure theta w hw
          (toMeasurable nu S ∩ {x : M | w x = p x}) :=
        measure_mono fun x hx => ⟨subset_toMeasurable nu S hx, hS hx⟩
    _ ≤ nu (toMeasurable nu S ∩ {x : M | w x = p x}) :=
        contact_measure_le omega hw hp hwp (measurableSet_toMeasurable nu S)
    _ ≤ nu (toMeasurable nu S) := measure_mono inter_subset_left
    _ = nu S := measure_toMeasurable S

/-- **Xia, SGPT, Lemma 3.1.1, inequality (3.2)**, proved from the concentration
interface above and the now-available contact comparison.  The statement is
exactly the one recorded in `Pending.RooftopMassDecomposition`. -/
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
            = psi x}) := by
  classical
  set w := rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) with hwdef
  obtain ⟨hwphi, hwpsi⟩ := rooftopEnvelope_min_le_obstacles hphi.1 hpsi.1
  have hzero := diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero
    omega theta hphi hpsi hw
  have hsub : B ⊆ (B ∩ {x : M | w x = phi x}) ∪
      ((B ∩ {x : M | w x = psi x}) ∪ {x : M | w x ≠ phi x ∧ w x ≠ psi x}) := by
    intro x hx
    by_cases h1 : w x = phi x
    · exact Or.inl ⟨hx, h1⟩
    · by_cases h2 : w x = psi x
      · exact Or.inr (Or.inl ⟨hx, h2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  calc diagonalPotentialMeasure theta w hw B
      ≤ diagonalPotentialMeasure theta w hw ((B ∩ {x : M | w x = phi x}) ∪
          ((B ∩ {x : M | w x = psi x}) ∪
            {x : M | w x ≠ phi x ∧ w x ≠ psi x})) := measure_mono hsub
    _ ≤ diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta w hw ((B ∩ {x : M | w x = psi x}) ∪
            {x : M | w x ≠ phi x ∧ w x ≠ psi x}) := measure_union_le _ _
    _ ≤ diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          (diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = psi x}) +
            diagonalPotentialMeasure theta w hw
              {x : M | w x ≠ phi x ∧ w x ≠ psi x}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ = diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta w hw (B ∩ {x : M | w x = psi x}) := by
        rw [hzero, add_zero]
    _ ≤ diagonalPotentialMeasure theta phi hphi (B ∩ {x : M | w x = phi x}) +
          diagonalPotentialMeasure theta psi hpsi (B ∩ {x : M | w x = psi x}) :=
        add_le_add
          (measure_le_of_subset_contact omega theta hw hphi hwphi _
            fun x hx => hx.2)
          (measure_le_of_subset_contact omega theta hw hpsi hwpsi _
            fun x hx => hx.2)

end

end SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
