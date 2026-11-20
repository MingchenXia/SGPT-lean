import SGPT.Foundations.Analysis.Pending.RooftopUscConcentrationPseudoeffective
import SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaCapacityMinQuasiContinuity
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

set_option autoImplicit false

/-!
# Theorem 2.4.4 for the truncated rooftop obstacle

The obstacle of Xia's Lemma 3.1.1 is `min {phi, psi}`, which is `-infinity` on
the poles of either potential and therefore satisfies none of the hypotheses of
Xia's Theorem 2.4.4 in this workspace.  Xia's remedy (`xia-sgpt:page-0080`,
Step 1.2) is to truncate; the truncation that keeps the *capacity sandwich* with
a single constant is against the reference, and this module treats it:

  `f_C := min {phi, psi} \/ (V_theta - C)`,   `C >= 0`.

**Everything Theorem 2.4.4 needs of `f_C` is proved here.**  Upper
semicontinuity, `f_C <= 0`, the relative lower bound `V_theta - C <= f_C`, and —
the point of the module — quasi-continuity of `f_C` against
`Cap_theta(-, V_theta)`.  The last is not an extra hypothesis because of the
lattice identity

  `min {phi, psi} \/ (V_theta - C) = min {phi \/ (V_theta - C), psi \/ (V_theta - C)}`,

whose two arguments are `theta`-PSH potentials squeezed between `V_theta - C`
and `0`, hence bounded on every open set where `V_theta` is bounded: exactly the
input of
`Pending.ThetaCapacityMinQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_min_of_boundedOn`.
So `diagonalPotentialMeasure_rooftopEnvelope_truncated_lt_eq_zero` below carries
**no** bigness hypothesis, **no** quasi-continuity hypothesis and no
nonemptiness hypothesis — only that `P_theta(f_C)` is a genuine potential, which
is what the Section 3.1 consumers assume of their own rooftop.

Also proved: the truncations decrease to the obstacle *after* the envelope,

  `P_theta(min {phi, psi}) = inf_k P_theta(f_k)`

(`rooftopEnvelope_min_eq_iInf_truncated`), through
`Pending.RooftopUscDecreasingLimit`.  The one step of Xia's Step 1.2 that
remains open is therefore the passage of the **measures** `theta^n_{P_theta(f_k)}`
to the limit; its three ingredients are plurifine locality on
`{P_theta(min{phi,psi}) > V_theta - k}`, the vague convergence of
`Pending.BedfordTaylorDecreasingLimit`, and
`Pending.ThetaCapacityIntegralComparison`.  The truncation cannot instead be
moved inside the envelope: `P_theta(f \/ (V_theta - C))` is strictly larger than
`P_theta(f) \/ (V_theta - C)` in general.

The normalization `phi, psi <= 0` is not a restriction on the consumers, only a
choice of representative: `P_theta` and the contact set both commute with adding
a real constant to the obstacle, and a `theta`-PSH potential on a compact
manifold has a real upper bound.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityMinQuasiContinuity
open SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### Upper semicontinuity of a lattice pair -/

omit [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- The maximum of two upper semicontinuous extended-real functions. -/
theorem upperSemicontinuous_max {f g : M → EReal} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun x => max (f x) (g x) := by
  intro x y hy
  rw [max_lt_iff] at hy
  filter_upwards [hf x y hy.1, hg x y hy.2] with z h1 h2
  exact max_lt h1 h2

omit [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- The minimum of two upper semicontinuous extended-real functions. -/
theorem upperSemicontinuous_min {f g : M → EReal} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun x => min (f x) (g x) := by
  intro x y hy
  rcases min_lt_iff.mp hy with h | h
  · filter_upwards [hf x y h] with z hz
    exact lt_of_le_of_lt (min_le_left _ _) hz
  · filter_upwards [hg x y h] with z hz
    exact lt_of_le_of_lt (min_le_right _ _) hz

/-! ### The truncated rooftop obstacle -/

variable {theta : ClosedRealOneOneForm n M} {phi psi : M → EReal}

/-- `min {phi, psi} \/ (V_theta - C)`, Xia's truncation of the rooftop obstacle
against the reference rather than against a constant. -/
def truncatedRooftopObstacle (theta : ClosedRealOneOneForm n M)
    (phi psi : M → EReal) (C : ℝ) : M → EReal :=
  fun x => max (min (phi x) (psi x)) (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **The truncation distributes over the rooftop**: truncating the minimum is
the minimum of the truncations.  This is `sup_inf_right` in the lattice `EReal`,
and it is what makes quasi-continuity of the truncated obstacle a consequence of
quasi-continuity of two `theta`-PSH potentials. -/
theorem truncatedRooftopObstacle_eq_min (C : ℝ) :
    truncatedRooftopObstacle theta phi psi C =
      fun x => min (max (phi x) (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal)))
        (max (psi x) (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal))) := by
  funext x
  exact max_min_distrib_right (phi x) (psi x)
    (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The reference translate is below the truncation, by construction.  This is
the hypothesis `hfc` of
`Pending.RooftopUscConcentrationPseudoeffective`. -/
theorem le_truncatedRooftopObstacle (C : ℝ) (x : M) :
    thetaPshSupremum theta.val x + ((-C : ℝ) : EReal) ≤
      truncatedRooftopObstacle theta phi psi C x := le_max_right _ _

omit [MeasurableSpace M] [BorelSpace M] in
/-- The truncation stays below `0` for a nonnegative truncation level. -/
theorem truncatedRooftopObstacle_le_zero (hphi0 : ∀ x, phi x ≤ 0) {C : ℝ}
    (hC : 0 ≤ C) (x : M) : truncatedRooftopObstacle theta phi psi C x ≤ 0 := by
  refine max_le ((min_le_left _ _).trans (hphi0 x)) ?_
  calc thetaPshSupremum theta.val x + ((-C : ℝ) : EReal)
      ≤ 0 + ((-C : ℝ) : EReal) :=
        add_le_add (by simpa using thetaPshSupremum_le_zero theta.val x) (le_refl _)
    _ = ((-C : ℝ) : EReal) := zero_add _
    _ ≤ 0 := by exact_mod_cast neg_nonpos.mpr hC

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The truncation is upper semicontinuous: `phi`, `psi` and `V_theta` all are,
being `theta`-PSH. -/
theorem upperSemicontinuous_truncatedRooftopObstacle
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) (C : ℝ) :
    UpperSemicontinuous (truncatedRooftopObstacle theta phi psi C) :=
  upperSemicontinuous_max
    (upperSemicontinuous_min hphi.quasiPshPotential.1.upperSemicontinuous
      hpsi.quasiPshPotential.1.upperSemicontinuous)
    (hV.add_const (-C)).quasiPshPotential.1.upperSemicontinuous

/-! ### Quasi-continuity of the truncated obstacle -/

/-- A `theta`-PSH potential truncated against `V_theta - C` from below and `0`
from above is bounded on every open set where `V_theta` is bounded. -/
theorem isBoundedPotentialOn_max_reference
    (hphi0 : ∀ x, phi x ≤ 0) {C : ℝ} (hC : 0 ≤ C) {Omega : Set M}
    (hVb : IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega) :
    IsBoundedPotentialOn
      (fun x => max (phi x) (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal))) Omega :=
  RooftopUscEnvelopeConcentration.isBoundedPotentialOn_of_le_add_const
    (c := -C) (C := 0) hVb (fun x => le_max_right _ _)
    (fun x => by
      rw [EReal.coe_zero]
      exact max_le (hphi0 x)
        (calc thetaPshSupremum theta.val x + ((-C : ℝ) : EReal)
            ≤ 0 + ((-C : ℝ) : EReal) :=
              add_le_add (by simpa using thetaPshSupremum_le_zero theta.val x) (le_refl _)
          _ = ((-C : ℝ) : EReal) := zero_add _
          _ ≤ 0 := by exact_mod_cast neg_nonpos.mpr hC))

/-- **The truncated rooftop obstacle is quasi-continuous for `Cap_theta`.**  In
the exact shape `Pending.RooftopUscConcentrationPseudoeffective` asks for it:
over compact subsets of an open set where `V_theta` is bounded.

The truncation is a minimum of two `theta`-PSH potentials, each bounded there,
so this is Xia's Theorem 2.3.2 applied twice
(`Pending.ThetaCapacityMinQuasiContinuity`). -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hphi0 : ∀ x, phi x ≤ 0) (hpsi0 : ∀ x, psi x ≤ 0) {C : ℝ} (hC : 0 ≤ C)
    (Omega : Set M) (hOmega : IsOpen Omega)
    (hVb : IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega)
    (K : Set M) (hK : IsCompact K) (hKO : K ⊆ Omega) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧
      thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (truncatedRooftopObstacle theta phi psi C y).toReal) (K \ G) := by
  obtain ⟨G, hGopen, hGcap, hGcont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_min_of_boundedOn
      (V := thetaPshSupremum theta.val)
      (IsThetaPshPotential.max hphi (hV.add_const (-C)))
      (IsThetaPshPotential.max hpsi (hV.add_const (-C))) hOmega
      (isBoundedPotentialOn_max_reference hphi0 hC hVb)
      (isBoundedPotentialOn_max_reference hpsi0 hC hVb) hVb hK hKO heps
  refine ⟨G, hGopen, hGcap, ?_⟩
  simpa only [truncatedRooftopObstacle_eq_min (theta := theta) (phi := phi) (psi := psi) C]
    using hGcont

/-! ### Theorem 2.4.4 for the truncated obstacle -/

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) for the
truncated rooftop obstacle `min {phi, psi} \/ (V_theta - C)`.**  Every
hypothesis of Theorem 2.4.4 is discharged here except that `P_theta` of the
truncation is a genuine potential: no bigness, no quasi-continuity, no
nonemptiness, no hypothesis on `V_theta`.

This is the input of Xia's Step 1.2 (`xia-sgpt:page-0080`, equation (2.24)), for
the truncation against the reference rather than against a constant. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_truncated_lt_eq_zero [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hphi0 : ∀ x, phi x ≤ 0) (hpsi0 : ∀ x, psi x ≤ 0) {C : ℝ} (hC : 0 ≤ C)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (truncatedRooftopObstacle theta phi psi C))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (truncatedRooftopObstacle theta phi psi C)) hw
      {x : M | rooftopEnvelope theta.val (truncatedRooftopObstacle theta phi psi C) x <
        truncatedRooftopObstacle theta phi psi C x} = 0 := by
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Set.eq_empty_of_isEmpty
      {x : M | rooftopEnvelope theta.val (truncatedRooftopObstacle theta phi psi C) x <
        truncatedRooftopObstacle theta phi psi C x}]
    exact measure_empty
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hphi.1.hasSmoothLocalPotentials ⟨_, hphi⟩
  exact RooftopUscConcentrationPseudoeffective.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous_of_pseudoeffective
    hn omega theta
    (upperSemicontinuous_truncatedRooftopObstacle hphi hpsi hV C)
    (c := -C) (le_truncatedRooftopObstacle C)
    (truncatedRooftopObstacle_le_zero hphi0 hC)
    (fun Omega hOmega hVb K hK hKO eps heps =>
      exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle
        hphi hpsi hV hphi0 hpsi0 hC Omega hOmega hVb K hK hKO heps)
    hw

/-! ### The truncations decrease to the rooftop obstacle -/

omit [MeasurableSpace M] [BorelSpace M] in
/-- The truncation levels exhaust: `inf_k (min {phi, psi} \/ (V_theta - k))` is
`min {phi, psi}`.  Because `V_theta <= 0`, the family is squeezed between the
obstacle and the constant truncations, whose infimum is the obstacle
(`RooftopUscDecreasingLimit.iInf_max_neg_natCast`). -/
theorem iInf_truncatedRooftopObstacle (x : M) :
    (⨅ k : ℕ, truncatedRooftopObstacle theta phi psi (k : ℝ) x) =
      min (phi x) (psi x) := by
  refine le_antisymm ?_ (le_iInf fun k => le_max_left _ _)
  refine le_of_le_of_eq (iInf_mono fun k => ?_) (iInf_max_neg_natCast (min (phi x) (psi x)))
  refine max_le_max (le_refl _) ?_
  calc thetaPshSupremum theta.val x + ((-(k : ℝ) : ℝ) : EReal)
      ≤ 0 + ((-(k : ℝ) : ℝ) : EReal) :=
        add_le_add (by simpa using thetaPshSupremum_le_zero theta.val x) (le_refl _)
    _ = ((-(k : ℝ) : ℝ) : EReal) := zero_add _

end

end SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
