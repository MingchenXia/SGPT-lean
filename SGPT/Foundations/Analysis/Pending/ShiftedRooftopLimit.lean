import SGPT.Foundations.Analysis.Pending.IncreasingLimitMass
import SGPT.Foundations.Analysis.Pending.MixedMass
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope

set_option autoImplicit false

/-!
# The increasing family of shifted rooftops and its regularized limit

Xia's Proposition 3.1.24 (`xia-sgpt:page-0134`, proof on `xia-sgpt:page-0135`)
studies the increasing family

  `C ↦ (v + C) ∧ u = P_theta (min (u, v + C))`,   `C ∈ ℝ`,

and its regularized supremum `eta = sup*_{C > 0} (v + C) ∧ u`, which the
source calls `P_theta[v](u)`.  This file establishes the order-theoretic and
mass-theoretic facts about that family which do not use any concentration
theorem: the family is nondecreasing, the regularized supremum is again a
`theta`-PSH potential below `u`, and its diagonal non-pluripolar mass is the
common mass of the members.

The mass statement is the only place where the Kähler background enters, via
the mixed-mass monotonicity theorem and the increasing-limit inequality of
`Pending.IncreasingLimitMass` (Xia, Corollary 2.4.1).
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IncreasingLimitMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A genuine global quasi-PSH potential is upper semicontinuous on the
manifold: upper semicontinuity is a chart-local property, and in each chart
the coordinate representative is quasi-PSH. -/
theorem IsGlobalQuasiPshPotential.upperSemicontinuous {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) : UpperSemicontinuous u := by
  intro x y hxy
  set e : ComplexChart n M := complexChartAt x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have husc : UpperSemicontinuousOn (chartFunction u e) e.val.target :=
    (hu.1 e).upperSemicontinuousOn
  have hzval : chartFunction u e (e.val x) = u x := by
    simp only [chartFunction, e.val.left_inv hx]
  have hstep : ∀ᶠ z in 𝓝 (e.val x), chartFunction u e z < y := by
    have hwithin := husc (e.val x) hz y (by simpa only [hzval] using hxy)
    rw [← nhdsWithin_eq_nhds.mpr (e.val.open_target.mem_nhds hz)]
    exact hwithin
  have hcont : ContinuousAt e.val x := e.val.continuousAt hx
  have := hcont.eventually hstep
  filter_upwards [this, e.val.open_source.mem_nhds hx] with w hw hws
  have : chartFunction u e (e.val w) = u w := by
    simp only [chartFunction, e.val.left_inv hws]
  rwa [this] at hw

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Xia's shifted rooftop `(v + C) ∧ u = P_theta (min (u, v + C))`
(`xia-sgpt:page-0099`, the identity `phi ∧ psi = P_theta (min {phi, psi})`). -/
def shiftedRooftop (theta : ClosedRealOneOneForm n M) (u v : M → EReal) (C : ℝ) :
    M → EReal :=
  rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem shiftedRooftop_def (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (C : ℝ) :
    shiftedRooftop theta u v C =
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The shifted rooftop family is nondecreasing in the translation. -/
theorem shiftedRooftop_monotone (theta : ClosedRealOneOneForm n M)
    (u v : M → EReal) : Monotone (shiftedRooftop theta u v) := by
  intro C D hCD
  refine rooftopEnvelope_mono (fun x => ?_)
  exact min_le_min le_rfl
    (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hCD))

/-- The regularized supremum `sup*_{C} (v + C) ∧ u` of the shifted rooftop
family, taken along the integer translations.  Xia writes it
`P_theta[v](u)` (`xia-sgpt:page-0101`, footnote 1). -/
def shiftedRooftopLimit (theta : ClosedRealOneOneForm n M) (u v : M → EReal) :
    M → EReal :=
  uscRegularization (⨆ j : ℕ, shiftedRooftop theta u v (j : ℝ))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem shiftedRooftop_le_shiftedRooftopLimit (theta : ClosedRealOneOneForm n M)
    (u v : M → EReal) (j : ℕ) :
    shiftedRooftop theta u v (j : ℝ) ≤ shiftedRooftopLimit theta u v :=
  (le_iSup (fun k : ℕ => shiftedRooftop theta u v (k : ℝ)) j).trans
    (le_uscRegularization _)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The regularized limit stays below the first obstacle. -/
theorem shiftedRooftopLimit_le (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u) :
    shiftedRooftopLimit theta u v ≤ u :=
  uscRegularization_le
    (IsGlobalQuasiPshPotential.upperSemicontinuous hu.quasiPshPotential)
    (iSup_le fun j => hle (j : ℝ))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The regularized limit of the shifted rooftop family is again a genuine
`theta`-PSH potential, provided every member is one and the first obstacle is
normalized.  This is the manifold instance of Choquet's regularization
theorem, not a new analytic input. -/
theorem isThetaPshPotential_shiftedRooftopLimit
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u) (hu0 : u ≤ 0) :
    IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v) := by
  refine ⟨?_, (hw 0).2.mono ?_⟩
  · refine thetaPlurisubharmonic_uscRegularization_sSup
      (hw 0).1.hasSmoothLocalPotentials ⟨_, Set.mem_range_self 0⟩ ?_ ?_
    · rintro _ ⟨j, rfl⟩
      exact hw (j : ℝ)
    · rintro _ ⟨j, rfl⟩
      exact (hle (j : ℝ)).trans hu0
  · have h0 : shiftedRooftop theta u v ((0 : ℕ) : ℝ) ≤
        shiftedRooftopLimit theta u v :=
      shiftedRooftop_le_shiftedRooftopLimit theta u v 0
    simpa only [Nat.cast_zero] using h0

/-- The regularized limit has the common diagonal non-pluripolar mass of the
family: the increasing-limit inequality of `Pending.IncreasingLimitMass`
(Xia, Corollary 2.4.1) bounds it above, and mixed-mass monotonicity applied to
one member bounds it below. -/
theorem diagonalPotentialMass_shiftedRooftopLimit (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (V : ℝ≥0∞)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u) (hu0 : u ≤ 0)
    (hmass : ∀ j : ℕ, diagonalPotentialMass theta
      (shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) = V) :
    diagonalPotentialMass theta (shiftedRooftopLimit theta u v)
      (isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0) = V := by
  set eta := shiftedRooftopLimit theta u v with heta
  have hetapsh : IsThetaPshPotential theta.val eta :=
    isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0
  have hmono : Monotone (fun j : ℕ => shiftedRooftop theta u v (j : ℝ)) :=
    fun j k hjk => shiftedRooftop_monotone theta u v (by exact_mod_cast hjk)
  refine le_antisymm ?_ ?_
  · have hbound := diagonalPotentialMass_le_iSup_of_monotone
      (theta := theta) (fun j : ℕ => shiftedRooftop theta u v (j : ℝ))
      (fun j => hw (j : ℝ)) hmono hetapsh
    refine hbound.trans ?_
    exact iSup_le fun j => (hmass j).le
  · have hlower : diagonalPotentialMass theta
        (shiftedRooftop theta u v ((0 : ℕ) : ℝ)) (hw ((0 : ℕ) : ℝ)) ≤
        diagonalPotentialMass theta eta hetapsh :=
      MixedMass.globalMixedMass_mono hn omega (fun _ : Fin n => hw ((0 : ℕ) : ℝ))
        (fun _ => hetapsh)
        (fun _ => MoreSingularOn.of_le fun x _ =>
          shiftedRooftop_le_shiftedRooftopLimit theta u v 0 x)
    rw [← hmass 0]
    exact hlower

end

end SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit
