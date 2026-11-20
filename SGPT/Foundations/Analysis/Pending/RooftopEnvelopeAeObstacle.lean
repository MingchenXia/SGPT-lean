import SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# The rooftop envelope lies below its obstacle almost everywhere

Xia, SGPT, inequality (2.20) (`xia-sgpt:page-0078`) states `P_theta(f) <= f`
*quasi*-everywhere.  The quasi-everywhere form rests on the Bedford--Taylor
negligibility theorem, which this workspace does not have.  What it does have
is the Lebesgue form of the same statement, and that is what this file proves:

  in every holomorphic chart, `rooftopEnvelope theta f <= f`
  Lebesgue-almost everywhere.

No new analytic input is used.  Three proved pieces are assembled.

* Choquet's lemma (`Pending.ChoquetRegularization`) replaces the competitor
  family by a *sequence* with the same regularized supremum.  Countability is
  the whole point: each competitor lies below the obstacle only off its own
  pluripolar set, and a pluripolar set is Haar-null in every chart, so only a
  countable family may be compared with the obstacle simultaneously.
* The running maxima of that sequence (`Pending.runningMax`, which lives with
  Choquet's lemma because every consumer of that lemma needs them) are an
  increasing sequence of genuine `theta`-PSH potentials with the same
  pointwise supremum.
* For increasing families the chart transfer is already proved:
  `Pending.IncreasingThetaPshChartL1.ae_chartFunction_iSup_eq` identifies the
  *unregularized* supremum with the chart representative of the regularized
  one, Lebesgue-almost everywhere.  It is stated for normalized families, and
  is upgraded here to a family with an arbitrary finite uniform upper bound by
  a constant shift.

The companion theorem `ThetaPlurisubharmonic.le_of_ae_in_charts_le` upgrades a
chartwise almost-everywhere comparison of two `theta`-PSH functions to a
pointwise one.  It is the exact analogue of
`FirstPass.ThetaPlurisubharmonic.le_of_quasiEverywhere_le`, and is strictly
stronger, since a pluripolar set is Haar-null; the existing proof already
factors through `PlurisubharmonicOn.le_of_ae_le` and nothing else is needed.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem isThetaPshPotential_runningMax {theta : SmoothRealForm n M 2}
    {s : ℕ → M → EReal} (hs : ∀ k, IsThetaPshPotential theta (s k)) (k : ℕ) :
    IsThetaPshPotential theta (runningMax s k) := by
  induction k with
  | zero => exact hs 0
  | succ m ih => exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max ih (hs (m + 1))

/-- The chart identification of the unregularized supremum with the regularized
one, for an increasing family with an arbitrary finite uniform upper bound.
The normalized case is `IncreasingThetaPshChartL1.ae_chartFunction_iSup_eq`; the
shift by `-B` is the only step. -/
theorem ae_chartFunction_iSup_eq_of_le_const {theta : ClosedRealOneOneForm n M}
    {g : ℕ → M → EReal} {u : M → EReal} {B : ℝ}
    (hg : ∀ j, IsThetaPshPotential theta.val (g j))
    (hgB : ∀ j, ∀ x, g j x ≤ (B : EReal)) (hmono : Monotone g)
    (heq : uscRegularization (⨆ j, g j) = u)
    (e : ComplexChart n M) :
    ∀ᵐ z ∂(volume.restrict e.val.target),
      (⨆ j, chartFunction (g j) e z) = chartFunction u e z := by
  set g' : ℕ → M → EReal := fun j x => g j x + ((-B : ℝ) : EReal) with hg'def
  set u' : M → EReal := fun x => u x + ((-B : ℝ) : EReal) with hu'def
  have hzero : ((B : EReal) + ((-B : ℝ) : EReal)) = 0 := by
    rw [← EReal.coe_add]
    norm_num
  have hg'psh : ∀ j, IsThetaPshPotential theta.val (g' j) :=
    fun j => (hg j).add_const (-B)
  have hg'0 : ∀ j, g' j ≤ 0 := by
    intro j x
    calc g' j x ≤ (B : EReal) + ((-B : ℝ) : EReal) :=
          add_le_add (hgB j x) le_rfl
      _ = 0 := hzero
  have hg'mono : Monotone g' := by
    intro j k hjk x
    exact add_le_add (hmono hjk x) le_rfl
  have hsupfun : (⨆ j, g' j) = fun x => (⨆ j, g j x) + ((-B : ℝ) : EReal) := by
    funext x
    simp only [iSup_apply, hg'def]
    exact iSup_add_coe (fun j => g j x) (-B)
  have heq' : uscRegularization (⨆ j, g' j) = u' := by
    rw [hsupfun, uscRegularization_add_coe_const]
    funext x
    have : uscRegularization (fun y => ⨆ j, g j y) x = u x := by
      have hfun : (fun y => ⨆ j, g j y) = (⨆ j, g j) := by
        funext y; simp [iSup_apply]
      rw [hfun, heq]
    rw [this]
  have hae := ae_chartFunction_iSup_eq hg'psh hg'0 hg'mono heq' e
  filter_upwards [hae] with z hz
  have h1 : (⨆ j, chartFunction (g' j) e z) =
      (⨆ j, chartFunction (g j) e z) + ((-B : ℝ) : EReal) :=
    iSup_add_coe (fun j => chartFunction (g j) e z) (-B)
  have h2 : chartFunction u' e z = chartFunction u e z + ((-B : ℝ) : EReal) := rfl
  rw [h1, h2] at hz
  exact eReal_add_coe_right_cancel hz

/-- **The Lebesgue form of Xia's (2.20).**  In every holomorphic chart, the
rooftop envelope of an obstacle whose competitor family is nonempty and
uniformly bounded above lies below that obstacle almost everywhere. -/
theorem ae_rooftopEnvelope_le_obstacle (theta : ClosedRealOneOneForm n M)
    {f : M → EReal}
    (hne : (rooftopCompetitors theta.val f).Nonempty)
    (hbound : ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta.val f, ∀ x, g x ≤ (B : EReal))
    (e : ComplexChart n M) :
    ∀ᵐ z ∂(volume.restrict e.val.target),
      rooftopEnvelope theta.val f (e.val.symm z) ≤ f (e.val.symm z) := by
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨s, hsF, hs⟩ := exists_seq_uscRegularization_iSup_eq hne
  set g : ℕ → M → EReal := runningMax s with hgdef
  have hgpsh : ∀ j, IsThetaPshPotential theta.val (g j) :=
    fun j => isThetaPshPotential_runningMax (fun k => (hsF k).1) j
  have hgB : ∀ j, ∀ x, g j x ≤ (B : EReal) :=
    fun j x => runningMax_apply_le (fun k => hB (s k) (hsF k) x) j
  have hmono : Monotone g := runningMax_monotone s
  have hsupfun : (⨆ j, g j) = (⨆ k, s k) := by
    funext x
    simp only [iSup_apply]
    exact iSup_runningMax s x
  have heq : uscRegularization (⨆ j, g j) = rooftopEnvelope theta.val f := by
    rw [hsupfun, hs]
    rfl
  have hae1 := ae_chartFunction_iSup_eq_of_le_const hgpsh hgB hmono heq e
  have hae2 : ∀ᵐ z ∂(volume.restrict e.val.target),
      ∀ k, s k (e.val.symm z) ≤ f (e.val.symm z) := by
    rw [ae_all_iff]
    intro k
    exact (hsF k).2.ae_in_chart e volume
  filter_upwards [hae1, hae2] with z h1 h2
  have h3 : (⨆ k, s k (e.val.symm z)) ≤ f (e.val.symm z) := iSup_le h2
  have h4 : (⨆ j, chartFunction (g j) e z) = ⨆ k, s k (e.val.symm z) :=
    iSup_runningMax s (e.val.symm z)
  have h5 : chartFunction (rooftopEnvelope theta.val f) e z =
      rooftopEnvelope theta.val f (e.val.symm z) := rfl
  rw [h4] at h1
  rw [← h5, ← h1]
  exact h3

/-- **Chartwise almost-everywhere comparison of `theta`-PSH functions is
pointwise.**  This is the exact analogue of
`FirstPass.ThetaPlurisubharmonic.le_of_quasiEverywhere_le`, with the
quasi-everywhere hypothesis weakened to Lebesgue-almost everywhere in every
chart.  It is strictly stronger, since a pluripolar set is Haar-null in every
chart, and no extra input is needed: the existing proof already factors
through `PlurisubharmonicOn.le_of_ae_le`, which only ever sees the chart
measure. -/
theorem ThetaPlurisubharmonic.le_of_ae_in_charts_le {theta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic theta u)
    (hv : ThetaPlurisubharmonic theta v)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
        u (e.val.symm z) ≤ v (e.val.symm z)) :
    u ≤ v := by
  intro x
  let e : ComplexChart n M := complexChartAt x
  have hx : e.val x ∈ e.val.target := e.val.map_source (mem_chart_source _ x)
  obtain ⟨W₁, rho, hzW₁, hrho, hpu⟩ := hu e (e.val x) hx
  obtain ⟨W₂, sigma, hzW₂, hsigma, hpv⟩ := hv e (e.val x) hx
  let V := W₁ ∩ W₂
  have hV : IsOpen V := hrho.1.inter hsigma.1
  have hrhoV := hrho.mono hV inter_subset_left
  have hsigmaV := hsigma.mono hV inter_subset_right
  have hpuV : PlurisubharmonicOn
      (fun y => chartFunction u e y + (sigma y : EReal)) V :=
    (smoothLocalPotential_psh_iff theta e V rho sigma hrhoV hsigmaV
      (chartFunction u e)).1 (hpu.mono inter_subset_left)
  have hpvV := hpv.mono (inter_subset_right (s := W₁))
  have haeV : ∀ᵐ y ∂((volume : Measure (ComplexModel n)).restrict V),
      chartFunction u e y + (sigma y : EReal) ≤
        chartFunction v e y + (sigma y : EReal) := by
    have hVt : V ⊆ e.val.target := inter_subset_left.trans hrho.2.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVt (hae e)] with y hy
    exact add_le_add_left hy _
  have hle := hpuV.le_of_ae_le hV hpvV.upperSemicontinuousOn volume haeV
    (e.val x) ⟨hzW₁, hzW₂⟩
  have hcancel := add_le_add_left hle (((0 - sigma (e.val x) : ℝ)) : EReal)
  rw [corrected_add_sub, corrected_add_sub, EReal.coe_zero, add_zero,
    add_zero] at hcancel
  simpa [chartFunction, e, e.val.left_inv (mem_chart_source _ x)] using hcancel

end

end SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
