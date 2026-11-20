import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 for a continuous obstacle

`Pending.BigClassEnvelopeContact` proves Xia's Theorem 2.4.4 for a big class
and a *lower semicontinuous* obstacle bounded below, but keeps `P_theta(f) ≤ f`
as a hypothesis: for a merely lower semicontinuous `f` that inequality is
genuinely false (take `f = 1` off one point and `0` at it; a point is
pluripolar, so the envelope ignores it).  For a **continuous real** obstacle it
is true, and this module proves it, which removes the last hypothesis.

The mechanism is Xia's inequality (2.20) in its Lebesgue form, already proved in
`Pending.RooftopEnvelopeAeObstacle.ae_rooftopEnvelope_le_obstacle`: in every
chart `P_theta(f) ≤ f` almost everywhere.  A plurisubharmonic function lying
below an upper semicontinuous one almost everywhere lies below it everywhere
(`PlurisubharmonicOn.le_of_ae_le`), and adding a smooth local potential to a
*continuous real* obstacle keeps it continuous — which is exactly what fails
for a general upper semicontinuous `EReal` obstacle, where the sum with the
potential is not an `EReal` sum one can control.

Continuous obstacles are the base case of Xia's Step 2 (`xia-sgpt:page-0082`):
there he applies Tietze to the small-capacity complements of a bounded
quasi-continuous `f`, obtains continuous `f_k`, and runs the argument on
`h_j = sup_{k >= j} f_k`, which is lower semicontinuous.  So what is proved here
and in `Pending.BigClassEnvelopeContact` is precisely the input of that step.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
open SGPT.Foundations.Analysis.Pending.BigClassSupremumContact
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Almost-everywhere comparison with a continuous real majorant -/

/-- **A `theta`-PSH function below a continuous real function almost everywhere
in every chart is below it everywhere.**  The companion of
`Pending.RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le`
with the `theta`-PSH majorant replaced by a continuous real one: adding the
smooth local potential keeps a continuous real function continuous, hence upper
semicontinuous, which is all `PlurisubharmonicOn.le_of_ae_le` needs. -/
theorem le_coe_of_ae_in_charts_le {theta : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic theta u)
    {F : M → ℝ} (hF : Continuous F)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
        u (e.val.symm z) ≤ ((F (e.val.symm z) : ℝ) : EReal)) :
    ∀ x, u x ≤ ((F x : ℝ) : EReal) := by
  intro x
  let e : ComplexChart n M := complexChartAt x
  have hxsrc : x ∈ e.val.source := mem_chart_source _ x
  have hx : e.val x ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨W, rho, hzW, hrho, hpu⟩ := hu e (e.val x) hx
  have hW : IsOpen W := hrho.1
  have hWt : W ⊆ e.val.target := hrho.2.1
  have hvc : ContinuousOn (fun y => F (e.val.symm y) + rho y) W :=
    (hF.comp_continuousOn (e.val.continuousOn_symm.mono hWt)).add hrho.2.2.1.continuousOn
  have hvusc : UpperSemicontinuousOn
      (fun y => ((F (e.val.symm y) + rho y : ℝ) : EReal)) W := fun y hy =>
    ((continuous_coe_real_ereal.comp_continuousOn hvc) y hy).upperSemicontinuousWithinAt
  have hae' : ∀ᵐ y ∂((volume : Measure (ComplexModel n)).restrict W),
      chartFunction u e y + (rho y : EReal) ≤ ((F (e.val.symm y) + rho y : ℝ) : EReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWt (hae e)] with y hy
    rw [EReal.coe_add]
    exact add_le_add_left hy _
  have hle := hpu.le_of_ae_le hW hvusc volume hae' (e.val x) hzW
  simp only [chartFunction, e.val.left_inv hxsrc] at hle
  rw [EReal.coe_add] at hle
  have hcancel := add_le_add_left hle ((0 - rho (e.val x) : ℝ) : EReal)
  rw [corrected_add_sub, corrected_add_sub, EReal.coe_zero, add_zero, add_zero] at hcancel
  exact hcancel

variable [CompactSpace M] [Nonempty M]

/-! ### The competitor family of a continuous obstacle -/

omit [CompactSpace M] [Nonempty M] in
/-- Every competitor of a continuous obstacle is bounded above by any upper
bound of the obstacle — everywhere, not only quasi-everywhere. -/
theorem rooftopCompetitors_le_const {theta : ClosedRealOneOneForm n M}
    {F : M → ℝ} {B : ℝ} (hB : ∀ x, F x ≤ B)
    {g : M → EReal} (hg : g ∈ rooftopCompetitors theta.val (fun x => (F x : EReal)))
    (x : M) : g x ≤ (B : EReal) := by
  refine le_coe_of_ae_in_charts_le (F := fun _ => B) hg.1.1 continuous_const ?_ x
  intro e
  filter_upwards [hg.2.ae_in_chart e volume] with z hz
  exact hz.trans (EReal.coe_le_coe_iff.mpr (hB _))

omit [CompactSpace M] [Nonempty M] in
/-- The competitors of a continuous obstacle are uniformly bounded above by the
obstacle's maximum. -/
theorem rooftopCompetitors_bddAbove {theta : ClosedRealOneOneForm n M}
    {F : M → ℝ} {B : ℝ} (hB : ∀ x, F x ≤ B) :
    ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta.val (fun x => (F x : EReal)),
      ∀ x, g x ≤ (B : EReal) :=
  ⟨B, fun _ hg y => rooftopCompetitors_le_const hB hg y⟩

/-- **The competitor family of a continuous obstacle in a big class is
nonempty.**  The normalized big-class reference shifted below `min F` is a
competitor. -/
theorem rooftopCompetitors_nonempty_of_isBigClass (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {F : M → ℝ} (hF : Continuous F) :
    (rooftopCompetitors theta.val (fun x => (F x : EReal))).Nonempty := by
  obtain ⟨psi, hpsi, hpsi0, -, -⟩ := exists_normalized_reference_of_isBigClass hn theta hbig
  obtain ⟨xmin, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (univ_nonempty (α := M)) hF.continuousOn
  refine ⟨fun y => psi y + ((F xmin : ℝ) : EReal),
    hpsi.add_const (F xmin), quasiEverywhere_of_forall fun y => ?_⟩
  have h0 : psi y + ((F xmin : ℝ) : EReal) ≤ 0 + ((F xmin : ℝ) : EReal) :=
    add_le_add (hpsi0 y) le_rfl
  rw [zero_add] at h0
  exact h0.trans (EReal.coe_le_coe_iff.mpr (hmin (mem_univ y)))

/-- **The envelope of a continuous obstacle in a big class is a genuine
`theta`-PSH potential.** -/
theorem isThetaPshPotential_rooftopEnvelope_of_continuous (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {F : M → ℝ} (hF : Continuous F) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val fun x => (F x : EReal)) := by
  obtain ⟨xmax, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (univ_nonempty (α := M)) hF.continuousOn
  exact isThetaPshPotential_rooftop_of_nonempty
    (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig hF)
    (rooftopCompetitors_bddAbove (B := F xmax) (fun z => hmax (mem_univ z)))

/-- **Xia's (2.20) for a continuous obstacle, everywhere.**  `P_theta(f) ≤ f`
pointwise, not merely quasi-everywhere, when `f` is a continuous real
function. -/
theorem rooftopEnvelope_le_of_continuous {theta : ClosedRealOneOneForm n M}
    {F : M → ℝ} (hF : Continuous F)
    (hne : (rooftopCompetitors theta.val (fun x => (F x : EReal))).Nonempty)
    (hw : ThetaPlurisubharmonic theta.val
      (rooftopEnvelope theta.val (fun x => (F x : EReal)))) (x : M) :
    rooftopEnvelope theta.val (fun y => (F y : EReal)) x ≤ (F x : EReal) := by
  obtain ⟨xmax, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (univ_nonempty (α := M)) hF.continuousOn
  refine le_coe_of_ae_in_charts_le hw hF ?_ x
  exact ae_rooftopEnvelope_le_obstacle theta hne
    (rooftopCompetitors_bddAbove (B := F xmax) (fun z => hmax (mem_univ z)))

variable [MeasurableSpace M] [BorelSpace M]

/-- **Xia, SGPT, Theorem 2.4.4 for a continuous obstacle and a big class.**  No
hypothesis is left beyond bigness, continuity of the obstacle and the
`theta`-PSH regularity of the envelope itself: the competitor family is
nonempty because the big-class reference shifted below `min F` is a competitor,
`P_theta(f) ≤ f` is the theorem above, and `f` is bounded below by `min F`.

This is the base case of Xia's Step 2 (`xia-sgpt:page-0082`). -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {F : M → ℝ} (hF : Continuous F)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => (F x : EReal)))) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val fun x => (F x : EReal)) hw
      {x | rooftopEnvelope theta.val (fun y => (F y : EReal)) x < (F x : EReal)} = 0 := by
  classical
  obtain ⟨xmin, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (univ_nonempty (α := M)) hF.continuousOn
  have hfb : ∀ y, ((F xmin : ℝ) : EReal) ≤ ((F y : ℝ) : EReal) := fun y =>
    EReal.coe_le_coe_iff.mpr (hmin (mem_univ y))
  exact diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_isBigClass hn theta hbig
    ((continuous_coe_real_ereal.comp hF).lowerSemicontinuous) hfb
    (rooftopEnvelope_le_of_continuous hF
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig hF) hw.1) hw

end

end SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
