import SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
import SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Xia's Step 1.2: Theorem 2.4.4 for an unbounded upper semicontinuous obstacle

`Pending.RooftopUscEnvelopeConcentration` proves Xia's Theorem 2.4.4
(`xia-sgpt:page-0079`, equation (2.23)) for an obstacle bounded below *relative
to the reference*, `V_theta + c <= f`.  Xia's Step 1.2
(`xia-sgpt:page-0080`--`page-0081`) removes that hypothesis by passing to the
limit along truncations of the obstacle.  This module carries out that passage,
along the truncations **against the reference**, `f_k = f \/ (V_theta - k)`,
rather than Xia's constant ones `f \/ (-k)`: a constant is not a `theta`-PSH
potential unless `theta` is semipositive, so quasi-continuity of `f \/ (-k)` is
not available for the Section 3.1 obstacles, whereas quasi-continuity of
`f \/ (V_theta - k)` is.  Since `V_theta <= 0`, the two families are interleaved
and have the same infimum, so nothing is lost.

The route here is not Xia's.  He integrates `1 - e^{P(f_k) - f_k}` against
`theta^n_{P(f_k) \/ (V_theta - C)}` and lets `k -> infinity` using convergence in
capacity of the *integrand*.  The argument below never forms an integral: it
works with the sets directly, and the only convergence used is convergence in
capacity of the *potentials*, which the workspace already has
(`Pending.ThetaCapacityLocalDecreasingConvergence`).  The two ingredients that
replace the integral are

* plurifine locality in its diagonal form
  (`Pending.MaxMassDecomposition.measure_inter_lt_left`), which identifies
  `theta^n_{P(f_k) \/ (V_theta - C)}` with `theta^n_{P(f_k)}` on
  `{V_theta - C < P(f_k)}`, and
* the open-set portmanteau along a decreasing family
  (`Pending.DiagonalMeasureDecreasingPortmanteau`).

The elementary inclusion that makes it work is this.  Write `w = P_theta(f)`,
`p_k = P_theta(f_k)`, `u_k = p_k \/ (V_theta - C)` and `u = w \/ (V_theta - C)`,
with `C` a truncation level of its own, independent of `k`.
On `U_C = {V_theta - C < w}` one has `u = w`, and for every `k`

  `{w + delta < f} ∩ U_C ⊆ {p_k < f} ∪ {u + delta <= u_k}`,

because `p_k <= u_k` and `u = w` there.  The first set is `theta^n_{u_k}`-null
by locality and the bounded theorem; the second has capacity tending to `0`
because `u_k` decreases to `u` with all of them trapped between `V_theta - C`
and `0`.  So the measures `theta^n_{u_k}` of a small open neighbourhood of
`{w + delta < f} ∩ U_C` are eventually as small as one likes, and the
portmanteau transfers that to `theta^n_u`, hence — by locality again — to
`theta^n_w`.

The truncation level `C` is then let go to infinity, which is a countable
monotone union because `⋃_C {V_theta - C < w} = {w > -infinity}` and the poles
of `w` are pluripolar; and `delta` is let go to `0` along `1/(m+1)`, exactly as
in the bounded theorem.

The obstacle hypothesis that survives is quasi-continuity of every reference
truncation `f \/ (V_theta - C)`, packaged as `RefTruncationsQuasiContinuous`.
It is Xia's own hypothesis on `f`, and it is what the Section 3.1 obstacles
satisfy: for `f = min {phi, psi}` the truncation is
`min {phi \/ (V_theta - C), psi \/ (V_theta - C)}`, a minimum of two `theta`-PSH
potentials bounded wherever `V_theta` is, so
`Pending.RooftopTruncatedObstacleConcentration.exists_isOpen_thetaCapacity_lt_continuousOn_truncatedRooftopObstacle`
supplies it.

Everything here inherits the `sorryAx` of the big-class reference chain
(Boucksom's Theorem 3.17 through `Pending.KahlerCurrentRegularization`, I-0173)
through `IsBigClass`; nothing else is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureDecreasingPortmanteau
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
open SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### The local estimate -/

section Core

variable [Nonempty M] {theta : ClosedRealOneOneForm n M} {f w : M → EReal}
  {p : ℕ → M → EReal}

/-- **The heart of Xia's Step 1.2** (`xia-sgpt:page-0080`--`page-0081`).

`p k` is a decreasing family of `theta`-PSH potentials above `w`, with `p k`
giving no mass to `{p k < f}` — the truncated instances of Theorem 2.4.4 — and
`C >= 1`, `delta > 0`.  Then, near every point off `nK({theta})`,
`theta^n_w` gives no mass to

  `{w + delta < f} ∩ {V_theta - C < w}`.

The proof runs on the maxima `u k = p k \/ (V_theta - C)`, which are trapped
between `V_theta - C` and `0`: they agree with `p k` on `{V_theta - C < p k}` by
plurifine locality, they decrease to `u = w \/ (V_theta - C)`, and their measures
are dominated by `C^n Cap_theta` uniformly in `k`.  The target set is enlarged to
an open set by quasi-continuity, the portmanteau of
`Pending.DiagonalMeasureDecreasingPortmanteau` transfers the bound from the
family to the limit, and locality transfers it from `u` to `w`.

Upper semicontinuity of `f` is used only through its measurability: this is the special case of
`RooftopTruncationConcentrationMeasurable.exists_isOpen_measure_inter_eq_zero_of_antitone_of_measurable`,
where the proof is. -/
theorem exists_isOpen_measure_inter_eq_zero_of_antitone (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hf : UpperSemicontinuous f) (hf0 : ∀ x, f x ≤ 0) {C : ℝ} (hC1 : 1 ≤ C)
    (hfqcC : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
        ∃ G : Set M, IsOpen G ∧
          thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
          ContinuousOn (fun y => (refTrunc theta f C y).toReal) (K \ G))
    (hp : ∀ k, IsThetaPshPotential theta.val (p k)) (hp0 : ∀ k y, p k y ≤ 0)
    (hpanti : ∀ y, Antitone fun k => p k y)
    (hw : IsThetaPshPotential theta.val w) (hwp : ∀ k y, w y ≤ p k y)
    (hplim : ∀ y, Tendsto (fun k => p k y) atTop (𝓝 (w y)))
    (hzero : ∀ k, diagonalPotentialMeasure theta (p k) (hp k)
      {y : M | p k y < f y} = 0)
    {delta : ℝ} (hdelta : 0 < delta)
    {x : M} (hx : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      diagonalPotentialMeasure theta w hw
        (O ∩ ({y : M | w y + (delta : EReal) < f y} ∩
          {y : M | thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) < w y})) = 0 :=
  exists_isOpen_measure_inter_eq_zero_of_antitone_of_measurable hn hbig hV hf.measurable hf0 hC1
    hfqcC hp hp0 hpanti hw hwp hplim hzero hdelta hx

end Core

/-! ### Step 1.2: Theorem 2.4.4 for an arbitrary nonpositive obstacle -/

section Step

variable [Nonempty M] {theta : ClosedRealOneOneForm n M} {f : M → EReal}

/-- The competitor family of an obstacle is nonempty as soon as its rooftop
envelope is a genuine potential: an empty family gives the envelope `-infinity`,
which is nowhere nondegenerate. -/
theorem rooftopCompetitors_nonempty_of_isThetaPshPotential
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    (rooftopCompetitors theta.val f).Nonempty := by
  rcases eq_empty_or_nonempty (rooftopCompetitors theta.val f) with hemp | h
  · exfalso
    rw [rooftopEnvelope_of_empty hemp] at hw
    obtain ⟨y, -, hy⟩ := hw.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact hy rfl
  · exact h

/-- A reference truncation of an upper semicontinuous obstacle is upper
semicontinuous. -/
theorem upperSemicontinuous_refTrunc (hf : UpperSemicontinuous f)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) (C : ℝ) :
    UpperSemicontinuous (refTrunc theta f C) := by
  have hVu : UpperSemicontinuous
      fun y : M => thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) :=
    (hV.add_const (-C)).1.quasiPlurisubharmonic.upperSemicontinuous
  intro x y hy
  have hy' : max (f x) (thetaPshSupremum theta.val x + ((-C : ℝ) : EReal)) < y := hy
  rw [max_lt_iff] at hy'
  filter_upwards [hf x y hy'.1, hVu x y hy'.2] with z h1 h2
  exact max_lt h1 h2

theorem refTrunc_le_zero (hf0 : ∀ x, f x ≤ 0) {C : ℝ} (hC : 0 ≤ C) (y : M) :
    refTrunc theta f C y ≤ (0 : EReal) := by
  refine max_le (hf0 y) ?_
  calc thetaPshSupremum theta.val y + ((-C : ℝ) : EReal)
      ≤ 0 + ((-C : ℝ) : EReal) :=
        add_le_add (by simpa using thetaPshSupremum_le_zero theta.val y) le_rfl
    _ = ((-C : ℝ) : EReal) := zero_add _
    _ ≤ 0 := by
        rw [show (0 : EReal) = ((0 : ℝ) : EReal) from by norm_num, EReal.coe_le_coe_iff]
        linarith

/-- **Xia, SGPT, Theorem 2.4.4, the `delta`-level statement above a truncated
reference** (`xia-sgpt:page-0081`, equation (2.26)).  For `C >= 1`,
`theta^n_{P_theta(f)}` gives no mass to
`{P_theta(f) + delta < f} ∩ {V_theta - C < P_theta(f)}`.

The obstacle is **not** assumed bounded below.  The truncated instances of the
bounded theorem are supplied here rather than assumed: the family is
`p_k = P_theta(f \/ (V_theta - k))`, each member of which satisfies
`V_theta + (-k) <= f \/ (V_theta - k)`, so the bounded theorem applies to it. -/
theorem diagonalPotentialMeasure_lt_add_inter_eq_zero (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hf : UpperSemicontinuous f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f))
    {C : ℝ} (hC1 : 1 ≤ C) {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      ({y : M | rooftopEnvelope theta.val f y + (delta : EReal) < f y} ∩
        {y : M | thetaPshSupremum theta.val y + ((-C : ℝ) : EReal) <
          rooftopEnvelope theta.val f y}) = 0 := by
  classical
  have hne : (rooftopCompetitors theta.val f).Nonempty :=
    rooftopCompetitors_nonempty_of_isThetaPshPotential hw
  have hTusc : ∀ k : ℕ, UpperSemicontinuous (refTrunc theta f (k : ℝ)) := fun k =>
    upperSemicontinuous_refTrunc hf hV _
  have hT0 : ∀ (k : ℕ) (y : M), refTrunc theta f (k : ℝ) y ≤ 0 := fun k y =>
    refTrunc_le_zero hf0 (Nat.cast_nonneg k) y
  have hTtop : ∀ (k : ℕ) (y : M), refTrunc theta f (k : ℝ) y ≠ ⊤ := fun k y =>
    ne_top_of_le_ne_top (by simp) (hT0 k y)
  have hTne : ∀ k : ℕ, (rooftopCompetitors theta.val (refTrunc theta f (k : ℝ))).Nonempty :=
    fun k => ⟨fun y => thetaPshSupremum theta.val y + ((-(k : ℝ) : ℝ) : EReal),
      hV.add_const _,
      quasiEverywhere_of_forall fun y => refShift_le_refTrunc theta f (k : ℝ) y⟩
  have hp : ∀ k : ℕ, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (refTrunc theta f (k : ℝ))) := fun k =>
    isThetaPshPotential_rooftopEnvelope_of_upperSemicontinuous hn theta hbig
      (hTusc k) (hTtop k) (hTne k)
  have hpT : ∀ k : ℕ, rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) ≤
      refTrunc theta f (k : ℝ) := fun k =>
    rooftopEnvelope_le_of_upperSemicontinuous hn theta hbig (hTusc k) (hTtop k)
  have hp0 : ∀ (k : ℕ) (y : M),
      rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) y ≤ 0 :=
    fun k y => (hpT k y).trans (hT0 k y)
  have hTanti : ∀ (y : M) (j k : ℕ), j ≤ k →
      refTrunc theta f (k : ℝ) y ≤ refTrunc theta f (j : ℝ) y := by
    intro y j k hjk
    refine max_le_max le_rfl (add_le_add le_rfl ?_)
    exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hjk))
  have hpanti : ∀ y : M, Antitone fun k : ℕ =>
      rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) y := by
    intro y j k hjk
    exact rooftopEnvelope_mono (θ := theta.val) (fun z => hTanti z j k hjk) y
  have hwp : ∀ (k : ℕ) (y : M), rooftopEnvelope theta.val f y ≤
      rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) y := fun k y =>
    rooftopEnvelope_mono (θ := theta.val) (fun z => le_refTrunc theta f (k : ℝ) z) y
  have hplim : ∀ y : M, Tendsto (fun k : ℕ =>
      rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) y) atTop
      (𝓝 (rooftopEnvelope theta.val f y)) := by
    intro y
    rw [RooftopUscDecreasingLimit.rooftopEnvelope_eq_iInf_of_antitone_usc hn theta hbig
      (F := fun k : ℕ => refTrunc theta f (k : ℝ)) hTusc hTtop hTne
      (fun z j k hjk => hTanti z j k hjk) (iInf_refTrunc theta f) hne y]
    exact tendsto_atTop_iInf (hpanti y)
  have hzero : ∀ k : ℕ, diagonalPotentialMeasure theta
      (rooftopEnvelope theta.val (refTrunc theta f (k : ℝ))) (hp k)
      {y : M | rooftopEnvelope theta.val (refTrunc theta f (k : ℝ)) y < f y} = 0 := by
    intro k
    refine measure_mono_null
      (fun y hy => lt_of_lt_of_le hy (le_refTrunc theta f (k : ℝ) y)) ?_
    exact diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous
      hn hbig hV (hTusc k) (fun y => refShift_le_refTrunc theta f (k : ℝ) y) (hT0 k)
      (hfqc (k : ℝ) (Nat.cast_nonneg k)) (hp k)
  refine measure_eq_zero_of_forall_exists_isOpen
    (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) ?_
  intro x hx
  exact exists_isOpen_measure_inter_eq_zero_of_antitone hn hbig hV hf hf0 hC1
    (hfqc C (le_trans zero_le_one hC1)) hp hp0 hpanti hw hwp hplim hzero hdelta hx.2

/-- **Xia, SGPT, Theorem 2.4.4, the `delta`-level statement** for an arbitrary
nonpositive upper semicontinuous obstacle.  The truncation level `C` is let go
to infinity: `⋃_C {V_theta - C < P_theta(f)}` is the complement of the poles of
`P_theta(f)`, which are pluripolar. -/
theorem diagonalPotentialMeasure_lt_add_eq_zero (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hf : UpperSemicontinuous f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f))
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {y : M | rooftopEnvelope theta.val f y + (delta : EReal) < f y} = 0 := by
  classical
  have hV0 : ∀ y, thetaPshSupremum theta.val y ≤ (0 : EReal) := fun y => by
    simpa using thetaPshSupremum_le_zero theta.val y
  have hftop : ∀ y : M, f y ≠ ⊤ := fun y => ne_top_of_le_ne_top (by simp) (hf0 y)
  have hwle : rooftopEnvelope theta.val f ≤ f :=
    rooftopEnvelope_le_of_upperSemicontinuous hn theta hbig hf hftop
  have hw0 : ∀ y : M, rooftopEnvelope theta.val f y ≤ (0 : EReal) := fun y =>
    (hwle y).trans (hf0 y)
  have hpoles : diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {y : M | rooftopEnvelope theta.val f y = ⊥} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hw.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)
  have hsub : {y : M | rooftopEnvelope theta.val f y + (delta : EReal) < f y} ⊆
      {y : M | rooftopEnvelope theta.val f y = ⊥} ∪
        ⋃ m : ℕ, ({y : M | rooftopEnvelope theta.val f y + (delta : EReal) < f y} ∩
          {y : M | thetaPshSupremum theta.val y +
            ((-((m : ℝ) + 1) : ℝ) : EReal) < rooftopEnvelope theta.val f y}) := by
    intro y hy
    by_cases hbot : rooftopEnvelope theta.val f y = ⊥
    · exact Or.inl hbot
    refine Or.inr ?_
    have htop : rooftopEnvelope theta.val f y ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (hw0 y)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, rooftopEnvelope theta.val f y = (r : EReal) :=
      ⟨_, (EReal.coe_toReal htop hbot).symm⟩
    rcases eq_or_ne (thetaPshSupremum theta.val y) ⊥ with hVb | hVb
    · refine mem_iUnion.mpr ⟨0, hy, ?_⟩
      show thetaPshSupremum theta.val y + _ < rooftopEnvelope theta.val f y
      rw [hVb, EReal.bot_add, hr]
      exact EReal.bot_lt_coe r
    · have hVt : thetaPshSupremum theta.val y ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) (hV0 y)
      obtain ⟨v, hv⟩ : ∃ v : ℝ, thetaPshSupremum theta.val y = (v : EReal) :=
        ⟨_, (EReal.coe_toReal hVt hVb).symm⟩
      obtain ⟨m, hm⟩ := exists_nat_gt (v - r)
      refine mem_iUnion.mpr ⟨m, hy, ?_⟩
      show thetaPshSupremum theta.val y + _ < rooftopEnvelope theta.val f y
      rw [hv, hr, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      linarith
  refine measure_mono_null hsub ?_
  refine measure_union_null hpoles (measure_iUnion_null fun m => ?_)
  exact diagonalPotentialMeasure_lt_add_inter_eq_zero hn hbig hV hf hf0 hfqc hw
    (le_add_of_nonneg_left (by positivity)) hdelta

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) for an
arbitrary nonpositive upper semicontinuous obstacle.**  `theta^n_{P_theta(f)}`
is carried by the contact set `{P_theta(f) = f}`.

No lower bound on the obstacle: this is the bounded theorem of
`Pending.RooftopUscEnvelopeConcentration` together with Xia's Step 1.2. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_nonpos (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hf : UpperSemicontinuous f) (hf0 : ∀ x, f x ≤ 0)
    (hfqc : RefTruncationsQuasiContinuous theta f)
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {y : M | rooftopEnvelope theta.val f y < f y} = 0 := by
  classical
  have hpoles : diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {y : M | rooftopEnvelope theta.val f y = ⊥} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hw.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)
  refine measure_mono_null
    (lt_subset_union_iUnion_add (rooftopEnvelope theta.val f) f) ?_
  refine measure_union_null hpoles (measure_iUnion_null fun m => ?_)
  exact diagonalPotentialMeasure_lt_add_eq_zero hn hbig hV hf hf0 hfqc hw
    (by positivity)

end Step

end

end SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
