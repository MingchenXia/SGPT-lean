import SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 for a bounded obstacle given by an abstract majorant family

`Pending.RooftopUscEnvelopeConcentration` proves Xia's Theorem 2.4.4
(`xia-sgpt:page-0079`, equation (2.23)) at the `delta` level for an obstacle
that is **upper semicontinuous**.  Upper semicontinuity enters that proof in
exactly two places, and nowhere else:

1. to produce a decreasing sequence of *continuous* majorants of the obstacle
   whose pointwise infimum is the obstacle
   (`Pending.RooftopUscObstacleApproximation.exists_continuous_antitone_majorants`);
2. to know `P_theta(f) <= f` pointwise, which is used only to bound
   `P_theta(f) <= 0`.

This module removes upper semicontinuity by turning both into hypotheses.  The
decreasing family `g` is now given, together with the three facts the argument
actually consumes about each of its members — that the envelope
`P_theta(g_k)` is a genuine potential, that it lies below `g_k`, and that Xia's
Theorem 2.4.4 already holds for `g_k` — and the nonpositivity of `P_theta(f)`
is assumed directly.  Nothing about the *regularity* of `g_k` is asked.

The point is Xia's own Step 2 (`xia-sgpt:page-0082`).  There the obstacle is
merely **quasi-continuous**, and the majorants he builds are
`h_j = sup_{k >= j} f_k` with `f_k` continuous Tietze extensions of `f` off a
set of small capacity: each `h_j` is lower semicontinuous, real valued and
bounded, and the family is decreasing — but it is *not* continuous, so the
upper semicontinuous engine does not apply to it, while the theorem below does.
A merely lower semicontinuous obstacle really is outside the reach of the usc
route: `P_theta(h) <= h` is false for such `h`
(`Pending.RooftopUscObstacleApproximation`, docstring of
`rooftopEnvelope_le_of_upperSemicontinuous`), which is why the contact
hypothesis for the members of the family is taken as an input here rather than
re-derived.

Source: Xia, *Singularities in Global Pluripotential Theory*, Theorem 2.4.4
(`xia-sgpt:page-0079`; proof `xia-sgpt:page-0080`--`page-0083`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentration

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityChart
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
open SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
open SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] {theta : ClosedRealOneOneForm n M} {f : M → EReal}

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`), the `delta`-level
statement, for a bounded obstacle presented by a decreasing family of real
majorants.**  `theta^n_{P_theta(f)}` gives no mass to `{P_theta(f) + delta < f}`.

Compared with
`Pending.RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero`
the upper semicontinuity of the obstacle is gone.  In its place stand the
family `g` and the three properties of its members that the capacity argument
uses — `hu`, `hple`, `hcontact` — together with `hw0`.  Everything else is
unchanged, including `hfc` (the obstacle dominates a real translate of the
reference) and `hfqc` (quasi-continuity of the obstacle on compact subsets of
an open set where the reference is bounded). -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants
    (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {g : ℕ → M → ℝ}
    (hg0 : ∀ k x, g k x ≤ 0)
    (hgmaj : ∀ k x, f x ≤ ((g k x : ℝ) : EReal))
    (hganti : ∀ x, Antitone fun k => g k x)
    (hginf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    (hu : ∀ k, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun y => ((g k y : ℝ) : EReal)))
    (hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal))
    (hcontact : ∀ k, diagonalPotentialMeasure theta
      (rooftopEnvelope theta.val fun y => ((g k y : ℝ) : EReal)) (hu k)
      {y : M | rooftopEnvelope theta.val (fun z => ((g k z : ℝ) : EReal)) y <
        ((g k y : ℝ) : EReal)} = 0)
    {c : ℝ}
    (hfc : ∀ x, thetaPshSupremum theta.val x + (c : EReal) ≤ f x)
    (hf0 : ∀ x, f x ≤ 0)
    (hfqc : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (f y).toReal) (K \ G))
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f))
    (hw0 : ∀ x, rooftopEnvelope theta.val f x ≤ 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x : M | rooftopEnvelope theta.val f x + (delta : EReal) < f x} = 0 := by
  classical
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  set w : M → EReal := rooftopEnvelope theta.val f with hwdef
  set u : ℕ → M → EReal :=
    fun k => rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) with hudef
  have hu0 : ∀ k x, u k x ≤ (0 : EReal) := fun k x =>
    (hple k x).trans (by simpa using EReal.coe_le_coe_iff.mpr (hg0 k x))
  have hleV : ∀ k, u k ≤ V := fun k =>
    le_thetaPshSupremum (hu k) (fun x => by simpa using hu0 k x)
  have hVf : ∀ x, V x + (c : EReal) ≤ f x := hfc
  have hVc : ∀ k x, V x + (c : EReal) ≤ u k x := fun k =>
    le_rooftopEnvelope (hV.add_const _)
      (quasiEverywhere_of_forall fun x => (hVf x).trans (hgmaj k x))
  have hne : (rooftopCompetitors theta.val f).Nonempty :=
    ⟨fun x => V x + (c : EReal), hV.add_const _, quasiEverywhere_of_forall hVf⟩
  have hVcw : ∀ x, V x + (c : EReal) ≤ w x :=
    le_rooftopEnvelope (hV.add_const _) (quasiEverywhere_of_forall hVf)
  -- the capacity sandwich
  set Cst : ℝ := max (-c) 1 with hCstdef
  have hC1 : (1 : ℝ) ≤ Cst := le_max_right _ _
  have hlbV : ∀ k x, V x ≤ u k x + (Cst : EReal) := fun k x =>
    (le_add_neg_of_add_coe_le c (hVc k x)).trans
      (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  have hanti : ∀ x, Antitone fun k => u k x :=
    fun x => antitone_rooftopEnvelope_of_antitone hganti x
  have hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)) :=
    fun x => tendsto_rooftopEnvelope_of_antitone hginf hganti (fun k => (hu k).1)
      hple hne x
  have hcontactO : ∀ (O : Set M) (k : ℕ), diagonalPotentialMeasure theta (u k) (hu k)
      (O ∩ {y : M | u k y < ((g k y : ℝ) : EReal)}) = 0 := fun O k =>
    measure_mono_null inter_subset_right (hcontact k)
  -- the local statement at every point off the non-Kähler locus
  have hloc : ∀ x ∈ {y : M | w y + (delta : EReal) < f y} \
      nonKahlerLocus (RealBottChern.ofRepresentative theta),
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
        diagonalPotentialMeasure theta w hw
          (O ∩ {y : M | w y + (delta : EReal) < f y}) = 0 := by
    intro x hx
    obtain ⟨N, hN, hVb0⟩ :=
      exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx.2
    obtain ⟨Omega, hOmegaN, hOmegaOpen, hxOmega⟩ := mem_nhds_iff.mp hN
    have hVbO : IsBoundedPotentialOn V Omega := hVb0.mono hOmegaN
    obtain ⟨e, D, hD, rho, hrho, L, O, hL, hsrcOmega, hOopen, hxO, hOS⟩ :=
      exists_diagSlotChart_source_subset_closure_subset theta hOmegaOpen hxOmega
    have hVbS : IsBoundedPotentialOn V
        ((diagSlotChart theta e D hD rho hrho).source : Set M) := hVbO.mono hsrcOmega
    have hubS : ∀ k, IsBoundedPotentialOn (u k)
        ((diagSlotChart theta e D hD rho hrho).source : Set M) := fun k =>
      isBoundedPotentialOn_of_le_add_const hVbS (hVc k)
        (fun y => by rw [EReal.coe_zero]; exact hu0 k y)
    have hwbS : IsBoundedPotentialOn w
        ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
      isBoundedPotentialOn_of_le_add_const hVbS hVcw
        (fun y => by rw [EReal.coe_zero]; exact hw0 y)
    have hfbS : IsBoundedPotentialOn f
        ((diagSlotChart theta e D hD rho hrho).source : Set M) :=
      isBoundedPotentialOn_of_le_add_const hVbS hfc
        (fun y => by rw [EReal.coe_zero]; exact hf0 y)
    have hKcomp : IsCompact (closure O) := isClosed_closure.isCompact
    have hqc : ∀ eps : ℝ, 0 < eps → ∃ A : Set M, IsOpen A ∧
        thetaCapacity theta V A < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (w y).toReal) (closure O \ A) ∧
        ContinuousOn (fun y => (f y).toReal) (closure O \ A) := by
      intro eps heps
      have heps4 : (0 : ℝ) < eps / 4 := by positivity
      obtain ⟨G1, hG1open, hG1cap, hG1cont⟩ :=
        exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hw
          (diagSlotChart theta e D hD rho hrho).source.isOpen hwbS hVbS hKcomp hOS heps4
      obtain ⟨G2, hG2open, hG2cap, hG2cont⟩ :=
        hfqc ((diagSlotChart theta e D hD rho hrho).source : Set M)
          (diagSlotChart theta e D hD rho hrho).source.isOpen hVbS (closure O) hKcomp
          hOS (eps / 4) heps4
      refine ⟨G1 ∪ G2, hG1open.union hG2open, ?_, ?_, ?_⟩
      · have hsum : thetaCapacity theta V (G1 ∪ G2) ≤
            ENNReal.ofReal (eps / 4) + ENNReal.ofReal (eps / 4) :=
          (thetaCapacity_union_le theta V G1 G2).trans
            (add_le_add hG1cap.le hG2cap.le)
        refine lt_of_le_of_lt hsum ?_
        rw [← ENNReal.ofReal_add heps4.le heps4.le]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)
      · exact hG1cont.mono (sdiff_subset_sdiff_right subset_union_left)
      · exact hG2cont.mono (sdiff_subset_sdiff_right subset_union_right)
    exact ⟨O, hOopen, hxO,
      diagonalPotentialMeasure_inter_lt_add_eq_zero (hD := hD) (hrho := hrho)
        (V := V) (w := w) (f := f) (u := u) (g := g) hu hw hV hubS hwbS hVbS hfbS
        hL hanti hlim hC1 hleV hlbV hple hgmaj hOopen hOS (hcontactO O) hqc hdelta⟩
  exact measure_eq_zero_of_forall_exists_isOpen
    (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) hloc

/-- **Faithfulness check: the upper semicontinuous engine is an instance.**

This re-proves
`Pending.RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero`
from the theorem above, by feeding it the truncated continuous decreasing
majorants of an upper semicontinuous obstacle.  Its only purpose is to show
that the abstract hypothesis package of that theorem is satisfiable and that
the generalisation is faithful: the statement proved here is the pre-existing
one, verbatim. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_upperSemicontinuous
    (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hf : UpperSemicontinuous f) {c : ℝ}
    (hfc : ∀ x, thetaPshSupremum theta.val x + (c : EReal) ≤ f x)
    (hf0 : ∀ x, f x ≤ 0)
    (hfqc : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (f y).toReal) (K \ G))
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f))
    {delta : ℝ} (hdelta : 0 < delta) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x : M | rooftopEnvelope theta.val f x + (delta : EReal) < f x} = 0 := by
  classical
  have htop : ∀ x, f x ≠ ⊤ := fun x => ne_top_of_le_ne_top (by simp) (hf0 x)
  obtain ⟨C0, g0, hcont0, hmaj0, -, hanti0, hgf0⟩ :=
    exists_continuous_antitone_majorants n hf htop
  have hmono : Monotone (fun r : ℝ => (r : EReal)) :=
    fun a b h => EReal.coe_le_coe_iff.mpr h
  set g : ℕ → M → ℝ := fun k x => min (g0 k x) 0 with hgdef
  have hcoe : ∀ k x, ((g k x : ℝ) : EReal) =
      min ((g0 k x : ℝ) : EReal) ((0 : ℝ) : EReal) := fun k x => hmono.map_min
  have hcont : ∀ k, Continuous (g k) := fun k => (hcont0 k).min continuous_const
  have hg0 : ∀ k x, g k x ≤ 0 := fun k x => min_le_right _ _
  have hgmaj : ∀ k x, f x ≤ ((g k x : ℝ) : EReal) := by
    intro k x
    rw [hcoe]
    exact le_min (hmaj0 k x) (by simpa using hf0 x)
  have hganti : ∀ x, Antitone fun k => g k x :=
    fun x _ _ hjk => min_le_min (hanti0 x hjk) le_rfl
  have hginf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x := by
    intro x
    refine le_antisymm ?_ (le_iInf fun k => hgmaj k x)
    exact (iInf_mono fun k => EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans
      (le_of_eq (hgf0 x))
  have hu : ∀ k, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun y => ((g k y : ℝ) : EReal)) :=
    fun k => isThetaPshPotential_rooftopEnvelope_of_continuous hn theta hbig (hcont k)
  have hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal) :=
    fun k => rooftopEnvelope_le_of_continuous (hcont k)
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig (hcont k)) (hu k).1
  have hw0 : ∀ x, rooftopEnvelope theta.val f x ≤ 0 := fun x =>
    ((rooftopEnvelope_le_of_upperSemicontinuous hn theta hbig hf htop) x).trans (hf0 x)
  exact diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants hn hbig hV
    hg0 hgmaj hganti hginf hu hple
    (fun k => diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous hn theta
      hbig hV (hcont k) (hu k))
    hfc hf0 hfqc hw hw0 hdelta


/-! ### Theorem 2.4.4 for a bounded lower semicontinuous obstacle -/

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`) for a bounded LOWER
semicontinuous real obstacle.**  `theta^n_{P_theta(F)}` gives no mass to
`{P_theta(F) < F}`.

This is Xia's Lemma 2.4.3 (`xia-sgpt:page-0079`, (2.21)) plus the fact that
`nK({theta})` is null, exactly as in
`Pending.RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous`;
the continuity of the obstacle was used there only to get the global bound and
Xia's (2.20).  Both are hypotheses here, and (2.20) really has to be one: for a
merely lower semicontinuous obstacle `P_theta(F) <= F` can FAIL pointwise.  A
closed pluripolar set `P` with empty interior and `F = -1` on `P`, `F = 0` off
`P` is lower semicontinuous, and every `theta`-PSH `v <= 0` is a competitor,
so `P_theta(F) = V_theta > F` on `P`.

This is the member-level hypothesis `hcontact` of
`diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants`, for the
lower semicontinuous majorant families that Xia's Step 2 produces. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous
    (hn : 0 < n) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {F : M → ℝ} (hF : LowerSemicontinuous F) {C : ℝ} (hCabs : ∀ x, |F x| ≤ C)
    (hu : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)))
    (hule : ∀ x, rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x ≤
      ((F x : ℝ) : EReal)) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)) hu
      {x : M | rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x <
        ((F x : ℝ) : EReal)} = 0 := by
  classical
  set u : M → EReal := rooftopEnvelope theta.val (fun x => ((F x : ℝ) : EReal)) with hudef
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  have hFle : ∀ x, F x ≤ C := fun x => (abs_le.mp (hCabs x)).2
  have hFge : ∀ x, (-C : ℝ) ≤ F x := fun x => (abs_le.mp (hCabs x)).1
  have huC : ∀ x, u x ≤ (C : EReal) :=
    fun x => (hule x).trans (EReal.coe_le_coe_iff.mpr (hFle x))
  have hVu : ∀ x, V x + ((-C : ℝ) : EReal) ≤ u x := by
    have hcomp : ∀ x, V x + ((-C : ℝ) : EReal) ≤ ((F x : ℝ) : EReal) := by
      intro x
      have h0 : V x ≤ (0 : EReal) := by
        simpa [hVdef] using thetaPshSupremum_le_zero theta.val x
      calc V x + ((-C : ℝ) : EReal) ≤ 0 + ((-C : ℝ) : EReal) :=
            add_le_add h0 (le_refl _)
        _ = ((-C : ℝ) : EReal) := zero_add _
        _ ≤ ((F x : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (hFge x)
    exact le_rooftopEnvelope (hV.add_const _) (quasiEverywhere_of_forall hcomp)
  have hloc : ∀ x, x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta) →
      ∃ N ∈ 𝓝 x, IsBoundedPotentialOn u N := by
    intro x hx
    obtain ⟨N, hN, hb⟩ :=
      exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx
    exact ⟨N, hN, isBoundedPotentialOn_of_le_add_const hb hVu huC⟩
  have hFlsc : LowerSemicontinuous (fun x => ((F x : ℝ) : EReal)) := by
    intro x r hr
    rcases EReal.lt_iff_exists_real_btwn.mp hr with ⟨q, hq1, hq2⟩
    have hq2' : q < F x := by
      simpa only [EReal.coe_lt_coe_iff] using hq2
    filter_upwards [hF x q hq2'] with y hy
    exact hq1.trans (EReal.coe_lt_coe_iff.mpr hy)
  have hgood : diagonalPotentialMeasure theta u hu
      ({x : M | u x < ((F x : ℝ) : EReal)} \
        nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
    diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded
      (f := fun x => ((F x : ℝ) : EReal)) hn hFlsc hule
      (fun v hv hvF => le_rooftopEnvelope hv (quasiEverywhere_of_forall hvF)) hu
      (fun _ hx => hx.1) (fun x hx => hloc x hx.2)
  have hbad : diagonalPotentialMeasure theta u hu
      (nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
    diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hu
  refine nonpos_iff_eq_zero.mp ?_
  calc diagonalPotentialMeasure theta u hu {x : M | u x < ((F x : ℝ) : EReal)}
      ≤ diagonalPotentialMeasure theta u hu
          (({x : M | u x < ((F x : ℝ) : EReal)} \
            nonKahlerLocus (RealBottChern.ofRepresentative theta)) ∪
            nonKahlerLocus (RealBottChern.ofRepresentative theta)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyn : y ∈ nonKahlerLocus (RealBottChern.ofRepresentative theta)
        · exact Or.inr hyn
        · exact Or.inl ⟨hy, hyn⟩
    _ ≤ _ := measure_union_le _ _
    _ = 0 := by rw [hgood, hbad, add_zero]


end

end SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentration
