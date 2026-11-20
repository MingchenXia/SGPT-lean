import SGPT.Foundations.Analysis.Pending.RooftopLocalConcentration
import SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
import SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink
import SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
import SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 for an upper semicontinuous obstacle bounded relative to
the reference

Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)): for a big
class `{theta}` and a quasi-continuous obstacle `f`, the non-pluripolar
Monge--Ampere measure of the envelope `P_theta(f)` is carried by the contact set
`{P_theta(f) = f}`.  This module proves it for an obstacle that is **upper
semicontinuous, at most `0`, and bounded below by a real translate of the
reference `V_theta`**, with quasi-continuity of the obstacle (`hfqc`) as the
remaining source-level hypothesis.

**What "bounded" means here, and what it still costs.**  The obstacle is not
assumed bounded below by a constant but only **relative to the reference**,
`hfc : V_theta + c <= f`.  That is strictly weaker (`V_theta <= 0`, so
`c <= f` implies it) and it is vacuous on the poles of `V_theta`, so an obstacle
may be `-infinity` exactly where `V_theta` is.  It is the honest hypothesis: the
proof uses `hfc` only twice, to make `V_theta + c` a competitor of the obstacle
and to bound `f` on a slot-chart source where `V_theta` is already bounded, and
the *global* content of both is a single constant `C` in the capacity sandwich
`V_theta - C <= P_theta(g_k) <= V_theta`.

Neither Section 3.1 obstacle satisfies it as written: `min {phi, psi}` in
`Pending.RooftopContactConcentration` and `a phi + (1 - a) psi` in
`Pending.DominationPrincipleContactChain` (not upper semicontinuous either,
`1 - a < 0`) are `-infinity` on the poles of a potential, and those poles need
not be poles of `V_theta`.  But the *truncations* do satisfy it, which is why
this is the right form of the hypothesis:

  `min {phi, psi} \/ (V_theta - C) = min {phi \/ (V_theta - C), psi \/ (V_theta - C)}`

is upper semicontinuous, lies above `V_theta - C`, and each of its two arguments
is bounded on any open set where `V_theta` is bounded -- so
`Pending.ThetaCapacityMinQuasiContinuity.exists_isOpen_thetaCapacity_lt_continuousOn_min_of_boundedOn`
supplies `hfqc` for it too.  What remains between this module and Xia's
Theorem 2.4.4 for the Section 3.1 obstacles is therefore *only* the passage of
the **measures** to the limit as `C -> infinity`, Xia's Step 1.2
(`xia-sgpt:page-0080`--`page-0081`): plurifine locality of `theta^n` on
`{P_theta(f) > V_theta - C}`, the vague convergence of
`Pending.BedfordTaylorDecreasingLimit` and the capacity estimate of
`Pending.ThetaCapacityIntegralComparison`.  No further hypothesis on the
obstacle is owed.  A shortcut that does **not** work, and was checked: the
truncation cannot be moved inside the envelope, because
`P_theta(f \/ (V_theta - C)) != P_theta(f) \/ (V_theta - C)` in general.

The local step is
`Pending.RooftopLocalConcentration.diagonalPotentialMeasure_inter_lt_add_eq_zero`;
what is done here is everything around it.  Its eight analytic hypotheses are
discharged as follows, and each discharge is a lemma below.

* **The decreasing family.**  `f` is the pointwise infimum of a decreasing
  sequence of continuous majorants (`Pending.RooftopUscObstacleApproximation`),
  truncated above at `0` so that the envelopes stay below `V_theta`; the
  envelopes `u_k = P_theta(g_k)` then decrease to `P_theta(f)`
  (`tendsto_rooftopEnvelope_of_antitone`).

* **The contact hypothesis `hcontact`.**  Each `g_k` is continuous, hence
  *lower* semicontinuous, so Xia's Lemma 2.4.3 in the form
  `Pending.PatchBoundedNeighborhood.diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded`
  applies to it directly, off `nK({theta})` where Lemma 2.4.1 bounds the
  envelope; and `nK({theta})` is null
  (`Pending.BigClassNonKahlerLocusNull`).  So the contact vanishing is a
  **theorem** here, `diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous`
  — Theorem 2.4.4 for a continuous obstacle — and not a hypothesis.  This is
  what replaces Xia's Step 2: his Tietze construction on small-capacity
  complements is needed only because he starts from a quasi-continuous
  obstacle, not from an upper semicontinuous one.

* **The capacity sandwich `V_theta - C <= u_k <= V_theta`.**  No truncation of
  the family is needed: `g_k <= 0` gives `u_k <= V_theta` outright, and
  `V_theta + c <= f <= g_k` makes `V_theta + c` a competitor of every `g_k`,
  which is the lower bound with the single constant `C = max (-c) 1`.

* **The local bounds on the slot-chart source.**  All of `V_theta`, `w`, the
  `u_k` and `f` are squeezed between `V_theta + c` and `0`, so one two-sided
  bound for `V_theta` on a neighbourhood bounds all of them at once, uniformly
  in `k`.  Lemma 2.4.1 supplies that neighbourhood off `nK({theta})`, and
  `Pending.SlotChartBoundedShrink` shrinks a slot chart inside it together with
  a relatively compact coordinate ball.

* **Quasi-continuity `hqc`.**  For `w` it is Theorem 2.3.2 in the local form of
  `Pending.ThetaCapacityLocalQuasiContinuity`.  For the obstacle it is Xia's own
  hypothesis on `f` and is kept as such, `hfqc`, quantified only over compact
  subsets of an open set where `V_theta` is bounded — which is where the proof
  uses it, and where a consumer can hope to supply it.

* **The passage to the global statement.**  `{w < f}` is the union of the poles
  of `w` and of the countably many sets `{w + 1/(m+1) < f}`
  (`RooftopLocalConcentration.lt_subset_union_iUnion_add`); each of those is
  handled point by point off `nK({theta})` by
  `RooftopLocalConcentration.measure_eq_zero_of_forall_exists_isOpen`.

Everything here inherits the `sorryAx` of the big-class reference chain
(Boucksom's Theorem 3.17 through `Pending.KahlerCurrentRegularization`, I-0173)
through `IsBigClass`; nothing else is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration

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
open SGPT.Foundations.Analysis.Pending.SlotChartBoundedShrink

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### Two pieces of `EReal` bookkeeping -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- A real constant can be moved across `<=` in `EReal`. -/
theorem le_add_neg_of_add_coe_le {a b : EReal} (c : ℝ) (h : a + (c : EReal) ≤ b) :
    a ≤ b + ((-c : ℝ) : EReal) := by
  have hc : a + (c : EReal) + ((-c : ℝ) : EReal) = a := by
    cases a with
    | bot => simp [EReal.bot_add]
    | top => simp
    | coe r => rw [← EReal.coe_add, ← EReal.coe_add]; norm_num
  calc a = a + (c : EReal) + ((-c : ℝ) : EReal) := hc.symm
    _ ≤ b + ((-c : ℝ) : EReal) := by gcongr

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
/-- A two-sided bound for `v` on `S` bounds every `u` squeezed between a real
translate of `v` and a global constant. -/
theorem isBoundedPotentialOn_of_le_add_const {v u : M → EReal} {S : Set M} {c C : ℝ}
    (hb : IsBoundedPotentialOn v S)
    (hvu : ∀ x, v x + (c : EReal) ≤ u x) (hu : ∀ x, u x ≤ (C : EReal)) :
    IsBoundedPotentialOn u S := by
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨a + c, C, fun x hx => ⟨?_, hu x⟩⟩
  rw [EReal.coe_add]
  exact (add_le_add (hab x hx).1 (le_refl ((c : ℝ) : EReal))).trans (hvu x)

/-! ### Theorem 2.4.4 for a continuous obstacle -/

/-- **Xia, SGPT, Theorem 2.4.4 for a continuous obstacle, on a big class.**
`theta^n_{P_theta(F)}` gives no mass to `{P_theta(F) < F}`.

A continuous obstacle is lower semicontinuous, so Xia's Lemma 2.4.3 applies to
it verbatim; the only thing to supply is his Lemma 2.4.1, and the fact that
`nK({theta})` — the one place where Lemma 2.4.1 says nothing — is null. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous
    [Nonempty M] (hn : 0 < n) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {F : M → ℝ} (hF : Continuous F)
    (hu : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)) hu
      {x : M | rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x <
        ((F x : ℝ) : EReal)} = 0 := by
  classical
  set u : M → EReal := rooftopEnvelope theta.val (fun x => ((F x : ℝ) : EReal)) with hudef
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  -- `F` is globally bounded
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (f := F) hF.continuousOn
  have hCabs : ∀ x, |F x| ≤ C := fun x => hC x (mem_univ x)
  have hFle : ∀ x, F x ≤ C := fun x => (abs_le.mp (hCabs x)).2
  have hFge : ∀ x, (-C : ℝ) ≤ F x := fun x => (abs_le.mp (hCabs x)).1
  -- the envelope lies below the obstacle, and above `V - C`
  have hule : ∀ x, u x ≤ ((F x : ℝ) : EReal) :=
    rooftopEnvelope_le_of_continuous hF
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig hF) hu.1
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
  -- the envelope is locally bounded off `nK({theta})`
  have hloc : ∀ x, x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta) →
      ∃ N ∈ 𝓝 x, IsBoundedPotentialOn u N := by
    intro x hx
    obtain ⟨N, hN, hb⟩ :=
      exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx
    exact ⟨N, hN, isBoundedPotentialOn_of_le_add_const hb hVu huC⟩
  -- Lemma 2.4.3 off the locus, and the locus is null
  have hgood : diagonalPotentialMeasure theta u hu
      ({x : M | u x < ((F x : ℝ) : EReal)} \
        nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
    diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded
      (f := fun x => ((F x : ℝ) : EReal)) hn
      (EReal.continuous_coe_iff.mpr hF).lowerSemicontinuous hule
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

/-! ### Theorem 2.4.4 for a bounded upper semicontinuous obstacle -/

section Usc

variable [Nonempty M] {theta : ClosedRealOneOneForm n M} {f : M → EReal}

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`), the `delta`-level
statement, for a bounded upper semicontinuous obstacle on a big class.**
`theta^n_{P_theta(f)}` gives no mass to `{P_theta(f) + delta < f}`.

The proof is Xia's, assembled from
`RooftopLocalConcentration.diagonalPotentialMeasure_inter_lt_add_eq_zero` at
every point off `nK({theta})`: the slot chart and the relatively compact
coordinate ball come from `Pending.SlotChartBoundedShrink`, the bounds on its
source from Lemma 2.4.1 for `V_theta` together with the sandwich
`V_theta + c <= u_k, w <= 0`, the contact hypothesis from Theorem 2.4.4 for the
continuous majorants above, and quasi-continuity of `w` from Theorem 2.3.2 in
its local form.  `nK({theta})` itself is null.

`hfqc` is quasi-continuity of the **obstacle** for `Cap_theta`, on compact
subsets of an open set where `V_theta` is bounded: Xia's own hypothesis on `f`,
in the only form this proof uses it.  It is satisfiable — a continuous `f` takes
`G = empty`.  `hfc` asks only that `f` dominate a real translate of the
reference, not a constant; see the module docstring for why that is the form
the truncated Section 3.1 obstacles satisfy. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero (hn : 0 < n)
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
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  set w : M → EReal := rooftopEnvelope theta.val f with hwdef
  have htop : ∀ x, f x ≠ ⊤ := fun x => ne_top_of_le_ne_top (by simp) (hf0 x)
  -- the truncated continuous majorants
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
    fun x j k hjk => min_le_min (hanti0 x hjk) le_rfl
  have hginf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x := by
    intro x
    refine le_antisymm ?_ (le_iInf fun k => hgmaj k x)
    exact (iInf_mono fun k => EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans
      (le_of_eq (hgf0 x))
  -- the decreasing family of envelopes
  set u : ℕ → M → EReal :=
    fun k => rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) with hudef
  have hu : ∀ k, IsThetaPshPotential theta.val (u k) :=
    fun k => isThetaPshPotential_rooftopEnvelope_of_continuous hn theta hbig (hcont k)
  have hple : ∀ k x, u k x ≤ ((g k x : ℝ) : EReal) :=
    fun k => rooftopEnvelope_le_of_continuous (hcont k)
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig (hcont k)) (hu k).1
  have hu0 : ∀ k x, u k x ≤ (0 : EReal) := fun k x =>
    (hple k x).trans (by simpa using EReal.coe_le_coe_iff.mpr (hg0 k x))
  have hleV : ∀ k, u k ≤ V := fun k =>
    le_thetaPshSupremum (hu k) (fun x => by simpa using hu0 k x)
  -- `V + c` is a competitor of every `g k` and of `f`
  have hVf : ∀ x, V x + (c : EReal) ≤ f x := hfc
  have hVc : ∀ k x, V x + (c : EReal) ≤ u k x := fun k =>
    le_rooftopEnvelope (hV.add_const _)
      (quasiEverywhere_of_forall fun x => (hVf x).trans (hgmaj k x))
  have hne : (rooftopCompetitors theta.val f).Nonempty :=
    ⟨fun x => V x + (c : EReal), hV.add_const _,
      quasiEverywhere_of_forall hVf⟩
  have hVcw : ∀ x, V x + (c : EReal) ≤ w x :=
    le_rooftopEnvelope (hV.add_const _) (quasiEverywhere_of_forall hVf)
  have hwf : w ≤ f :=
    rooftopEnvelope_le_of_upperSemicontinuous hn theta hbig hf htop
  have hw0 : ∀ x, w x ≤ (0 : EReal) := fun x => (hwf x).trans (hf0 x)
  -- the capacity sandwich
  set Cst : ℝ := max (-c) 1 with hCstdef
  have hC1 : (1 : ℝ) ≤ Cst := le_max_right _ _
  have hlbV : ∀ k x, V x ≤ u k x + (Cst : EReal) := fun k x =>
    (le_add_neg_of_add_coe_le c (hVc k x)).trans
      (add_le_add (le_refl _) (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  -- monotonicity and convergence of the family
  have hanti : ∀ x, Antitone fun k => u k x :=
    fun x => antitone_rooftopEnvelope_of_antitone hganti x
  have hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)) :=
    fun x => tendsto_rooftopEnvelope_of_antitone hginf hganti (fun k => (hu k).1)
      hple hne x
  -- the contact hypothesis, for every member of the family at once
  have hcontact : ∀ (O : Set M) (k : ℕ), diagonalPotentialMeasure theta (u k) (hu k)
      (O ∩ {y : M | u k y < ((g k y : ℝ) : EReal)}) = 0 := fun O k =>
    measure_mono_null inter_subset_right
      (diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous hn theta hbig
        hV (hcont k) (hu k))
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
      isBoundedPotentialOn_of_le_add_const hVbS hVcw (fun y => by rw [EReal.coe_zero]; exact hw0 y)
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
        hL hanti hlim hC1 hleV hlbV hple hgmaj hOopen hOS (hcontact O) hqc hdelta⟩
  exact measure_eq_zero_of_forall_exists_isOpen
    (diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hw) hloc

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)), for a
bounded upper semicontinuous obstacle on a big class.**  The non-pluripolar
Monge--Ampere measure of `P_theta(f)` is carried by the contact set
`{P_theta(f) = f}`.

`{w < f}` is the union of the poles of `w`, which are pluripolar hence null, and
of the countably many sets `{w + 1/(m+1) < f}`, each handled by the
`delta`-level statement. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
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
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x : M | rooftopEnvelope theta.val f x < f x} = 0 := by
  classical
  set w : M → EReal := rooftopEnvelope theta.val f with hwdef
  have hpoles : diagonalPotentialMeasure theta w hw {x : M | w x = ⊥} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hw.1) _
      (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential)
  have hmid : ∀ m : ℕ, diagonalPotentialMeasure theta w hw
      {x : M | w x + ((1 / ((m : ℝ) + 1) : ℝ) : EReal) < f x} = 0 := fun m =>
    diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero hn hbig hV hf hfc hf0
      hfqc hw (by positivity)
  refine measure_mono_null (lt_subset_union_iUnion_add w f) ?_
  exact measure_union_null hpoles (measure_iUnion_null hmid)

end Usc

end

end SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
