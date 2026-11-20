import SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

set_option autoImplicit false

/-!
# Xia's Lemma 2.4.3 with nothing left over, for a big class

`Pending.PolydiskPatchBalayageContact.diagonalPotentialMeasure_lt_eq_zero` is
Xia's Lemma 2.4.3 (`xia-sgpt:page-0079`) with its local-boundedness datum
`hloc` carried as a hypothesis, and
`Pending.PatchBoundedNeighborhood.diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded`
states that datum in Xia's own analytic form.  Xia discharges it by his
Lemma 2.4.1, which holds on `X \ nK({theta})` for a **big** class, and then
discards `nK({theta})` because it is a proper analytic subset, hence null for a
non-pluripolar product.

This module carries out that last step, so that for a big class Lemma 2.4.3
holds on the whole of `{P_theta(f) < f}` with no residual set and no local
hypothesis:

  `theta^n_{P_theta(f)} {P_theta(f) < f} = 0`     for lower semicontinuous `f`
                                                  bounded below.

The mechanism is Xia's own, in the first lines of his proof of Lemma 2.4.3:
`V_theta + inf_X f` is a competitor, so `P_theta(f) >= V_theta + inf_X f`, and
`P_theta(f)` is bounded above because it is `theta`-PSH on a compact manifold.
Here the role of `V_theta` is played directly by the normalized reference of
`Pending.BigClassSupremumContact.exists_normalized_reference_of_isBigClass`,
which is what makes the sandwich two-sided off the reference's polar set; the
polar set itself is locally pluripolar and therefore null.

Since `f` is lower semicontinuous and real valued on a compact manifold in the
source, `inf_X f` is finite there; here that finiteness is the explicit
hypothesis `hfb`, which is also what makes the statement true for `f` allowed
to take the value `+infinity`.

Bigness is a genuine hypothesis and is carried, exactly as in the source: for a
merely pseudo-effective class there is no reference at all.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
set_option linter.unusedSectionVars false in
/-- A potential squeezed between a locally bounded one and a finite constant is
itself locally bounded. -/
theorem isBoundedPotentialOn_of_le_of_le_const {u psi : M → EReal} {C : ℝ}
    (hpsiu : psi ≤ u) (hC : ∀ x, u x ≤ (C : EReal)) {N : Set M}
    (hb : IsBoundedPotentialOn psi N) : IsBoundedPotentialOn u N := by
  obtain ⟨a, _, hab⟩ := hb
  exact ⟨a, C, fun x hx => ⟨(hab x hx).1.trans (hpsiu x), hC x⟩⟩

variable [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Xia, SGPT, Lemma 2.4.3, with `hloc` discharged (big class).**  For a
lower semicontinuous obstacle bounded below, the largest `theta`-PSH potential
`w` below it is two-sided bounded on a neighbourhood of every point off the
polar set of the big-class reference. -/
theorem exists_isBoundedPotentialOn_of_reference
    {theta : ClosedRealOneOneForm n M}
    {psi : M → EReal} (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0)
    (hlocpsi : ∀ x, psi x ≠ ⊥ → ∃ N ∈ 𝓝 x, IsBoundedPotentialOn psi N)
    {f w : M → EReal} {c : ℝ} (hfb : ∀ y, (c : EReal) ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) :
    ∀ x, psi x ≠ ⊥ → ∃ N ∈ 𝓝 x, IsBoundedPotentialOn w N := by
  -- `psi + c` is a competitor, so it lies below `w`
  have hshift : IsThetaPshPotential theta.val (fun y => psi y + (c : EReal)) :=
    hpsi.add_const c
  have hshift_le : ∀ y, psi y + (c : EReal) ≤ f y := by
    intro y
    have h0 : psi y + (c : EReal) ≤ 0 + (c : EReal) := add_le_add (hpsi0 y) le_rfl
    rw [zero_add] at h0
    exact h0.trans (hfb y)
  have hlow : (fun y => psi y + (c : EReal)) ≤ w := hmax _ hshift hshift_le
  obtain ⟨C, hC⟩ := hw.exists_global_upper_bound
  intro x hx
  obtain ⟨N, hN, hb⟩ := hlocpsi x hx
  refine ⟨N, hN, isBoundedPotentialOn_of_le_of_le_const hlow hC ?_⟩
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨a + c, b + c, fun y hy => ⟨?_, ?_⟩⟩
  · show ((a + c : ℝ) : EReal) ≤ psi y + (c : EReal)
    rw [EReal.coe_add]
    exact add_le_add (hab y hy).1 le_rfl
  · show psi y + (c : EReal) ≤ ((b + c : ℝ) : EReal)
    rw [EReal.coe_add]
    exact add_le_add (hab y hy).2 le_rfl

/-- **Xia, SGPT, Lemma 2.4.3 with no residual set (big class).**  The
non-pluripolar Monge--Ampère measure of the largest `theta`-PSH potential `w`
below a lower semicontinuous obstacle bounded below gives no mass at all to
`{w < f}`.

This is Xia's Theorem 2.4.4 for a *lower semicontinuous* obstacle: the general
theorem takes a quasi-continuous obstacle and reduces it to this case through
his Step 2 (Tietze extensions of the small-capacity complements and
`h_j = sup_{k >= j} f_k`, which is lower semicontinuous). -/
theorem diagonalPotentialMeasure_lt_eq_zero_of_isBigClass (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f w : M → EReal} (hf : LowerSemicontinuous f)
    {c : ℝ} (hfb : ∀ y, (c : EReal) ≤ f y)
    (hwf : ∀ y, w y ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) :
    diagonalPotentialMeasure theta w hw {x | w x < f x} = 0 := by
  classical
  obtain ⟨psi, hpsi, hpsi0, -, hlocpsi⟩ := exists_normalized_reference_of_isBigClass hn theta hbig
  have hloc := exists_isBoundedPotentialOn_of_reference hpsi hpsi0 hlocpsi hfb hmax hw
  set mu := diagonalPotentialMeasure theta w hw with hmu
  have hnc : DoesNotChargeManifoldPluripolar (n := n) mu :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar (fun _ => hw.1)
  have hpoles : mu {x : M | psi x = ⊥} = 0 :=
    hnc _ (quasiPsh_poles_manifoldLocallyPluripolar hpsi.quasiPshPotential)
  have hgood : mu ({x : M | w x < f x} ∩ {x : M | psi x ≠ ⊥}) = 0 :=
    PatchBoundedNeighborhood.diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded
      hn hf hwf hmax hw (fun _ hx => hx.1) (fun x hx => hloc x hx.2)
  have hsub : {x : M | w x < f x} ⊆
      ({x : M | w x < f x} ∩ {x : M | psi x ≠ ⊥}) ∪ {x : M | psi x = ⊥} := by
    intro x hx
    by_cases hb : psi x = ⊥
    · exact Or.inr hb
    · exact Or.inl ⟨hx, hb⟩
  refine nonpos_iff_eq_zero.mp ?_
  calc mu {x : M | w x < f x}
      ≤ mu (({x : M | w x < f x} ∩ {x : M | psi x ≠ ⊥}) ∪ {x : M | psi x = ⊥}) :=
        measure_mono hsub
    _ ≤ mu ({x : M | w x < f x} ∩ {x : M | psi x ≠ ⊥}) + mu {x : M | psi x = ⊥} :=
        measure_union_le _ _
    _ = 0 := by rw [hgood, hpoles, add_zero]

/-- The same statement for the rooftop envelope itself: its maximality is
`FirstPass.le_rooftopEnvelope`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_isBigClass (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f : M → EReal} (hf : LowerSemicontinuous f)
    {c : ℝ} (hfb : ∀ y, (c : EReal) ≤ f y)
    (hwf : ∀ y, rooftopEnvelope theta.val f y ≤ f y)
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x | rooftopEnvelope theta.val f x < f x} = 0 :=
  diagonalPotentialMeasure_lt_eq_zero_of_isBigClass hn theta hbig hf hfb hwf
    (fun _ hv hvf => le_rooftopEnvelope hv (quasiEverywhere_of_forall hvf)) hw

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Xia, SGPT, Lemma 2.4.1 (`xia-sgpt:page-0074`), in the generality its own
consumer needs.**  For a big class, the largest `theta`-PSH potential below a
lower semicontinuous obstacle bounded below is locally bounded outside
`nK({theta})`.

Xia states it for `V_theta` and applies it to `P_theta(f)` in the proof of
Lemma 2.4.3; both are instances of the statement here, the first at the
obstacle `0`. -/
theorem exists_isBoundedPotentialOn_offNonKahlerLocus (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f w : M → EReal} {c : ℝ} (hfb : ∀ y, (c : EReal) ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w)
    {x : M} (hx : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta)) :
    ∃ N ∈ 𝓝 x, IsBoundedPotentialOn w N := by
  obtain ⟨psi, hpsi, hpsi0, hpole, hlocpsi⟩ :=
    exists_normalized_reference_of_isBigClass hn theta hbig
  refine exists_isBoundedPotentialOn_of_reference hpsi hpsi0 hlocpsi hfb hmax hw x ?_
  intro hb
  have hmem : x ∈ poleSet psi := hb
  rw [hpole] at hmem
  exact hx hmem

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Xia, SGPT, Lemma 2.4.1, literally.**  `V_theta` is locally bounded
outside `nK({theta})` for a big class. -/
theorem exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {x : M} (hx : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta)) :
    ∃ N ∈ 𝓝 x, IsBoundedPotentialOn (thetaPshSupremum theta.val) N :=
  exists_isBoundedPotentialOn_offNonKahlerLocus (f := fun _ => (0 : EReal)) hn theta hbig
    (c := 0) (fun _ => by simp) (fun _ hv hv0 => le_thetaPshSupremum hv hv0) hV hx

/-- **Xia, SGPT, Corollary 2.4.4 (big class), as the obstacle-`0` instance of
the lemma above.**  This is the workspace's only statement of Corollary 2.4.4
for a big class: the obstacle `0` is continuous, hence lower
semicontinuous, and bounded below by `0`, and `V_theta` is by definition the
largest `theta`-PSH potential below it. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_isBigClass (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
      {x | thetaPshSupremum theta.val x < 0} = 0 :=
  diagonalPotentialMeasure_lt_eq_zero_of_isBigClass (f := fun _ => (0 : EReal))
    hn theta hbig lowerSemicontinuous_const (c := 0) (fun _ => by simp)
    (fun y => thetaPshSupremum_le_zero theta.val y)
    (fun _ hv hv0 => le_thetaPshSupremum hv hv0) hV

end

end SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
