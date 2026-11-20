import SGPT.Foundations.Analysis.Pending.ThetaPshSupremumContact

set_option autoImplicit false

/-!
# `hloc` is exactly local boundedness

Xia's Lemma 2.4.3, as proved in
`Pending.PolydiskPatchBalayageContact.diagonalPotentialMeasure_lt_eq_zero`,
carries the hypothesis

  `∀ x ∈ S, ∃ P i, x ∈ P.source ∧ IsBoundedPotentialOn w P.source`,

a statement about the *patches* of `Pending.PatchLocalBoundedMeasure`.  What
Xia assumes (his Lemma 2.4.1) is the plain analytic statement that `w` is
locally bounded at each point of `S`.  The two are the same, and this module
proves it: a patch can always be shrunk inside a given neighbourhood without
disturbing its chart or its smooth corrections (`Patch.restrict`), and a patch
exists around every point (`exists_patch_containing`).

So every consumer of Lemma 2.4.3 may now discharge `hloc` by exhibiting one
two-sided bound on one neighbourhood, and the outstanding input of the three
Theorem 2.4.4 instances is visibly Xia's Lemma 2.4.1 and nothing about patches.

The dimension hypothesis `0 < n` is only used to produce a slot index `i : Fin
n`; it is also a hypothesis of Lemma 2.4.3 itself.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood

open FirstPass FirstPass.MongeAmpere
open FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {theta : ClosedRealOneOneForm n M} {w : M → EReal}

/-- **A bounded neighbourhood produces a bounded patch.**  Take any patch
around `x`, and shrink its coordinate domain to the part lying over the
neighbourhood; shrinking keeps the chart, the smooth corrections and the
plurisubharmonicity, so the result is still a patch. -/
theorem exists_patch_isBoundedPotentialOn
    (hw : ThetaPlurisubharmonic theta.val w) {x : M} {N : Set M} (hN : N ∈ 𝓝 x)
    (hb : IsBoundedPotentialOn w N) :
    ∃ P : Patch (fun _ : Fin n => theta) (fun _ => w),
      x ∈ P.source ∧ IsBoundedPotentialOn w P.source := by
  classical
  obtain ⟨U, hUN, hUopen, hxU⟩ := mem_nhds_iff.mp hN
  obtain ⟨P, hxP⟩ := exists_patch_containing (fun _ => hw) x
  refine ⟨P.restrict ⟨(P.domain : Set (ComplexModel n)) ∩
      (P.chart.val.target ∩ P.chart.val.symm ⁻¹' U),
      P.domain.isOpen.inter (P.chart.val.isOpen_inter_preimage_symm hUopen)⟩
    (fun _ hz => hz.1), ?_, ?_⟩
  · have hxsrc : x ∈ P.chart.val.source := P.source_subset hxP
    have hxdom : P.chart.val x ∈ P.domain := P.map_source hxP
    have hxU' : P.chart.val.symm (P.chart.val x) ∈ U := by
      rw [P.chart.val.left_inv hxsrc]; exact hxU
    exact ⟨hxsrc, hxdom, P.domain_le_target hxdom, hxU'⟩
  · refine hb.mono ?_
    intro y hy
    have hysrc : y ∈ P.chart.val.source := hy.1
    have hyU : P.chart.val.symm (P.chart.val y) ∈ U := hy.2.2.2
    rw [P.chart.val.left_inv hysrc] at hyU
    exact hUN hyU

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Xia, SGPT, Lemma 2.4.3, with `hloc` in Xia's own form.**  The
non-pluripolar Monge--Ampère measure of the largest `θ`-PSH potential `w` below
a lower semicontinuous obstacle `f` gives no mass to any subset of `{w < f}` on
which `w` is *locally bounded*. -/
theorem diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded (hn : 0 < n)
    {f : M → EReal} (hf : LowerSemicontinuous f)
    (hwf : ∀ y, w y ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (hS : ∀ x ∈ S, w x < f x)
    (hloc : ∀ x ∈ S, ∃ N ∈ 𝓝 x, IsBoundedPotentialOn w N) :
    diagonalPotentialMeasure theta w hw S = 0 := by
  refine diagonalPotentialMeasure_lt_eq_zero hn hf hwf hmax hw hS ?_
  intro x hx
  obtain ⟨N, hN, hb⟩ := hloc x hx
  obtain ⟨P, hxP, hbP⟩ := exists_patch_isBoundedPotentialOn hw.1 hN hb
  exact ⟨P, ⟨0, hn⟩, hxP, hbP⟩

/-- **Xia, SGPT, Corollary 2.4.4 for `V_theta`, with Xia's own hypothesis.**
`theta^n_{V_theta}` gives no mass to a set of points where `V_theta` is
strictly negative and locally bounded.  Together with Xia's Lemma 2.4.1 —
`V_theta` is locally bounded outside `nK({theta})` — and the fact that a proper
analytic subset is null for a non-pluripolar measure, this is the whole of
Corollary 2.4.4. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_locallyBounded
    (hn : 0 < n)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) {S : Set M}
    (hS : ∀ x ∈ S, thetaPshSupremum theta.val x < 0)
    (hloc : ∀ x ∈ S, ∃ N ∈ 𝓝 x,
      IsBoundedPotentialOn (thetaPshSupremum theta.val) N) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV S = 0 :=
  diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded (f := (0 : M → EReal))
    hn lowerSemicontinuous_const (fun y => thetaPshSupremum_le_zero theta.val y)
    (fun _ hv hv0 => le_thetaPshSupremum hv hv0) hV hS hloc

/-- **`V_theta` inherits local boundedness from any normalized reference below
it.**  `V_theta` is bounded above by `0` outright, so a lower bound for a
normalized `theta`-PSH competitor on a set is a two-sided bound for `V_theta`
there.  This is the mechanism of Xia's Lemma 2.4.1: the reference is the
potential of a Kähler current with analytic singularities, which is locally
bounded off its polar set `nK({theta})`. -/
theorem isBoundedPotentialOn_thetaPshSupremum_of_le {psi : M → EReal}
    (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0)
    {N : Set M} (hb : IsBoundedPotentialOn psi N) :
    IsBoundedPotentialOn (thetaPshSupremum theta.val) N := by
  obtain ⟨a, _b, hab⟩ := hb
  refine ⟨a, 0, fun x hx => ⟨(hab x hx).1.trans (le_thetaPshSupremum hpsi hpsi0 x), ?_⟩⟩
  simpa using thetaPshSupremum_le_zero theta.val x

/-- **Xia, SGPT, Corollary 2.4.4, reduced to Boucksom's theorem.**
`theta^n_{V_theta}` gives no mass to the set where `V_theta` is negative and
*some* normalized `theta`-PSH reference is locally bounded.  Xia's Lemma 2.4.1
is exactly the statement that such a reference — the potential of a Kähler
current with analytic singularities — is locally bounded off `nK({theta})`.

That reference exists only for a **big** class: Xia's Lemma 2.4.1
(`xia-sgpt:page-0074`) and Lemma 2.4.3 (`xia-sgpt:page-0079`) both open with the
bigness hypothesis, and so does Boucksom's theorem here
(`Pending.NonKahlerLocusPoleSetBounded`).  For a merely pseudo-effective class
`nK({theta})` can be all of `X` and no such `psi` exists.  The interface
`Pending.SingularityEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero`
carries no bigness hypothesis, so it is stated more strongly than Xia's theorem;
that discrepancy is I-0422 and is the human's call.  Nothing in this module
depends on it: `psi` is a hypothesis here, so the statements below are true as
written whatever `{theta}` is. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_reference (hn : 0 < n)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {psi : M → EReal} (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0)
    {S : Set M} (hS : ∀ x ∈ S, thetaPshSupremum theta.val x < 0)
    (hloc : ∀ x ∈ S, ∃ N ∈ 𝓝 x, IsBoundedPotentialOn psi N) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV S = 0 :=
  diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_locallyBounded hn hV hS
    fun x hx =>
      let ⟨N, hN, hb⟩ := hloc x hx
      ⟨N, hN, isBoundedPotentialOn_thetaPshSupremum_of_le hpsi hpsi0 hb⟩

/-- **Xia, SGPT, Corollary 2.4.4 on the whole negativity set, modulo one
existential.**  If some normalized `theta`-PSH reference `psi` is locally
bounded at every point off its own polar set, then `theta^n_{V_theta}` gives no
mass at all to `{V_theta < 0}`.

The polar set of a nondegenerate global quasi-PSH potential is locally
pluripolar, and a non-pluripolar product charges no locally pluripolar set, so
the poles of `psi` are discarded for free; away from them the previous theorem
applies.  Xia's Lemma 2.4.1 is precisely the existence of such a `psi` — the
potential of a Kähler current with analytic singularities, whose polar set is
`nK({theta})` (Boucksom; `Pending.NonKahlerLocusPoleSetBounded`). -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_reference_offPoles
    (hn : 0 < n)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {psi : M → EReal} (hpsi : IsThetaPshPotential theta.val psi) (hpsi0 : psi ≤ 0)
    (hlocbdd : ∀ x, psi x ≠ ⊥ → ∃ N ∈ 𝓝 x, IsBoundedPotentialOn psi N) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
      {x | thetaPshSupremum theta.val x < 0} = 0 := by
  classical
  set mu := diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV with hmu
  have hnc : DoesNotChargeManifoldPluripolar (n := n) mu :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar (fun _ => hV.1)
  have hpoles : mu {x : M | psi x = ⊥} = 0 :=
    hnc _ (quasiPsh_poles_manifoldLocallyPluripolar hpsi.quasiPshPotential)
  have hgood : mu ({x : M | thetaPshSupremum theta.val x < 0} ∩
      {x : M | psi x ≠ ⊥}) = 0 :=
    diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_reference hn hV hpsi hpsi0
      (fun _ hx => hx.1) (fun x hx => hlocbdd x hx.2)
  have hsub : {x : M | thetaPshSupremum theta.val x < 0} ⊆
      ({x : M | thetaPshSupremum theta.val x < 0} ∩ {x : M | psi x ≠ ⊥}) ∪
        {x : M | psi x = ⊥} := by
    intro x hx
    by_cases hb : psi x = ⊥
    · exact Or.inr hb
    · exact Or.inl ⟨hx, hb⟩
  refine nonpos_iff_eq_zero.mp ?_
  calc mu {x : M | thetaPshSupremum theta.val x < 0}
      ≤ mu (({x : M | thetaPshSupremum theta.val x < 0} ∩ {x : M | psi x ≠ ⊥}) ∪
          {x : M | psi x = ⊥}) := measure_mono hsub
    _ ≤ mu ({x : M | thetaPshSupremum theta.val x < 0} ∩ {x : M | psi x ≠ ⊥}) +
          mu {x : M | psi x = ⊥} := measure_union_le _ _
    _ = 0 := by rw [hgood, hpoles, add_zero]

end

end SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
