import SGPT.Foundations.Analysis.Pending.BedfordTaylorCompactMassEquality
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit

set_option autoImplicit false

/-!
# Błocki's local comparison principle, the continuous case

Błocki, *The complex Monge--Ampère operator in pluripotential theory*, lecture
notes, Theorem 2.2.6 (p. 46): for a bounded domain `Ω ⊆ ℂⁿ` and `u, v` bounded
plurisubharmonic on `Ω` with `(u - v)^* ≥ 0` on `∂Ω`,

  `∫_{u < v} (ddᶜ v)ⁿ ≤ ∫_{u < v} (ddᶜ u)ⁿ`.

This is the input Xia's Proposition 1.2.10 -- the *local domination principle*,
the last missing link of the local half of Xia's Lemma 2.4.3 -- is reduced to by
Błocki's own Corollary 2.8 perturbation.

This file proves the first part of Błocki's proof: the case in which `u` and `v`
are continuous.  The boundary hypothesis enters only through its consequence,
which is what the statement below assumes: the contact set `O = {u < v}` is
*relatively compact* in `Ω` (Błocki obtains this by replacing `u` with `u + δ`,
so that `(u - v)^* ≥ δ > 0` on `∂Ω`).

The proof is Błocki's.  For `ε > 0` put `u_ε = max(u + ε, v)`.  Off the compact
set `{u + ε ≤ v} ⊆ O` one has `u_ε = u + ε`, so the local Stokes mass equality
`Pending.BedfordTaylor.measure_eq_of_eqOn_compl` gives

  `(ddᶜu_ε)ⁿ(O) = (ddᶜ(u + ε))ⁿ(O) = (ddᶜu)ⁿ(O)`,

a constant in `ε`.  On `O` the functions `u_ε` decrease to `max(u, v) = v`, so
their Bedford--Taylor measures converge vaguely on `O`
(`tendsto_integral_of_antitone_isBTLimit`), and the open-set portmanteau
inequality (`Pending.VaguePortmanteau.measure_le_liminf_of_tendsto_integral`)
gives `(ddᶜv)ⁿ(O) ≤ liminf (ddᶜu_ε)ⁿ(O) = (ddᶜu)ⁿ(O)`.

Continuity of `u` and `v` is used only to know that `O` is open and that
`{u + ε ≤ v}` is closed; the general case of Theorem 2.2.6 replaces it by
quasi-continuity with respect to the relative capacity, which is available in
this workspace as
`Pending.BedfordTaylorQuasiContinuity.IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_diff`
but is not used here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-! ## Two closure properties of the locally bounded plurisubharmonic class -/

/-- Adding a real constant preserves local boundedness and plurisubharmonicity. -/
theorem IsLocallyBoundedPshOn.add_const {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) (c : ℝ) :
    IsLocallyBoundedPshOn Ω fun z ↦ f z + c := by
  refine ⟨?_, fun z hz ↦ ?_⟩
  · have hc : PlurisubharmonicOn (fun _ : ComplexModel n ↦ ((c : ℝ) : EReal)) Ω :=
      fun x _ ↦ plurisubharmonicAt_const _ (EReal.coe_ne_top _) x
    simpa only [EReal.coe_add] using hf.1.add hc
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    refine ⟨V, hzV, hVΩ, C + |c|, fun y hy ↦ ?_⟩
    exact (abs_add_le _ _).trans (by linarith [hC y hy])

/-- The maximum of two locally bounded plurisubharmonic functions is locally bounded
plurisubharmonic. -/
theorem IsLocallyBoundedPshOn.max {Ω : Opens (ComplexModel n)}
    {f g : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f)
    (hg : IsLocallyBoundedPshOn Ω g) :
    IsLocallyBoundedPshOn Ω fun z ↦ max (f z) (g z) := by
  refine ⟨?_, fun z hz ↦ ?_⟩
  · simpa only [EReal.coe_strictMono.monotone.map_max] using hf.1.max hg.1
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    obtain ⟨V', hzV', -, C', hC'⟩ := hg.2 z hz
    refine ⟨V ⊓ V', ⟨hzV, hzV'⟩, inf_le_left.trans hVΩ, C ⊔ C', fun y hy ↦ ?_⟩
    exact abs_max_le_max_abs_abs.trans (max_le_max (hC y hy.1) (hC' y hy.2))

/-- Adding a real constant does not change the diagonal Bedford--Taylor limit. -/
theorem IsBTLimit.add_const_diag {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ ↦ u) μ) (c : ℝ) :
    IsBTLimit Ω (fun _ ↦ fun z ↦ u z + c) μ :=
  hμ.add_pluriharmonic fun _ ↦ isSmoothPluriharmonicOn_const Ω c

/-! ## The continuous case of Theorem 2.2.6 -/

/-- **Błocki's local comparison principle, continuous case** (lecture notes,
Theorem 2.2.6, first part).  Let `u, v` be locally bounded plurisubharmonic and
continuous on an open `Ω ⊆ ℂⁿ`, and suppose the contact set `O = {u < v}` is
relatively compact in `Ω` (the form in which the boundary hypothesis
`(u - v)^* ≥ δ > 0` on `∂Ω` is used).  Then the Monge--Ampère mass of `v` on `O`
does not exceed that of `u`. -/
theorem measure_lt_le_of_continuousOn
    {Ω O : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hcu : ContinuousOn u Ω) (hcv : ContinuousOn v Ω)
    (hO : (O : Set (ComplexModel n)) = {z | z ∈ (Ω : Set (ComplexModel n)) ∧ u z < v z})
    (hrc : RelativelyCompactIn O Ω)
    {μu μv : Measure (ComplexModel n)}
    (hμu : IsBTLimit Ω (fun _ ↦ u) μu) (hμv : IsBTLimit Ω (fun _ ↦ v) μv) :
    μv (O : Set (ComplexModel n)) ≤ μu (O : Set (ComplexModel n)) := by
  classical
  have hOΩ : O ≤ Ω := subset_closure.trans hrc.2
  have hOmeas : MeasurableSet (O : Set (ComplexModel n)) := O.isOpen.measurableSet
  -- the shifts
  set eps : ℕ → ℝ := fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1) with heps_def
  have heps_pos : ∀ k, 0 < eps k := fun k ↦ by
    simp only [heps_def]; positivity
  have heps_anti : Antitone eps := by
    intro k l hkl
    simp only [heps_def]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.cast_le.mpr (by omega : k + 1 ≤ l + 1)
  have heps_lim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the shifted maxima
  set w : ℕ → ComplexModel n → ℝ := fun k z ↦ max (u z + eps k) (v z) with hw_def
  have hwpsh : ∀ k, IsLocallyBoundedPshOn Ω (w k) := fun k ↦
    IsLocallyBoundedPshOn.max (IsLocallyBoundedPshOn.add_const hu (eps k)) hv
  choose muw hmuw using fun k ↦ exists_isBTLimit_of_isLocallyBoundedPshOn
    (Ω := Ω) (u := fun _ : Fin n ↦ w k) (fun _ ↦ hwpsh k)
  -- each shifted maximum carries the mass of `u` on `O`
  have hmass : ∀ k, muw k (O : Set (ComplexModel n)) = μu (O : Set (ComplexModel n)) := by
    intro k
    set K : Set (ComplexModel n) :=
      {z | z ∈ (Ω : Set (ComplexModel n)) ∧ u z + eps k ≤ v z} with hK_def
    have hKO : K ⊆ (O : Set (ComplexModel n)) := by
      intro z hz
      rw [hO]
      exact ⟨hz.1, by linarith [heps_pos k, hz.2]⟩
    have hclK : closure K ⊆ (Ω : Set (ComplexModel n)) :=
      (closure_mono hKO).trans hrc.2
    have hKcl : IsClosed K := by
      rw [← closure_subset_iff_isClosed]
      intro z hz
      have hzΩ : z ∈ (Ω : Set (ComplexModel n)) := hclK hz
      refine ⟨hzΩ, ?_⟩
      have hcont : ContinuousAt (fun y ↦ u y + eps k - v y) z :=
        (((hcu.add continuousOn_const).sub hcv)).continuousAt (Ω.isOpen.mem_nhds hzΩ)
      have hne : (𝓝[K] z).NeBot := mem_closure_iff_clusterPt.mp hz
      have htend : Tendsto (fun y ↦ u y + eps k - v y) (𝓝[K] z)
          (𝓝 (u z + eps k - v z)) := hcont.continuousWithinAt.tendsto
      have hle : u z + eps k - v z ≤ 0 :=
        le_of_tendsto htend (eventually_nhdsWithin_of_forall fun y hy ↦ by linarith [hy.2])
      linarith
    have hKcompact : IsCompact K :=
      IsCompact.of_isClosed_subset hrc.1 hKcl (subset_closure.trans (closure_mono hKO))
    have hEq : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ K → w k z = u z + eps k := by
      intro z hzΩ hzK
      have : ¬ (u z + eps k ≤ v z) := fun h ↦ hzK ⟨hzΩ, h⟩
      simp only [hw_def]
      exact max_eq_left (le_of_not_ge this)
    exact measure_eq_of_eqOn_compl (hwpsh k) (IsLocallyBoundedPshOn.add_const hu (eps k))
      hrc hKcompact hKO hEq (hmuw k) (hμu.add_const_diag (eps k))
  -- the shifted maxima decrease to `v` on `O`
  have hrestrict : ∀ f : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω f →
      IsLocallyBoundedPshOn O f := by
    intro f hf
    refine ⟨hf.1.mono hOΩ, fun z hz ↦ ?_⟩
    obtain ⟨V, hzV, -, C, hC⟩ := hf.2 z (hOΩ hz)
    exact ⟨V ⊓ O, ⟨hzV, hz⟩, inf_le_right, C, fun y hy ↦ hC y hy.1⟩
  have hwO : ∀ k, IsLocallyBoundedPshOn O (w k) := fun k ↦ hrestrict _ (hwpsh k)
  have hvO : IsLocallyBoundedPshOn O v := hrestrict _ hv
  have hanti : ∀ z ∈ O, Antitone fun k ↦ w k z := by
    intro z _ k l hkl
    simp only [hw_def]
    exact max_le_max (by linarith [heps_anti hkl]) le_rfl
  have hlim : ∀ z ∈ O, Tendsto (fun k ↦ w k z) atTop (𝓝 (v z)) := by
    intro z hz
    have hzlt : u z < v z := by
      have hz' : z ∈ (O : Set (ComplexModel n)) := hz
      rw [hO] at hz'
      exact hz'.2
    have h1 : Tendsto (fun k ↦ u z + eps k) atTop (𝓝 (u z)) := by
      simpa using tendsto_const_nhds.add heps_lim
    have h2 : Tendsto (fun k ↦ max (u z + eps k) (v z)) atTop (𝓝 (max (u z) (v z))) :=
      (continuous_id.max continuous_const).continuousAt.tendsto.comp h1
    rw [max_eq_right hzlt.le] at h2
    exact h2
  have hmuwO : ∀ k, IsBTLimit O (fun _ ↦ w k)
      ((muw k).restrict (O : Set (ComplexModel n))) := fun k ↦ (hmuw k).restrict_opens hOΩ
  have hμvO : IsBTLimit O (fun _ ↦ v) (μv.restrict (O : Set (ComplexModel n))) :=
    hμv.restrict_opens hOΩ
  -- the open-set portmanteau inequality
  have hport := VaguePortmanteau.measure_le_liminf_of_tendsto_integral
    (μs := fun k ↦ (muw k).restrict (O : Set (ComplexModel n)))
    (μ := μv.restrict (O : Set (ComplexModel n)))
    (Ω := (O : Set (ComplexModel n))) (O := (O : Set (ComplexModel n)))
    O.isOpen le_rfl (fun k _ hKc hKO ↦ (hmuwO k).2.1 _ hKc hKO)
    (fun _ hKc hKO ↦ hμvO.2.1 _ hKc hKO)
    (fun φ hφ hφc hφO ↦ tendsto_integral_of_antitone_isBTLimit hwO hvO hanti hlim
      hmuwO hμvO hφ hφc hφO)
  -- read off the masses
  have hself : ∀ ρ : Measure (ComplexModel n),
      ρ.restrict (O : Set (ComplexModel n)) (O : Set (ComplexModel n)) =
        ρ (O : Set (ComplexModel n)) := by
    intro ρ
    rw [Measure.restrict_apply hOmeas, inter_self]
  rw [hself μv] at hport
  simp only [hself] at hport
  calc μv (O : Set (ComplexModel n)) ≤ liminf (fun k ↦ muw k (O : Set (ComplexModel n))) atTop :=
        hport
    _ = μu (O : Set (ComplexModel n)) := by
        simp only [hmass]
        exact liminf_const _

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
