import SGPT.Foundations.Analysis.Pending.PshBallDeficitComparison
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false

/-!
# Antitone families of theta-PSH potentials with suprema bounded below

`Pending.ThetaPshDecreasingLimit` proves that a pointwise decreasing sequence of
`θ`-PSH functions has a `θ`-PSH infimum, *unconditionally*: the infimum is
allowed to be identically `-∞`.  This module proves the classical
nondegeneracy criterion that rules that out.

## The statement

If `(w_j)` is a pointwise antitone sequence of genuine `θ`-PSH potentials on a
compact `M` and there is one real `C` with `sup_M w_j ≥ -C` for every `j`, then
`inf_j w_j` is not identically `-∞`.  The hypothesis is recorded in the form
`∀ j, ∃ x, -C ≤ w_j x`, which is what an upper semicontinuous function attaining
its supremum on a compact space supplies, and which is what the proof below
consumes.

## The proof

This is the standard compactness ("Hartogs") property of quasi-plurisubharmonic
functions on a compact manifold, and it is proved here from the project's own
ball-deficit machinery rather than assumed.

Write `x_j` for a point with `w_j x_j ≥ -C`.  Compactness of `M` gives a cluster
point `p` of the sequence `(x_j)`, so `x_j` lies in *any* fixed neighbourhood of
`p` for cofinally many `j`.  Fix the chart `e` at `p`, put `z₀ = e p`, and take
the smooth local potential `ρ` of `θ` supplied by the *first* member of the
family on a neighbourhood `W` of `z₀`; by
`ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic`
that one potential tests every member, so `v_j := w_j ∘ e.symm + ρ` is honestly
plurisubharmonic on `W` for every `j`.  Choose `R' > 0` with
`closedBall z₀ R' ⊆ W` and set `r = R'/3`.

* `v_0` is bounded above by some `A` on `closedBall z₀ R'`, hence so is every
  `v_j`, by antitonicity.
* `ρ` is continuous, hence bounded below by some `P` on the same compact set.
* For a cofinal set of `j` the point `a_j = e x_j` lies in `ball z₀ r`, and
  there `v_j a_j = w_j x_j + ρ a_j ≥ -C + P`, so the *pointwise* deficit
  `(A - v_j a_j)⁺` is at most the fixed finite constant `A + C - P`.
* The Harnack form of the submean inequality,
  `PshBallDeficitComparison.deficitInt_le_of_near_center`, therefore bounds
  `∫ (A - v_j)⁺` over the fixed ball `ball z₀ r` by
  `vol (ball 0 (2r)) · (A + C - P)` — a bound independent of `j`.
* The deficits increase with `j`, so that bound holds for *every* `j`, not only
  the cofinal ones, and monotone convergence transfers it to their pointwise
  supremum.

If the infimum were identically `-∞`, that supremum would be `+∞` at every point
of a ball of positive measure, so the integral would be `+∞`: a contradiction.
No normalisation of `w_j` and no `toReal` truncation is used; poles are carried
throughout as the value `⊥`.

## Degenerate cases

* `n = 0`: `M` is a compact discrete space, hence finite; the proof above still
  runs (the "ball" is the whole one-point model and carries positive mass).
* `M` empty: the hypothesis `∀ j, ∃ x, -C ≤ w_j x` is unsatisfiable, so nothing
  is claimed; the proof extracts `Nonempty M` from it.
* Poles: each `w_j` may be `-∞` on a pluripolar set — `IsThetaPshPotential`
  only forbids being locally identically `-∞` — and the *infimum* is allowed to
  be `-∞` everywhere; ruling that out is the whole content.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate

open FirstPass

noncomputable section

/-- **Deficits blow up along a family whose infimum is `⊥`.**  Below a fixed
finite level `C` the nonnegative deficits `(C - f j)⁺` have supremum `⊤` as soon
as `⨅ j, f j = ⊥`.  No monotonicity and no upper bound on `f` are needed. -/
theorem iSup_deficit_eq_top_of_iInf_eq_bot {f : ℕ → EReal} (C : ℝ)
    (hbot : (⨅ j, f j) = ⊥) :
    (⨆ j, ((C : EReal) - f j).toENNReal) = ⊤ := by
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  refine iSup_le fun N => ?_
  set a : ℝ := C - (N : ℝ) with ha
  have hlt : (⨅ j, f j) < (a : EReal) := by
    rw [hbot]; exact EReal.bot_lt_coe a
  obtain ⟨j, hj⟩ := iInf_lt_iff.mp hlt
  refine le_trans ?_ (le_iSup (fun j => ((C : EReal) - f j).toENNReal) j)
  have hstep : ((C : EReal) - (a : EReal)) ≤ (C : EReal) - f j :=
    EReal.sub_le_sub le_rfl hj.le
  have hval : ((C : EReal) - (a : EReal)) = (((N : ℝ)) : EReal) := by
    rw [← EReal.coe_sub, ha]; norm_num
  have hmono := EReal.toENNReal_le_toENNReal (hval ▸ hstep)
  rwa [EReal.real_coe_toENNReal, ENNReal.ofReal_natCast] at hmono

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **Compactness of `PSH(X, θ)` ("Hartogs").**  An antitone sequence of
`θ`-PSH potentials whose suprema stay above one finite level has an infimum
that is finite somewhere.

See the module docstring for the shape of the argument. -/
theorem exists_ne_bot_iInf_of_forall_exists_le
    {theta : SmoothRealForm n M 2} {w : ℕ → M → EReal}
    (hw : ∀ j, IsThetaPshPotential theta (w j))
    (hanti : ∀ x : M, Antitone fun j => w j x)
    {C : ℝ} (hC : ∀ j, ∃ x : M, ((-C : ℝ) : EReal) ≤ w j x) :
    ∃ x : M, (⨅ j, w j x) ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  choose xs hxs using hC
  have : Nonempty M := ⟨xs 0⟩
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (Filter.map xs Filter.atTop)
  have hmcp : MapClusterPt p Filter.atTop xs := hp
  set e : ComplexChart n M := complexChartAt (n := n) p with he
  have hpsrc : p ∈ e.val.source := mem_complexChartAt_source p
  set z0 : ComplexModel n := e.val p with hz0def
  have hz0 : z0 ∈ e.val.target := e.val.map_source hpsrc
  obtain ⟨W, rho, hz0W, hrho, -⟩ := (hw 0).1 e z0 hz0
  set v : ℕ → ComplexModel n → EReal :=
    fun j y => chartFunction (w j) e y + (rho y : EReal) with hvdef
  have hvdisc : ∀ j, DiscPshOn (v j) W := fun j =>
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      (hw j).1 e hrho).discPshOn
  -- a closed ball inside `W`, and the working radius
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.mp hrho.1 z0 hz0W
  set R' : ℝ := R / 2 with hR'def
  have hR' : 0 < R' := by positivity
  have hcballW : closedBall z0 R' ⊆ W := fun y hy =>
    hRW (by
      rw [mem_closedBall] at hy
      exact mem_ball.mpr (lt_of_le_of_lt hy (by rw [hR'def]; linarith)))
  have hballW : ball z0 R' ⊆ W := ball_subset_closedBall.trans hcballW
  set r : ℝ := R' / 3 with hrdef
  have hr : 0 < r := by positivity
  -- a uniform upper bound for the whole family on the closed ball
  obtain ⟨A, hA⟩ := (hvdisc 0).exists_compact_upper_bound (isCompact_closedBall z0 R')
    ⟨z0, mem_closedBall_self hR'.le⟩ hcballW
  have hvle : ∀ j, ∀ y : ComplexModel n, v j y ≤ v 0 y := by
    intro j y
    exact add_le_add (hanti (e.val.symm y) (Nat.zero_le j)) le_rfl
  have hAj : ∀ j, ∀ y ∈ ball z0 R', v j y ≤ (A : EReal) := fun j y hy =>
    (hvle j y).trans (hA y (ball_subset_closedBall hy))
  -- a uniform lower bound for the smooth potential on the same ball
  obtain ⟨y0, hy0, hy0min⟩ := (isCompact_closedBall z0 R').exists_isMinOn
    ⟨z0, mem_closedBall_self hR'.le⟩ ((hrho.2.2.1.continuousOn).mono hcballW)
  set P : ℝ := rho y0 with hPdef
  have hPle : ∀ y ∈ closedBall z0 R', P ≤ rho y := fun y hy => hy0min hy
  -- the chart neighbourhood in which the near-maximizers cluster
  set Nb : Set M := e.val.source ∩ e.val ⁻¹' (ball z0 r) with hNbdef
  have hNopen : IsOpen Nb :=
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source isOpen_ball
  have hpN : p ∈ Nb :=
    ⟨hpsrc, show e.val p ∈ ball z0 r by rw [← hz0def]; exact mem_ball_self hr⟩
  have hfreq : ∃ᶠ j in Filter.atTop, xs j ∈ Nb :=
    mapClusterPt_iff_frequently.mp hmcp Nb (hNopen.mem_nhds hpN)
  -- the uniform bound on the deficit integral over the fixed small ball
  set D : ℝ≥0∞ := ENNReal.ofReal (A + C - P) with hDdef
  set Kb : ℝ≥0∞ := volume (ball (0 : ComplexModel n) (2 * r)) * D with hKdef
  have hKlt : Kb < ⊤ :=
    ENNReal.mul_lt_top
      (measure_ball_lt_top (μ := (volume : Measure (ComplexModel n)))
        (x := (0 : ComplexModel n)) (r := 2 * r))
      ENNReal.ofReal_lt_top
  have hgood : ∀ j, xs j ∈ Nb →
      ∫⁻ z in ball z0 r, ((A : EReal) - v j z).toENNReal ∂volume ≤ Kb := by
    intro j hj
    have haj : e.val (xs j) ∈ ball z0 r := hj.2
    have hdist : ‖e.val (xs j) - z0‖ ≤ r := by
      have hb := mem_ball.mp haj
      rw [dist_eq_norm] at hb
      exact hb.le
    have hR3 : ((1 : ℝ) + 2) * r ≤ R' := by rw [hrdef]; linarith
    have hkey := PshBallDeficitComparison.deficitInt_le_of_near_center
      (μ := volume) (u := v j) (p := z0) (R := R')
      ((hvdisc j).mono hballW) (hAj j) (r := r) (K := 1) hR3 hdist
    have h1 : (1 : ℝ) * r = r := one_mul r
    have h2 : ((1 : ℝ) + 1) * r = 2 * r := by ring
    rw [h1, h2] at hkey
    refine hkey.trans (mul_le_mul' (le_refl _) ?_)
    -- the pointwise deficit at the near-maximizer is bounded
    have hinv : e.val.symm (e.val (xs j)) = xs j := e.val.left_inv hj.1
    have hvval : v j (e.val (xs j)) = w j (xs j) + ((rho (e.val (xs j)) : ℝ) : EReal) := by
      simp only [hvdef, chartFunction, hinv]
    have hPa : P ≤ rho (e.val (xs j)) :=
      hPle _ (ball_subset_closedBall (ball_subset_ball (by rw [hrdef]; linarith) haj))
    have hlow : (((-C + P : ℝ)) : EReal) ≤ v j (e.val (xs j)) := by
      rw [hvval, EReal.coe_add]
      exact add_le_add (hxs j) (EReal.coe_le_coe_iff.mpr hPa)
    have hsub : ((A : EReal) - v j (e.val (xs j))) ≤ (((A + C - P : ℝ)) : EReal) := by
      have := EReal.sub_le_sub (le_refl ((A : ℝ) : EReal)) hlow
      refine this.trans ?_
      rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    have := EReal.toENNReal_le_toENNReal hsub
    rwa [EReal.real_coe_toENNReal] at this
  -- the deficit is monotone in the index, so the bound holds for every index
  have hdmono : ∀ z : ComplexModel n,
      Monotone fun j => ((A : EReal) - v j z).toENNReal := by
    intro z j k hjk
    refine EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl ?_)
    exact add_le_add (hanti (e.val.symm z) hjk) le_rfl
  have hrR' : r ≤ R' := by rw [hrdef]; linarith
  have hsmall : ball z0 r ⊆ W := (ball_subset_ball hrR').trans hballW
  have hall : ∀ j, ∫⁻ z in ball z0 r, ((A : EReal) - v j z).toENNReal ∂volume ≤ Kb := by
    intro j
    obtain ⟨k, hjk, hk⟩ := hfreq.forall_exists_of_atTop j
    exact le_trans (lintegral_mono fun z => hdmono z hjk) (hgood k hk)
  have hmeas : ∀ j, AEMeasurable (fun z => ((A : EReal) - v j z).toENNReal)
      (volume.restrict (ball z0 r)) := fun j =>
    (hvdisc j).aemeasurable_deficit_restrict measurableSet_ball hsmall A volume
  have hsup := MeasureTheory.lintegral_iSup'
    (μ := (volume : Measure (ComplexModel n)).restrict (ball z0 r))
    (f := fun j z => ((A : EReal) - v j z).toENNReal) hmeas
    (Filter.Eventually.of_forall fun z => hdmono z)
  -- the pointwise supremum of the deficits is identically ⊤
  have hbotv : ∀ z : ComplexModel n, (⨅ j, v j z) = ⊥ := by
    intro z
    have h1 : (⨅ j, chartFunction (w j) e z) = ⊥ := hcon (e.val.symm z)
    calc (⨅ j, v j z) = (⨅ j, chartFunction (w j) e z) + ((rho z : ℝ) : EReal) :=
          ThetaPshDecreasingLimit.iInf_add_coe _ _
      _ = ⊥ := by rw [h1]; exact EReal.bot_add _
  have htop : ∀ z : ComplexModel n, (⨆ j, ((A : EReal) - v j z).toENNReal) = ⊤ :=
    fun z => iSup_deficit_eq_top_of_iInf_eq_bot A (hbotv z)
  have hLHS : ∫⁻ z in ball z0 r, (⨆ j, ((A : EReal) - v j z).toENNReal) ∂volume = ⊤ := by
    rw [lintegral_congr fun z => htop z, setLIntegral_const]
    exact ENNReal.top_mul (measure_ball_pos volume z0 hr).ne'
  rw [hLHS] at hsup
  have hfin : (⊤ : ℝ≥0∞) ≤ Kb := by rw [hsup]; exact iSup_le hall
  exact hKlt.ne (top_le_iff.mp hfin)

/-- **The contrapositive the Step-1.3 contradiction consumes.**  If the
infimum of an antitone family of `θ`-PSH potentials is identically `-∞`, then
the family is eventually below *every* finite level, uniformly on `M`.

Proved from the theorem above; the `Antitone` hypothesis is not used here, but
is kept so that the two statements share their hypotheses. -/
theorem exists_forall_le_of_forall_iInf_eq_bot
    {theta : SmoothRealForm n M 2} {w : ℕ → M → EReal}
    (hw : ∀ j, IsThetaPshPotential theta (w j))
    (hanti : ∀ x : M, Antitone fun j => w j x)
    (hbot : ∀ x : M, (⨅ j, w j x) = ⊥) (C : ℝ) :
    ∃ j, ∀ x : M, w j x ≤ ((-C : ℝ) : EReal) := by
  by_contra hcon
  have hC : ∀ j, ∃ x : M, ((-C : ℝ) : EReal) ≤ w j x := fun j => by
    by_contra hj
    exact hcon ⟨j, fun x => not_lt.mp fun hlt => hj ⟨x, hlt.le⟩⟩
  obtain ⟨x, hx⟩ := exists_ne_bot_iInf_of_forall_exists_le hw hanti (C := C) hC
  exact hx (hbot x)

end

end SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
