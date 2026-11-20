import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityDecreasingConvergence

set_option autoImplicit false

/-!
# Xia's Theorem 2.3.3 on a compact set where the data are bounded

`Pending.ThetaCapacityDecreasingConvergence.tendsto_thetaCapacity_of_antitone`
is Xia's Theorem 2.3.3 (`xia-sgpt:page-0063`, decreasing case) for globally
bounded potentials over a globally bounded reference — hypotheses that
`Pending.ThetaCapacityBoundedDegeneracy` shows cannot be met together once
`nK({theta})` is nonempty.

`Pending.ThetaCapacityLocalQuasiContinuity` removed that restriction from
Theorem 2.3.2, so the same proof now runs with all the bounds imposed on an
open set `Omega` only, the conclusion being about the sublevel sets intersected
with a compact `K subset Omega`:

  `Cap_theta(K ∩ {w + delta < u_k}, V) -> 0`.

Nothing in the argument changes: the exceptional sets come from the compact
form of Theorem 2.3.2, they are collected with a geometric tolerance by
countable subadditivity of `Cap_theta`, and Dini's theorem (unconditional, and
reused unchanged from the global module) upgrades the pointwise monotone
convergence off them to a uniform bound on the compact set `K \ G`.

This is the form Xia's Theorem 2.4.4 consumes: on `xia-sgpt:page-0081` the
limit `j -> infinity` is taken on `W <<- X \ nK({theta})`, never on `X`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityDecreasingConvergence
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **The quantitative step, localized.**  For every tolerance `eps > 0` there
is an open `G` of capacity at most `eps` and an index `N` beyond which
`K ∩ {w + delta < u_k}` is contained in `G`. -/
theorem exists_isOpen_forall_subset_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    {Omega : Set M} (hOmega : IsOpen Omega) (hVb : IsBoundedPotentialOn V Omega)
    {K : Set M} (hK : IsCompact K) (hKO : K ⊆ Omega)
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hub : ∀ k, IsBoundedPotentialOn (u k) Omega)
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotentialOn w Omega)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {delta : ℝ} (hdelta : 0 < delta) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G ≤ ENNReal.ofReal eps ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        K ∩ {x | w x + (delta : EReal) < u k x} ⊆ G := by
  classical
  obtain ⟨G₀, hG₀open, hG₀cap, hG₀cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn (V := V) hw hOmega hwb hVb
      hK hKO (eps := eps / 2 / 2 / 2 ^ (0 : ℕ)) (by positivity)
  choose Gu hGuopen hGucap hGucont using fun k : ℕ =>
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn (V := V) (hu k) hOmega
      (hub k) hVb hK hKO (eps := eps / 2 / 2 / 2 ^ (k + 1)) (by positivity)
  set E : ℕ → Set M := fun j => Nat.rec G₀ (fun k _ => Gu k) j with hE_def
  set G : Set M := ⋃ j, E j with hG_def
  have hGopen : IsOpen G := isOpen_iUnion fun j => by
    cases j with
    | zero => exact hG₀open
    | succ k => exact hGuopen k
  have hEcap : ∀ j, thetaCapacity theta V (E j) ≤
      ENNReal.ofReal (eps / 2 / 2 / 2 ^ j) := by
    intro j
    cases j with
    | zero => exact hG₀cap.le
    | succ k => exact (hGucap k).le
  have hGcap : thetaCapacity theta V G ≤ ENNReal.ofReal eps := by
    refine le_trans (thetaCapacity_iUnion_le theta V E) ?_
    refine le_trans (ENNReal.tsum_le_tsum hEcap) ?_
    rw [tsum_ofReal_geometric_half eps heps]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hKcompact : IsCompact (K \ G) := hK.diff hGopen
  have hsub0 : K \ G ⊆ K \ G₀ :=
    sdiff_subset_sdiff_right (le_iSup E 0)
  have hsubk : ∀ k, K \ G ⊆ K \ Gu k := fun k =>
    sdiff_subset_sdiff_right (le_iSup E (k + 1))
  have hcontw : ContinuousOn (fun y => (w y).toReal) (K \ G) := hG₀cont.mono hsub0
  have hcontu : ∀ k, ContinuousOn (fun y => (u k y).toReal) (K \ G) := fun k =>
    (hGucont k).mono (hsubk k)
  have hmemO : ∀ x ∈ K \ G, x ∈ Omega := fun x hx => hKO hx.1
  have hantiR : ∀ x ∈ K \ G, Antitone fun k => (u k x).toReal := by
    intro x hx j k hjk
    exact EReal.toReal_le_toReal (hanti x hjk) ((hub k).ne_bot (hmemO x hx))
      ((hub j).ne_top (hmemO x hx))
  have hlimR : ∀ x ∈ K \ G,
      Tendsto (fun k => (u k x).toReal) atTop (𝓝 ((w x).toReal)) := by
    intro x hx
    exact (EReal.tendsto_toReal (hwb.ne_top (hmemO x hx))
      (hwb.ne_bot (hmemO x hx))).comp (hlim x)
  obtain ⟨N, hN⟩ := exists_forall_lt_add_of_antitone_of_continuousOn hKcompact
    hcontu hcontw hantiR hlimR hdelta
  refine ⟨G, hGopen, hGcap, N, fun k hk x hx => ?_⟩
  by_contra hxG
  have hxK : x ∈ K \ G := ⟨hx.1, hxG⟩
  have hO : x ∈ Omega := hmemO x hxK
  have hlt : (u k x).toReal < (w x).toReal + delta := hN k hk x hxK
  have hwx : ((w x).toReal : EReal) = w x :=
    EReal.coe_toReal (hwb.ne_top hO) (hwb.ne_bot hO)
  have hux : ((u k x).toReal : EReal) = u k x :=
    EReal.coe_toReal ((hub k).ne_top hO) ((hub k).ne_bot hO)
  have hxmem : w x + (delta : EReal) < u k x := hx.2
  rw [← hwx, ← hux, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hxmem
  linarith

/-- **Xia, SGPT, Theorem 2.3.3, decreasing case, on a compact subset of an open
set where the data are bounded.**  A decreasing sequence of `theta`-PSH
potentials converges to its pointwise limit in `Cap_theta(-, V)` there. -/
theorem tendsto_thetaCapacity_of_antitone_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    {Omega : Set M} (hOmega : IsOpen Omega) (hVb : IsBoundedPotentialOn V Omega)
    {K : Set M} (hK : IsCompact K) (hKO : K ⊆ Omega)
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hub : ∀ k, IsBoundedPotentialOn (u k) Omega)
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotentialOn w Omega)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun k => thetaCapacity theta V
        (K ∩ {x | w x + (delta : EReal) < u k x})) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro eta heta
  rcases eq_or_ne eta ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  · have hreal : 0 < eta.toReal := ENNReal.toReal_pos heta.ne' htop
    obtain ⟨G, _, hGcap, N, hN⟩ :=
      exists_isOpen_forall_subset_of_boundedOn hOmega hVb hK hKO hu hub hw hwb
        hanti hlim hdelta hreal
    filter_upwards [eventually_ge_atTop N] with k hk
    refine le_trans (le_trans (thetaCapacity_mono (hN k hk)) hGcap) ?_
    rw [ENNReal.ofReal_toReal htop]

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalDecreasingConvergence
