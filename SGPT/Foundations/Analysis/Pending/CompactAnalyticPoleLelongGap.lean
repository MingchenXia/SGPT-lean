import SGPT.Foundations.Analysis.Pending.AnalyticPoleLelongLowerBound
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

set_option autoImplicit false

/-! # Uniform analytic pole gaps and genuine ordinary restriction -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactAnalyticPoleLelongGap

open FirstPass FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation AnalyticPoleLelongLowerBound

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite cover of actual analytic germs internally produces one
positive real lower bound for every pole on the actual compact set. -/
theorem exists_pos_uniform_pole_lelong_lower_bound
    {S : Set M} (hS : IsCompact S) {u : M → EReal}
    (htype : ∀ x ∈ S, HasAnalyticSingularityTypeAt
      (chartFunction u (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, u x = ⊥ →
      ENNReal.ofReal δ ≤ lelongNumber (n := n) u x := by
  classical
  have hlocal : ∀ x : S, ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set M,
      IsOpen U ∧ x.val ∈ U ∧ ∀ y ∈ U, u y = ⊥ →
        ENNReal.ofReal δ ≤ lelongNumber (n := n) u y := by
    intro x
    obtain ⟨c, N, f, hlog⟩ := htype x.val x.property
    have hc : 0 < (c : ℝ) := hlog.1
    have hnear := eventually_ofReal_two_mul_le_lelongNumber_at_poles
      (complexChartAt (n := n) x.val) (mem_complexChartAt_source x.val) hlog
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
    exact ⟨2 * c, by positivity, U, hU, hxU, fun y hy => hUsub hy⟩
  choose δ hδ U hU hxU hbound using hlocal
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hfinite : ∀ t : Finset S, ∃ d : ℝ, 0 < d ∧ ∀ i ∈ t, d ≤ δ i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i t hi ih =>
      obtain ⟨d, hd, hdi⟩ := ih
      refine ⟨min (δ i) d, lt_min (hδ i) hd, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hdi j hj)
  obtain ⟨d, hd, hdi⟩ := hfinite s
  refine ⟨d, hd, ?_⟩
  intro x hx hxbot
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨his, hxU⟩ := mem_iUnion.mp hi
  exact (ENNReal.ofReal_le_ofReal (hdi i his)).trans (hbound i x hxU hxbot)

/-- Zero actual generic infimum and local analytic type on a compact target
internally produce a target point outside the pole set. -/
theorem exists_mem_ne_bot_of_generic_lelong_inf_eq_zero
    {S : Set M} (hS : IsCompact S) {u : M → EReal}
    (htype : ∀ x ∈ S, HasAnalyticSingularityTypeAt
      (chartFunction u (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x))
    (hgeneric : (⨅ x ∈ S, lelongNumber (n := n) u x) = 0) :
    ∃ x ∈ S, u x ≠ ⊥ := by
  classical
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_uniform_pole_lelong_lower_bound hS htype
  by_contra hnone
  have hpoles : ∀ x ∈ S, u x = ⊥ := by
    intro x hx
    by_contra hbot
    exact hnone ⟨x, hx, hbot⟩
  have hle : ENNReal.ofReal δ ≤ ⨅ x ∈ S, lelongNumber (n := n) u x :=
    le_iInf fun x => le_iInf fun hx => hbound x hx (hpoles x hx)
  rw [hgeneric] at hle
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hδ)) hle

/-- For a genuine compact connected target and any actual holomorphic map,
zero ambient generic infimum along its image supplies the missing local
nondegeneracy of the literal ordinary restriction. -/
theorem isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
    {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [CompactSpace V] [ConnectedSpace V] {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ.val u)
    (htype : ∀ x ∈ Set.range ι, HasAnalyticSingularityTypeAt
      (chartFunction u (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    IsThetaPshPotential (FirstPass.ClosedRealOneOneForm.pullback hι θ).val
      (fun y => u (ι y)) := by
  have hcompact : IsCompact (Set.range ι) := by
    simpa only [Set.image_univ] using isCompact_univ.image hι.continuous
  have hle : (⨅ x ∈ Set.range ι, lelongNumber (n := n) u x) ≤
      ⨅ y : V, lelongNumber (n := n) u (ι y) :=
    le_iInf fun y => iInf₂_le
      (f := fun x (_ : x ∈ Set.range ι) => lelongNumber (n := n) u x)
      (ι y) ⟨y, rfl⟩
  have hzero : (⨅ x ∈ Set.range ι, lelongNumber (n := n) u x) = 0 :=
    le_antisymm (by simpa only [hgeneric] using hle) zero_le
  obtain ⟨x, ⟨y, rfl⟩, hy⟩ :=
    exists_mem_ne_bot_of_generic_lelong_inf_eq_zero hcompact htype hzero
  exact ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
    (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hu) ⟨y, hy⟩

end

end SGPT.Foundations.Analysis.Pending.CompactAnalyticPoleLelongGap
