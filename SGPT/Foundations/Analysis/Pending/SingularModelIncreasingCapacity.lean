import SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityDecreasingConvergence

set_option autoImplicit false

/-!
# Actual increasing same-type gap convergence in capacity

An independently proved Dini consequence of actual countable capacity
subadditivity and unbounded canonical-weight quasicontinuity, supplying the
same-type increasing energy input. This is an independent Dini adaptation
using the actual canonical-weight mechanism of Lu, Theorem 4.1 Step 1.2;
general finite-energy truncation tails are separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingCapacity

open FirstPass FirstPass.PositiveClasses ThetaCapacity CapacityWeightedConvergence
open ThetaCapacityDecreasingConvergence
open RelativeEnergyIntegrability

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- Actual countable capacity subadditivity and quasicontinuity produce
capacity convergence of a decreasing real sequence with pointwise limit zero. -/
theorem tendsto_capacity_of_antitone_quasiContinuous
    {θ : ClosedRealOneOneForm n M} {V : M → EReal} {f : ℕ → M → ℝ}
    (hq : ∀ j, QuasiContinuousFor (thetaCapacity θ V) (f j))
    (ha : ∀ x, Antitone fun j => f j x)
    (hl : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity θ V {x | δ < f j x}) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have heps : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  choose G hGo hGc hGf using fun j : ℕ => hq j
    (ENNReal.ofReal (η.toReal / 2 / 2 / 2 ^ j))
    (ENNReal.ofReal_pos.mpr (by positivity))
  let H : Set M := ⋃ j, G j
  have hHo : IsOpen H := isOpen_iUnion hGo
  have hHc : thetaCapacity θ V H ≤ η := by
    refine (thetaCapacity_iUnion_le θ V G).trans ?_
    refine (ENNReal.tsum_le_tsum fun j => (hGc j).le).trans ?_
    rw [tsum_ofReal_geometric_half η.toReal heps]
    refine (ENNReal.ofReal_le_ofReal (show η.toReal / 2 ≤ η.toReal by linarith)).trans ?_
    exact le_of_eq (ENNReal.ofReal_toReal htop)
  have hHf : ∀ j, ContinuousOn (f j) Hᶜ := fun j =>
    (hGf j).mono (compl_subset_compl.mpr (le_iSup G j))
  obtain ⟨N, hN⟩ := exists_forall_lt_add_of_antitone_of_continuousOn
    hHo.isClosed_compl.isCompact hHf continuousOn_const
    (fun x _ => ha x) (fun x _ => hl x) hδ
  filter_upwards [eventually_ge_atTop N] with j hj
  refine (thetaCapacity_mono ?_).trans hHc
  intro x hx
  by_contra hxH
  have h := hN j hj x hxH
  simp only [zero_add] at h
  exact (not_lt_of_ge h.le) hx

/-- Genuine increasing same-type potentials supply actual canonical-gap
capacity convergence, including the canonical zero values on common poles. -/
theorem tendsto_capacity_canonicalGap_of_monotone
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    (hθ : θ.val.IsSemipositive) {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (hv : IsThetaPshPotential θ.val v) (hm : ∀ x, Monotone fun j => u j x)
    (huv : ∀ j, u j ≤ v) (hv0 : v ≤ 0)
    (ht : SameSingularityTypeOn (u 0) v univ)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity θ (fun _ => 0)
      {x | δ < |canonicalERealDiffToReal (v x) (u j x)|}) atTop (𝓝 0) := by
  have htj : ∀ j, SameSingularityTypeOn (u j) v univ := fun j =>
    ⟨MoreSingularOn.of_le fun x _ => huv j x,
      ht.2.trans (MoreSingularOn.of_le fun x _ => hm x (Nat.zero_le j))⟩
  have hp : ∀ j x, v x = ⊥ ↔ u j x = ⊥ := fun j x =>
    (sameSingularityTypeOn_eq_bot_iff (htj j) (mem_univ x)).symm
  have hvt : ∀ x, v x ≠ ⊤ := hv.1.quasiPlurisubharmonic.ne_top
  have hut : ∀ j x, u j x ≠ ⊤ := fun j => (hu j).1.quasiPlurisubharmonic.ne_top
  let f : ℕ → M → ℝ := fun j x => canonicalERealDiffToReal (v x) (u j x)
  have hfr : ∀ j x, f j x = (v x).toReal - (u j x).toReal := fun j x =>
    canonicalDiff_eq_sub_toReal (hvt x) (hut j x) (hp j x)
  have hnon : ∀ j x, 0 ≤ f j x := by
    intro j x
    rw [hfr]
    by_cases hbot : v x = ⊥
    · rw [hbot, (hp j x).mp hbot]
      simp
    · have hjbot : u j x ≠ ⊥ := fun h => hbot ((hp j x).mpr h)
      exact sub_nonneg.mpr (EReal.toReal_le_toReal (huv j x) hjbot (hvt x))
  have hfa : ∀ x, Antitone fun j => f j x := by
    intro x j k hjk
    change f k x ≤ f j x
    rw [hfr, hfr]
    by_cases hbot : v x = ⊥
    · rw [(hp j x).mp hbot, (hp k x).mp hbot]
    · have hjbot : u j x ≠ ⊥ := fun h => hbot ((hp j x).mpr h)
      exact sub_le_sub_left (EReal.toReal_le_toReal (hm x hjk) hjbot (hut k x)) _
  have hfl : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 0) := by
    intro x
    by_cases hbot : v x = ⊥
    · have hz : (fun j => f j x) = fun _ => 0 := by
        funext j
        rw [hfr, hbot, (hp j x).mp hbot]
        simp
      rw [hz]
      exact tendsto_const_nhds
    · have hreal := (EReal.tendsto_toReal (hvt x) hbot).comp (hl x)
      have hc : Tendsto (fun _ : ℕ => (v x).toReal) atTop (𝓝 ((v x).toReal)) :=
        tendsto_const_nhds
      simpa only [hfr, Function.comp_apply, sub_self] using hc.sub hreal
  have hq : ∀ j, QuasiContinuousFor (thetaCapacity θ (fun _ => 0)) (f j) := fun j =>
    PoleCoalescingCapacity.quasiContinuousFor_canonicalWeight omega hθ hv (hu j)
      hv0 ((huv j).trans hv0) (htj j).symm
  have h := tendsto_capacity_of_antitone_quasiContinuous hq hfa hfl hδ
  simpa only [f, abs_of_nonneg (hnon _ _)] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingCapacity
