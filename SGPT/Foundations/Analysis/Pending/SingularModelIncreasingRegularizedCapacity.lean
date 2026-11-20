import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingCapacity
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof

set_option autoImplicit false

/-!
# Canonical gap capacity convergence at a regularized increasing supremum

An independent Dini adaptation of Lu's actual canonical-weight mechanism,
using actual negligible-set pluripolarity and pluripolar outer capacity.
This supplies the regularized-limit input for Xia SGPT PDF0127 increasing
energy continuity without a pointwise-limit or capacity-control premise.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedCapacity

open FirstPass FirstPass.PositiveClasses ThetaCapacity CapacityWeightedConvergence
open ThetaCapacityDecreasingConvergence RelativeEnergyIntegrability
open PluripolarCapacityZero PluripolarOuterCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
private theorem tendsto_capacity_of_antitone_quasiContinuous_off_outerZero
    (omega : KahlerBackground n M) {f : ℕ → M → ℝ} {Z : Set M}
    (hZ : OuterCapacityZero omega Z)
    (hq : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (f j))
    (ha : ∀ x, Antitone fun j => f j x)
    (hl : ∀ x, x ∉ Z → Tendsto (fun j => f j x) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity omega.form (fun _ => 0) {x | δ < f j x})
      atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have heps : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨G₀, hG₀o, hZG₀, hG₀c⟩ := hZ
    (ENNReal.ofReal (η.toReal / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  choose G hGo hGc hGf using fun j : ℕ => hq j
    (ENNReal.ofReal (η.toReal / 2 / 2 / 2 / 2 ^ j))
    (ENNReal.ofReal_pos.mpr (by positivity))
  let H := G₀ ∪ ⋃ j, G j
  have hHo : IsOpen H := hG₀o.union (isOpen_iUnion hGo)
  have hUnion : thetaCapacity omega.form (fun _ => 0) (⋃ j, G j) ≤
      ENNReal.ofReal (η.toReal / 2 / 2) := by
    refine (thetaCapacity_iUnion_le _ _ G).trans ?_
    refine (ENNReal.tsum_le_tsum fun j => (hGc j).le).trans ?_
    rw [tsum_ofReal_geometric_half (η.toReal / 2) (half_pos heps)]
  have hHc : thetaCapacity omega.form (fun _ => 0) H ≤ η := by
    calc
      _ ≤ thetaCapacity omega.form (fun _ => 0) G₀ +
          thetaCapacity omega.form (fun _ => 0) (⋃ j, G j) := thetaCapacity_union_le _ _ _ _
      _ ≤ ENNReal.ofReal (η.toReal / 4) + ENNReal.ofReal (η.toReal / 2 / 2) :=
        add_le_add hG₀c.le hUnion
      _ = ENNReal.ofReal (η.toReal / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ η := (ENNReal.ofReal_le_ofReal (by linarith)).trans
        (le_of_eq (ENNReal.ofReal_toReal htop))
  have hHf : ∀ j, ContinuousOn (f j) Hᶜ := fun j =>
    (hGf j).mono (compl_subset_compl.mpr (fun x hx =>
      Or.inr (mem_iUnion.mpr ⟨j, hx⟩)))
  obtain ⟨N, hN⟩ := exists_forall_lt_add_of_antitone_of_continuousOn
    hHo.isClosed_compl.isCompact hHf continuousOn_const
    (fun x _ => ha x) (fun x hx => hl x (fun hxZ => hx (Or.inl (hZG₀ hxZ)))) hδ
  filter_upwards [eventually_ge_atTop N] with j hj
  refine (thetaCapacity_mono ?_).trans hHc
  intro x hx
  by_contra hxH
  have h := hN j hj x hxH
  simp only [zero_add] at h
  exact (not_lt_of_ge h.le) hx

variable [ConnectedSpace M]

/-- Actual regularized increasing genuine suprema give canonical gap
capacity convergence; their raw-supremum deficit is internally pluripolar. -/
theorem tendsto_capacity_canonicalGap_of_monotone_regularized
    (omega : KahlerBackground n M) {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential omega.form.val (u j))
    (hv : IsThetaPshPotential omega.form.val v) (hm : ∀ x, Monotone fun j => u j x)
    (hv0 : v ≤ 0) (ht : SameSingularityTypeOn (u 0) v univ)
    (hreg : uscRegularization (⨆ j, u j) = v) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | δ < |canonicalERealDiffToReal (v x) (u j x)|}) atTop (𝓝 0) := by
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
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
  let Z := {x | ¬ v x ≤ (⨆ j, u j) x}
  have hQ := NegligibleSetsPluripolarProof.negligibleSetsPluripolar omega omega.form
    u 0 hu (fun j x => (huv j x).trans (hv0 x))
  rw [hreg] at hQ
  have hZ : OuterCapacityZero omega Z := outerCapacityZero_of_manifoldLocallyPluripolar omega hQ
  have hfl : ∀ x, x ∉ Z → Tendsto (fun j => f j x) atTop (𝓝 0) := by
    intro x hx
    have hSup : (⨆ j, u j x) = v x := le_antisymm (iSup_le fun j => huv j x)
      (by simpa only [Z, mem_ofPred_eq, not_not, iSup_apply] using hx)
    have hl : Tendsto (fun j => u j x) atTop (𝓝 (v x)) := by
      simpa only [hSup] using tendsto_atTop_iSup (hm x)
    by_cases hbot : v x = ⊥
    · have hz : (fun j => f j x) = fun _ => 0 := by
        funext j
        rw [hfr, hbot, (hp j x).mp hbot]
        simp
      rw [hz]
      exact tendsto_const_nhds
    · have hreal := (EReal.tendsto_toReal (hvt x) hbot).comp hl
      have hc : Tendsto (fun _ : ℕ => (v x).toReal) atTop (𝓝 ((v x).toReal)) :=
        tendsto_const_nhds
      simpa only [hfr, Function.comp_apply, sub_self] using hc.sub hreal
  have hq : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (f j) := fun j =>
    PoleCoalescingCapacity.quasiContinuousFor_canonicalWeight omega omega.isSemipositive
      hv (hu j) hv0 ((huv j).trans hv0) (htj j).symm
  have h := tendsto_capacity_of_antitone_quasiContinuous_off_outerZero omega hZ hq hfa hfl hδ
  simpa only [f, abs_of_nonneg (hnon _ _)] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedCapacity
