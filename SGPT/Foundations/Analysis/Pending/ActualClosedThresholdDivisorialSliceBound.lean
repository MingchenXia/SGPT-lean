import SGPT.Foundations.Analysis.Pending.DivisorialUniformFamilySliceBound

set_option autoImplicit false

/-! # The exact closed coefficient threshold of genuine slice bounds

The existing three-circle estimates have a finite constant independent of the
coefficient. Their affine endpoint therefore gives the exact coefficient,
including zero and pole values, without positive mass or a uniformity premise.
These are local ingredients, not an analytic-reference P/I identification.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualClosedThresholdDivisorialSliceBound

open FirstPass FirstPass.NonKahlerLocus DivisorialSliceBound
  DemaillyApproximantDivisorialLelong DivisorialUniformFamilySliceBound

noncomputable section

/-- The real coefficient may equal the actual point Lelong threshold; the
original finite bound supplies the uniform affine constant internally. -/
theorem le_log_last_add_of_le_lelongNumber {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} {Ω : Set (ComplexModel (m + 1))}
    (hu : PlurisubharmonicOn u Ω) {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall p (2 * r) ⊆ Ω) {K : ℝ}
    (hK : ∀ z ∈ closedBall p (2 * r), u z ≤ (K : EReal))
    {a : ℝ≥0}
    (hν : ∀ q ∈ ball p r, q (Fin.last m) = 0 →
      (a : ℝ≥0∞) ≤ lelongNumber (n := m + 1) u q)
    {z : ComplexModel (m + 1)} (hz : z ∈ ball p r)
    (hz0 : z (Fin.last m) ≠ 0) :
    u z ≤ (((a : ℝ) * Real.log ‖z (Fin.last m)‖ +
      (K - (a : ℝ) * Real.log r) : ℝ) : EReal) := by
  by_cases ha : a = 0
  · subst a
    simpa using hK z ((ball_subset_ball (by linarith : r ≤ 2 * r) hz)
      |> ball_subset_closedBall)
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ha)
  have hid : Tendsto (fun s : ℝ => s) (𝓝[<] (a : ℝ)) (𝓝 (a : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => ((s * Real.log ‖z (Fin.last m)‖ +
      (K - s * Real.log r) : ℝ) : EReal)) (𝓝[<] (a : ℝ))
      (𝓝 (((a : ℝ) * Real.log ‖z (Fin.last m)‖ +
        (K - (a : ℝ) * Real.log r) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr ((hid.mul_const _).add
      (tendsto_const_nhds.sub (hid.mul_const _)))
  apply ge_of_tendsto hlim
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (a : ℝ), 0 < s :=
    (eventually_gt_nhds ha0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs0 hs1
  let γ : ℝ≥0 := ⟨s, hs0.le⟩
  have hγa : γ < a := by exact_mod_cast hs1
  have hcoe : (γ : ℝ) = s := rfl
  simpa only [hcoe] using
    le_log_last_add_of_lt_lelongNumber hu hp hΩ hK
      (fun q hq hq0 => (ENNReal.coe_lt_coe.mpr hγa).trans_le (hν q hq hq0)) hz hz0

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- A single internally selected radius and finite constant work at every
finite closed threshold for the entire family, including its actual poles. -/
theorem exists_uniform_extended_slice_bound_of_le {I : Type*} [Nonempty I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal))
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ,
      ball (0 : ComplexModel (m + 1)) r ⊆ Φ.Φ.target ∧
      ∀ a : ℝ≥0, (∀ i, (a : ℝ≥0∞) ≤ divisorialLelongNumber m (u i) E) →
        ∀ i z, z ∈ ball (0 : ComplexModel (m + 1)) r →
          u i (Φ.point z) ≤ (((a : ℝ) / 2 : ℝ) : EReal) *
            logNormSq (z (Fin.last m)) + ((A - (a : ℝ) * Real.log r : ℝ) : EReal) := by
  obtain ⟨r, hr, A, hrt, hall⟩ := exists_uniform_extended_slice_bound hu hB Φ
  refine ⟨r, hr, max A B, hrt, ?_⟩
  intro a hν i z hz
  by_cases ha : a = 0
  · subst a
    simpa using (hB i (Φ.point z)).trans
      (EReal.coe_le_coe_iff.mpr (le_max_right A B))
  have ha0 : 0 < a := pos_iff_ne_zero.mpr ha
  have ha0real : 0 < (a : ℝ) := by exact_mod_cast ha0
  by_cases hz0 : z (Fin.last m) = 0
  · have hpoint : 0 < lelongNumber (n := m + 1) (u i) (Φ.point z) :=
      (ENNReal.coe_pos.mpr ha0).trans_le
        ((hν i).trans (divisorialLelongNumber_le (Φ.point_mem (hrt hz) hz0)))
    have hbot := eq_bot_of_lelongNumber_pos (Nat.succ_pos m) (hu i) hpoint
    rw [hbot, hz0, logNormSq_zero, EReal.coe_mul_bot_of_pos (by positivity)]
    exact bot_le
  have hlog : logNormSq (z (Fin.last m)) =
      ((2 * Real.log ‖z (Fin.last m)‖ : ℝ) : EReal) := by
    rw [logNormSq_of_ne_zero hz0, Real.log_pow]
    norm_num
  have heq : (((a : ℝ) / 2 : ℝ) : EReal) * logNormSq (z (Fin.last m)) +
      ((max A B - (a : ℝ) * Real.log r : ℝ) : EReal) =
      (((a : ℝ) * Real.log ‖z (Fin.last m)‖ +
        (max A B - (a : ℝ) * Real.log r) : ℝ) : EReal) := by
    rw [hlog, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring
  rw [heq]
  have hid : Tendsto (fun s : ℝ => s) (𝓝[<] (a : ℝ)) (𝓝 (a : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => ((s * Real.log ‖z (Fin.last m)‖ +
      (max A B - s * Real.log r) : ℝ) : EReal)) (𝓝[<] (a : ℝ))
      (𝓝 (((a : ℝ) * Real.log ‖z (Fin.last m)‖ +
        (max A B - (a : ℝ) * Real.log r) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr ((hid.mul_const _).add
      (tendsto_const_nhds.sub (hid.mul_const _)))
  apply ge_of_tendsto hlim
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (a : ℝ), 0 < s :=
    (eventually_gt_nhds ha0real).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs0 hs1
  let γ : ℝ≥0 := ⟨s, hs0.le⟩
  have hγ0 : 0 < γ := by exact_mod_cast hs0
  have hγa : γ < a := by exact_mod_cast hs1
  have hs := (hall γ hγ0 (fun j => (ENNReal.coe_lt_coe.mpr hγa).trans_le (hν j))
      i z hz).trans
    (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
      (sub_le_sub_right (le_max_left A B) ((γ : ℝ) * Real.log r))))
  rw [hlog, ← EReal.coe_mul, ← EReal.coe_add] at hs
  have hcoe : (γ : ℝ) = s := rfl
  have hreal : (γ : ℝ) / 2 * (2 * Real.log ‖z (Fin.last m)‖) +
      (max A B - (γ : ℝ) * Real.log r) =
      s * Real.log ‖z (Fin.last m)‖ + (max A B - s * Real.log r) := by
    rw [hcoe]
    ring
  rw [hreal] at hs
  exact hs

end
end SGPT.Foundations.Analysis.Pending.ActualClosedThresholdDivisorialSliceBound
