import SGPT.Foundations.Analysis.Pending.FiniteGeodesicSingularBarriers
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsTimeConvexity
import Mathlib.Analysis.Convex.Slope

set_option autoImplicit false

/-!
# Actual finite-gap time increments of singular Perron geodesics

Xia SGPT PDF0172's affine-barrier and convexity argument, adapted to
actual genuine same-type singular potentials and their common poles.
Actual adjacent secant slopes and the explicit endpoint limits give
the finite time bound, without a bounded model or energy affinity.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularGeodesicUniformTimeBounds

open FirstPass FiniteGeodesicSingularBarriers

noncomputable section

private theorem abs_sub_le_of_convex_endpoint_barriers {f : ℝ → ℝ} {a b C : ℝ}
    (hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) f)
    (hbar : ∀ r ∈ Ioo (0 : ℝ) 1, |f r - a| ≤ C * r ∧ |f r - b| ≤ C * (1 - r))
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    |f t - f s| ≤ C * |t - s| := by
  have key : ∀ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 → s < t →
      |f t - f s| ≤ C * (t - s) := by
    intro s t hs ht hst
    have hl : ∀ r ∈ Ioo (0 : ℝ) s,
        -C * (s + r) / (s - r) ≤ (f t - f s) / (t - s) := by
      intro r hr
      have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hs.2⟩
      have hmono := hconv.slope_mono_adjacent hr1 ht hr.2 hst
      have hbound : -C * (s + r) / (s - r) ≤ (f s - f r) / (s - r) := by
        apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hr.2.le)
        have hrb := abs_le.mp (hbar r hr1).1
        have hsb := abs_le.mp (hbar s hs).1
        linarith
      exact hbound.trans hmono
    have hltend : Tendsto (fun r : ℝ => -C * (s + r) / (s - r)) (𝓝[>] (0 : ℝ)) (𝓝 (-C)) := by
      have hc : ContinuousAt (fun r : ℝ => -C * (s + r) / (s - r)) 0 :=
        (continuous_const.mul (continuous_const.add continuous_id)).continuousAt.div
          (continuous_const.sub continuous_id).continuousAt (by simpa using hs.1.ne')
      have hzero : -C * (s + 0) / (s - 0) = -C := by
        simp only [add_zero, sub_zero]
        exact mul_div_cancel_right₀ (-C) hs.1.ne'
      simpa only [hzero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hlo : -C ≤ (f t - f s) / (t - s) := le_of_tendsto hltend (by
      filter_upwards [Ioo_mem_nhdsGT hs.1] with r hr using hl r hr)
    have hh : ∀ w ∈ Ioo t 1,
        (f t - f s) / (t - s) ≤ C * (2 - w - t) / (w - t) := by
      intro w hw
      have hw1 : w ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hw.1, hw.2⟩
      have hmono := hconv.slope_mono_adjacent hs hw1 hst hw.1
      have hbound : (f w - f t) / (w - t) ≤ C * (2 - w - t) / (w - t) := by
        apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hw.1.le)
        have hwb := abs_le.mp (hbar w hw1).2
        have htb := abs_le.mp (hbar t ht).2
        linarith
      exact hmono.trans hbound
    have hhtend : Tendsto (fun w : ℝ => C * (2 - w - t) / (w - t)) (𝓝[<] (1 : ℝ)) (𝓝 C) := by
      have hc : ContinuousAt (fun w : ℝ => C * (2 - w - t) / (w - t)) 1 :=
        (continuous_const.mul ((continuous_const.sub continuous_id).sub continuous_const)).continuousAt.div
          (continuous_id.sub continuous_const).continuousAt (sub_ne_zero.mpr ht.2.ne')
      have hone : C * (2 - 1 - t) / (1 - t) = C := by
        rw [show (2 : ℝ) - 1 - t = 1 - t by ring]
        exact mul_div_cancel_right₀ C (sub_ne_zero.mpr ht.2.ne')
      simpa only [hone] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    have hhi : (f t - f s) / (t - s) ≤ C := ge_of_tendsto hhtend (by
      filter_upwards [Ioo_mem_nhdsLT ht.2] with w hw using hh w hw)
    have hlo' := (le_div_iff₀ (sub_pos.mpr hst)).mp hlo
    have hhi' := (div_le_iff₀ (sub_pos.mpr hst)).mp hhi
    exact abs_le.mpr ⟨by linarith, hhi'⟩
  rcases lt_trichotomy s t with hst | rfl | hts
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact key s t hs ht hst
  · simp
  · rw [abs_sub_comm, abs_of_neg (sub_neg.mpr hts), neg_sub]
    exact key t s ht hs hts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- Actual Perron time increments satisfy a finite extended bound, including common poles. -/
theorem finiteGeodesic_le_add_mul_abs (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ} (hC : 0 ≤ C)
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    finiteGeodesic θ u₀ u₁ s x ≤
      finiteGeodesic θ u₀ u₁ t x + ((C * |s - t| : ℝ) : EReal) := by
  by_cases hbot : u₀ x = ⊥
  · have hg (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : finiteGeodesic θ u₀ u₁ r x = ⊥ := by
      have h := (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ hr x).1.2
      simpa only [hbot, EReal.bot_add, le_bot_iff] using h
    simp only [hg s hs, hg t ht, EReal.bot_add, le_refl]
  have hbot₁ : u₁ x ≠ ⊥ := by
    intro hb
    have h := hC₀ x
    rw [hb, EReal.bot_add, le_bot_iff] at h
    exact hbot h
  have he₀ := (EReal.coe_toReal (hu₀.1.quasiPlurisubharmonic.ne_top x) hbot).symm
  have he₁ := (EReal.coe_toReal (hu₁.1.quasiPlurisubharmonic.ne_top x) hbot₁).symm
  have hfinite (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : finiteGeodesic θ u₀ u₁ r x ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot _ (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ hr x).1.1
    rw [he₀, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  have heg (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      finiteGeodesic θ u₀ u₁ r x = ((finiteGeodesic θ u₀ u₁ r x).toReal : EReal) :=
    (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ hr x) (hfinite r hr)).symm
  have hbar (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      |(finiteGeodesic θ u₀ u₁ r x).toReal - (u₀ x).toReal| ≤ C * r ∧
      |(finiteGeodesic θ u₀ u₁ r x).toReal - (u₁ x).toReal| ≤ C * (1 - r) := by
    have hl := canonicalDiff_finiteGeodesic_left_le hu₀ hu₁ hC hC₁ hC₀ hr x
    have hh := canonicalDiff_finiteGeodesic_right_le hu₀ hu₁ hC hC₁ hC₀ hr x
    rw [heg r hr, he₀, canonicalERealDiffToReal_coe_coe] at hl
    rw [heg r hr, he₁, canonicalERealDiffToReal_coe_coe] at hh
    exact ⟨hl, hh⟩
  have hconv := convexOn_toReal_finiteGeodesic_of_forall_ne_bot hu₀ hu₁ x hfinite
  have hbound := abs_sub_le_of_convex_endpoint_barriers hconv hbar ht hs
  rw [heg s hs, heg t ht, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith [abs_le.mp hbound]

private theorem le_add_of_add_neg_le {a b : EReal} {c : ℝ}
    (h : a + ((-c : ℝ) : EReal) ≤ b) : a ≤ b + (c : EReal) := by
  have h' : (a + ((-c : ℝ) : EReal)) + (c : EReal) ≤ b + (c : EReal) := add_le_add h le_rfl
  have hcancel : (a + ((-c : ℝ) : EReal)) + (c : EReal) = a := by
    cases a with
    | bot => simp
    | top => simp
    | coe a =>
      rw [← EReal.coe_add, ← EReal.coe_add]
      congr 1
      ring
  rwa [hcancel] at h'

/-- The actual endpoint-completed Perron curve has the same finite time bound on the entire closed interval. -/
theorem closedSubgeodesicSlice_le_add_mul_abs (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ} (hC : 0 ≤ C)
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
    closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ s x ≤
      closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t x +
        ((C * |s - t| : ℝ) : EReal) := by
  by_cases hs0 : s = 0
  · subst s
    by_cases ht0 : t = 0
    · subst t
      simp
    by_cases ht1 : t = 1
    · subst t
      simpa using hC₀ x
    have ht' : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    have h := (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ ht' x).1.1
    rw [show -C * t = -(C * t) by ring] at h
    have h' := le_add_of_add_neg_le h
    simpa only [closedSubgeodesicSlice_zero, closedSubgeodesicSlice_eq_curve ht',
      zero_sub, abs_neg, abs_of_nonneg ht.1] using h'
  by_cases hs1 : s = 1
  · subst s
    by_cases ht0 : t = 0
    · subst t
      simpa using hC₁ x
    by_cases ht1 : t = 1
    · subst t
      simp
    have ht' : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    have h := (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ ht' x).2.1
    rw [show -C * (1 - t) = -(C * (1 - t)) by ring] at h
    have h' := le_add_of_add_neg_le h
    simpa only [closedSubgeodesicSlice_one, closedSubgeodesicSlice_eq_curve ht',
      abs_of_nonneg (sub_nonneg.mpr ht.2)] using h'
  have hs' : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
  by_cases ht0 : t = 0
  · subst t
    simpa only [closedSubgeodesicSlice_zero, closedSubgeodesicSlice_eq_curve hs',
      sub_zero, abs_of_nonneg hs.1] using
      (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ hs' x).1.2
  by_cases ht1 : t = 1
  · subst t
    have h := (finiteGeodesic_extended_barriers hu₀ hu₁ hC₁ hC₀ hs' x).2.2
    rw [show |s - 1| = 1 - s by rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]; ring]
    simpa only [closedSubgeodesicSlice_one, closedSubgeodesicSlice_eq_curve hs'] using h
  have ht' : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  simpa only [closedSubgeodesicSlice_eq_curve hs', closedSubgeodesicSlice_eq_curve ht'] using
    finiteGeodesic_le_add_mul_abs hu₀ hu₁ hC hC₁ hC₀ hs' ht' x

end

end SGPT.Foundations.Analysis.Pending.SingularGeodesicUniformTimeBounds
