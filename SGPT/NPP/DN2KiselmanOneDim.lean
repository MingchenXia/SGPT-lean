import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The one-variable penalized minimum of FPT `lem:varying-log-radius-minimum`

Lane DN2, `thm:DNT23_C11bar`; FPT `lem:varying-log-radius-minimum`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 368–413), the one-variable part of the
proof.  For a fixed base point the function `h(s) = H(z, s)` satisfies `h' ≥ 0`, `h'' > 0` and
`h ≥ m` on `s ≤ b`.  For `0 < ε ≤ c/4` the penalized function
`h(s) - c s - ε log(b - s)` on `s < b` has a unique critical point, which is its minimum; the
unpenalized function `h(s) - c s` attains its minimum on `s ≤ b` at a point where `h' ≤ c`.

## Main results

* `LogRadiusProfile`: the hypotheses on `h`.
* `LogRadiusProfile.exists_penaltyDeriv_eq_zero`, `LogRadiusProfile.penaltyDeriv_injOn`,
  `LogRadiusProfile.isMinOn_penalty`: the penalized minimizer.
* `LogRadiusProfile.sub_le_max`: the minimizer stays within `max 1 (2(h(b) - m)/c)` of `b`.
* `LogRadiusProfile.exists_isMinOn`: the unpenalized minimum, with `h' ≤ c` at the minimizer.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.NPP.DN2

/-- The hypotheses of FPT `lem:varying-log-radius-minimum` on one fibre: `h' ≥ 0`, `h'' > 0`,
`h ≥ m` on `s ≤ b`, `c > 0`. -/
structure LogRadiusProfile (h : ℝ → ℝ) (b c m : ℝ) : Prop where
  c_pos : 0 < c
  diff : ∀ s ≤ b, DifferentiableAt ℝ h s
  diff2 : ∀ s ≤ b, DifferentiableAt ℝ (deriv h) s
  deriv_nonneg : ∀ s ≤ b, 0 ≤ deriv h s
  deriv2_pos : ∀ s ≤ b, 0 < deriv (deriv h) s
  lower : ∀ s ≤ b, m ≤ h s

/-- The penalized function `h(s) - c s - ε log(b - s)`. -/
def penalty (h : ℝ → ℝ) (b c ε s : ℝ) : ℝ := h s - c * s - ε * Real.log (b - s)

/-- Its derivative `h'(s) - c + ε/(b - s)`. -/
def penaltyDeriv (h : ℝ → ℝ) (b c ε s : ℝ) : ℝ := deriv h s - c + ε / (b - s)

namespace LogRadiusProfile

variable {h : ℝ → ℝ} {b c m : ℝ}

theorem continuousOn (P : LogRadiusProfile h b c m) : ContinuousOn h (Iic b) :=
  fun s hs => (P.diff s hs).continuousAt.continuousWithinAt

theorem continuousOn_deriv (P : LogRadiusProfile h b c m) : ContinuousOn (deriv h) (Iic b) :=
  fun s hs => (P.diff2 s hs).continuousAt.continuousWithinAt

/-- `h'` is strictly increasing on `s ≤ b`. -/
theorem strictMonoOn_deriv (P : LogRadiusProfile h b c m) : StrictMonoOn (deriv h) (Iic b) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic b) P.continuousOn_deriv fun s hs => ?_
  rw [interior_Iic] at hs
  exact P.deriv2_pos s hs.le

/-- The mean value inequality: `h'(s)(t - s) ≤ h(t) - h(s)` for `s ≤ t ≤ b`. -/
theorem deriv_mul_le_sub (P : LogRadiusProfile h b c m) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ b) :
    deriv h s * (t - s) ≤ h t - h s := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope h (deriv h) hlt
    (P.continuousOn.mono (Icc_subset_Iic_self.trans (Iic_subset_Iic.mpr ht)))
    fun x hx => (P.diff x (hx.2.le.trans ht)).hasDerivAt
  have hle : deriv h s ≤ deriv h ξ :=
    P.strictMonoOn_deriv.monotoneOn (hlt.le.trans ht) (hξ.2.le.trans ht) hξ.1.le
  have hpos : 0 < t - s := sub_pos.mpr hlt
  rw [hξeq, div_eq_iff hpos.ne'] at *
  nlinarith

/-- Somewhere the slope is below `c/2` (otherwise `h → -∞`). -/
theorem exists_deriv_lt (P : LogRadiusProfile h b c m) : ∃ s₁ ≤ b, deriv h s₁ < c / 2 := by
  by_contra hcon
  push Not at hcon
  have hc := P.c_pos
  set s := b - 2 * (h b - m + 1) / c with hs
  have hmb := P.lower b le_rfl
  have hsb : s ≤ b := by
    rw [hs]; have : 0 ≤ 2 * (h b - m + 1) / c := by positivity
    linarith
  have h1 := P.deriv_mul_le_sub hsb le_rfl
  have h2 := hcon s hsb
  have h3 := P.lower s hsb
  have hbs : b - s = 2 * (h b - m + 1) / c := by rw [hs]; ring
  have h4 : c / 2 * (b - s) ≤ deriv h s * (b - s) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  rw [hbs] at h4
  have h5 : c / 2 * (2 * (h b - m + 1) / c) = h b - m + 1 := by field_simp
  linarith

theorem hasDerivAt_penalty (P : LogRadiusProfile h b c m) (ε : ℝ) {s : ℝ} (hs : s < b) :
    HasDerivAt (penalty h b c ε) (penaltyDeriv h b c ε s) s := by
  have hbs : b - s ≠ 0 := (sub_pos.mpr hs).ne'
  have h1 : HasDerivAt (fun t => b - t) (-1) s := (hasDerivAt_id' s).const_sub b
  have h2 : HasDerivAt (fun t => Real.log (b - t)) ((-1) / (b - s)) s := h1.log hbs
  have h3 : HasDerivAt (fun t => h t - c * t - ε * Real.log (b - t))
      (deriv h s - c * 1 - ε * ((-1) / (b - s))) s :=
    ((P.diff s hs.le).hasDerivAt.sub ((hasDerivAt_id' s).const_mul c)).sub (h2.const_mul ε)
  have heq : deriv h s - c * 1 - ε * ((-1) / (b - s)) = penaltyDeriv h b c ε s := by
    unfold penaltyDeriv; field_simp; ring
  rw [heq] at h3
  exact h3

/-- The derivative of the penalized function is strictly increasing on `s < b` (`ε ≥ 0`). -/
theorem strictMonoOn_penaltyDeriv (P : LogRadiusProfile h b c m) {ε : ℝ} (hε : 0 ≤ ε) :
    StrictMonoOn (penaltyDeriv h b c ε) (Iio b) := by
  intro s hs t ht hst
  have h1 : deriv h s < deriv h t :=
    P.strictMonoOn_deriv (mem_Iic.mpr (mem_Iio.mp hs).le) (mem_Iic.mpr (mem_Iio.mp ht).le) hst
  have hbt : 0 < b - t := sub_pos.mpr ht
  have h2 : ε / (b - s) ≤ ε / (b - t) :=
    div_le_div_of_nonneg_left hε hbt (by linarith)
  unfold penaltyDeriv
  linarith

theorem penaltyDeriv_injOn (P : LogRadiusProfile h b c m) {ε : ℝ} (hε : 0 ≤ ε) :
    InjOn (penaltyDeriv h b c ε) (Iio b) :=
  (P.strictMonoOn_penaltyDeriv hε).injOn

theorem continuousOn_penaltyDeriv (P : LogRadiusProfile h b c m) (ε : ℝ) :
    ContinuousOn (penaltyDeriv h b c ε) (Iio b) := by
  refine ((P.continuousOn_deriv.mono Iio_subset_Iic_self).sub continuousOn_const).add ?_
  exact continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun s hs =>
    (sub_pos.mpr hs).ne'

/-- **Existence of the penalized critical point** for `0 < ε ≤ c/4`. -/
theorem exists_penaltyDeriv_eq_zero (P : LogRadiusProfile h b c m) {ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ c / 4) : ∃ s < b, penaltyDeriv h b c ε s = 0 := by
  have hc := P.c_pos
  obtain ⟨s₁, hs₁b, hs₁⟩ := P.exists_deriv_lt
  set a := min s₁ (b - 1) with ha
  set a' := b - ε / (2 * c) with ha'
  have hεc' : ε / (2 * c) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hεc0 : 0 < ε / (2 * c) := by positivity
  have hab : a ≤ b - 1 := min_le_right _ _
  have haa' : a ≤ a' := by rw [ha']; linarith
  have ha'b : a' < b := by rw [ha']; linarith
  have hga : penaltyDeriv h b c ε a < 0 := by
    have h1 : deriv h a ≤ deriv h s₁ :=
      P.strictMonoOn_deriv.monotoneOn (mem_Iic.mpr (by linarith)) (mem_Iic.mpr hs₁b)
        (min_le_left _ _)
    have h2 : ε / (b - a) ≤ ε := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    unfold penaltyDeriv; linarith
  have hga' : 0 < penaltyDeriv h b c ε a' := by
    have h1 := P.deriv_nonneg a' ha'b.le
    have h2 : ε / (b - a') = 2 * c := by
      rw [ha', sub_sub_cancel]; field_simp
    unfold penaltyDeriv; linarith
  have hcont : ContinuousOn (penaltyDeriv h b c ε) (Icc a a') :=
    (P.continuousOn_penaltyDeriv ε).mono fun s hs => mem_Iio.mpr (lt_of_le_of_lt hs.2 ha'b)
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc haa' hcont ⟨hga.le, hga'.le⟩
  exact ⟨s, lt_of_le_of_lt hs.2 ha'b, hs0⟩

/-- **The penalized critical point is the minimum** on `s < b`. -/
theorem isMinOn_penalty (P : LogRadiusProfile h b c m) {ε : ℝ} (hε : 0 ≤ ε) {s : ℝ}
    (hs : s < b) (hcrit : penaltyDeriv h b c ε s = 0) :
    IsMinOn (penalty h b c ε) (Iio b) s := by
  have hderiv : ∀ t < b, deriv (penalty h b c ε) t = penaltyDeriv h b c ε t := fun t ht =>
    (P.hasDerivAt_penalty ε ht).deriv
  have hcont : ∀ t < b, ContinuousAt (penalty h b c ε) t := fun t ht =>
    (P.hasDerivAt_penalty ε ht).continuousAt
  intro t ht
  have ht' : t < b := ht
  rcases le_total t s with hts | hst
  · -- `penalty` is antitone on `[t, s]`
    have hanti : AntitoneOn (penalty h b c ε) (Icc t s) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc t s)
        (fun x hx => (hcont x (lt_of_le_of_lt hx.2 hs)).continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Icc] at hx
        exact (P.hasDerivAt_penalty ε (lt_trans hx.2 hs)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hx
        rw [hderiv x (lt_trans hx.2 hs), ← hcrit]
        exact (P.strictMonoOn_penaltyDeriv hε (mem_Iio.mpr (lt_trans hx.2 hs))
          (mem_Iio.mpr hs) hx.2).le
    exact hanti ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
  · have hmono : MonotoneOn (penalty h b c ε) (Icc s t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc s t)
        (fun x hx => (hcont x (lt_of_le_of_lt hx.2 ht')).continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Icc] at hx
        exact (P.hasDerivAt_penalty ε (lt_trans hx.2 ht')).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hx
        rw [hderiv x (lt_trans hx.2 ht'), ← hcrit]
        exact (P.strictMonoOn_penaltyDeriv hε (mem_Iio.mpr hs)
          (mem_Iio.mpr (lt_trans hx.2 ht')) hx.1).le
    exact hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- **The penalized minimizer stays near the end point**: if `ε ≤ c/2`, then
`b - s ≤ max 1 (2 (h(b) - m)/c)`. -/
theorem sub_le_max (P : LogRadiusProfile h b c m) {ε : ℝ} (hε : 0 ≤ ε) (hεc : ε ≤ c / 2)
    {s : ℝ} (hs : s < b) (hcrit : penaltyDeriv h b c ε s = 0) :
    b - s ≤ max 1 (2 * (h b - m) / c) := by
  have hc := P.c_pos
  by_cases h1 : b - s ≤ 1
  · exact h1.trans (le_max_left _ _)
  push Not at h1
  have hdh : deriv h s = c - ε / (b - s) := by
    unfold penaltyDeriv at hcrit; linarith
  have hεb : ε / (b - s) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hge : c / 2 ≤ deriv h s := by rw [hdh]; linarith
  have htan := P.deriv_mul_le_sub hs.le le_rfl
  have hm := P.lower s hs.le
  have h2 : c / 2 * (b - s) ≤ h b - m := by
    have := mul_le_mul_of_nonneg_right hge (by linarith : (0 : ℝ) ≤ b - s)
    linarith
  refine le_trans ?_ (le_max_right _ _)
  rw [le_div_iff₀ hc]
  linarith

/-- **The unpenalized minimum** of `h(s) - c s` on `s ≤ b` is attained, at a point where
`h' ≤ c`. -/
theorem exists_isMinOn (P : LogRadiusProfile h b c m) :
    ∃ s ≤ b, IsMinOn (fun t => h t - c * t) (Iic b) s ∧ deriv h s ≤ c := by
  have hc := P.c_pos
  set R := (h b - m) / c + 1 with hR
  have hmb := P.lower b le_rfl
  have hR0 : 0 < R := by
    have : 0 ≤ (h b - m) / c := div_nonneg (by linarith) hc.le
    rw [hR]; linarith
  have hcont : ContinuousOn (fun t => h t - c * t) (Icc (b - R) b) :=
    (P.continuousOn.mono Icc_subset_Iic_self).sub (continuousOn_const.mul continuousOn_id)
  obtain ⟨s, hs, hmin⟩ := (isCompact_Icc).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) hcont
  have hmin' : IsMinOn (fun t => h t - c * t) (Iic b) s := by
    intro t ht
    have ht' : t ≤ b := ht
    by_cases htR : b - R ≤ t
    · exact hmin ⟨htR, ht'⟩
    · push Not at htR
      have h1 : h s - c * s ≤ h b - c * b := hmin (⟨by linarith, le_rfl⟩ : b ∈ Icc (b - R) b)
      have h2 := P.lower t ht'
      show h s - c * s ≤ h t - c * t
      have h3 : c * (b - R) = c * b - (h b - m) - c := by
        rw [hR]; field_simp; ring
      have h4 : c * t < c * (b - R) := mul_lt_mul_of_pos_left htR hc
      linarith
  refine ⟨s, hs.2, hmin', ?_⟩
  by_contra hcon
  push Not at hcon
  -- near `s` the slope exceeds `c`, so moving left decreases the value
  have hev : ∀ᶠ t in 𝓝 s, c < deriv h t :=
    (P.diff2 s hs.2).continuousAt.eventually (lt_mem_nhds hcon)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set t := s - δ / 2 with ht
  have hts : t < s := by rw [ht]; linarith
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope h (deriv h) hts
    (P.continuousOn.mono (Icc_subset_Iic_self.trans (Iic_subset_Iic.mpr hs.2)))
    fun x hx => (P.diff x (hx.2.le.trans hs.2)).hasDerivAt
  have hξd : c < deriv h ξ := by
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hξ.1, hξ.2]
  have hpos : 0 < s - t := sub_pos.mpr hts
  rw [hξeq, lt_div_iff₀ hpos] at hξd
  have hle : h s - c * s ≤ h t - c * t := hmin' (mem_Iic.mpr (hts.le.trans hs.2))
  linarith

end LogRadiusProfile

end SGPT.NPP.DN2
