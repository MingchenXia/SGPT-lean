import SGPT.Foundations.Analysis.Pending.PshThreeCircles

set_option autoImplicit false

/-! # Actual explicit and uniform logarithmic-exponent bounds from genuine PSH data -/

open Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.LocalUniformLogarithmicExponentBound

open PshThreeCircles

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual three-circle inequality bounds every logarithmic exponent
by one explicit real ratio, independently of its germ radius and constant. -/
theorem log_exponent_le_of_point_bounds {u : E → EReal} {Ω : Set E}
    (hu : PlurisubharmonicOn u Ω) {p y₀ : E} {R A B γ C ρ : ℝ}
    (hΩ : closedBall p R ⊆ Ω) (hy₀ : ‖y₀ - p‖ < R) (hy₀p : y₀ ≠ p)
    (hA : ∀ z ∈ closedBall p R, u z ≤ (A : EReal)) (hB : (B : EReal) ≤ u y₀)
    (hρ : 0 < ρ)
    (hadm : ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      u z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal)) :
    γ ≤ (A - B) / (Real.log R - Real.log ‖y₀ - p‖) := by
  have hd : 0 < ‖y₀ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy₀p)
  have hdR : ‖y₀ - p‖ < R := hy₀
  have hRpos : 0 < R := hd.trans hy₀
  let t₂ : ℝ := Real.log ‖y₀ - p‖
  let t₀ : ℝ := Real.log R
  have ht₂t₀ : t₂ < t₀ := Real.log_lt_log hd hdR
  have hBA : B ≤ A := EReal.coe_le_coe_iff.mp
    (hB.trans (hA y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hy₀.le))))
  have ht₂ : t₂ = Real.log ‖y₀ - p‖ := rfl
  have ht₀ : t₀ = Real.log R := rfl
  by_contra hgs
  rw [not_le] at hgs
  set P : ℝ := A - B - γ * (t₀ - t₂) with hP
  have hPneg : P < 0 := by
    have hpos : 0 < t₀ - t₂ := by linarith
    rw [hP]
    have := (div_lt_iff₀ hpos).mp hgs
    linarith
  set Q : ℝ := B * t₀ - C * (t₀ - t₂) - t₂ * A with hQ
  set t : ℝ := min (min (Real.log ρ) t₂) (-Q / P) - 1 with ht
  have htρ : t < Real.log ρ := by
    have : t ≤ Real.log ρ - 1 := by
      rw [ht]; have := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_left (Real.log ρ) t₂
      linarith [this.trans h2]
    linarith
  have htt₂ : t < t₂ := by
    have : t ≤ t₂ - 1 := by
      rw [ht]
      have h1 := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_right (Real.log ρ) t₂
      linarith [h1.trans h2]
    linarith
  have htQ : t < -Q / P := by
    have : t ≤ -Q / P - 1 := by
      rw [ht]; linarith [min_le_right (min (Real.log ρ) t₂) (-Q / P)]
    linarith
  -- the inner radius
  set r : ℝ := Real.exp t with hr
  have hrpos : 0 < r := Real.exp_pos t
  have hrρ : r < ρ := by
    rw [hr, ← Real.exp_log hρ]; exact Real.exp_lt_exp.mpr htρ
  have hrd : r < ‖y₀ - p‖ := by
    rw [hr, ← Real.exp_log hd]; exact Real.exp_lt_exp.mpr htt₂
  have hrR : r < R := hrd.trans hdR
  have hlogr : Real.log r = t := Real.log_exp t
  -- the three-circle inequality on `r < ‖y₀ - p‖ < R`
  have h1 : ∀ z : E, ‖z - p‖ = r → u z ≤ ((γ * t + C : ℝ) : EReal) := by
    intro z hz
    have := hadm z (by rw [hz]; exact hrpos) (by rw [hz]; exact hrρ)
    rwa [hz, hlogr] at this
  have h3 : ∀ z : E, ‖z - p‖ = R → u z ≤ (A : EReal) := fun z hz =>
    hA z (mem_closedBall.mpr (by rw [dist_eq_norm, hz]))
  have hchord := le_log_interpolation hu hrpos hrR hΩ h1 h3
    (z := y₀) hrd.le hdR.le
  rw [hlogr, ← ht₂, ← ht₀] at hchord
  have hreal : B ≤ γ * t + C + (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) :=
    EReal.coe_le_coe_iff.mp (hB.trans hchord)
  -- and the contradiction
  have ht₀t : 0 < t₀ - t := by linarith
  have h' : B - (γ * t + C) ≤ (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) := by linarith
  have hstep : (B - (γ * t + C)) * (t₀ - t) ≤ (t₂ - t) * (A - (γ * t + C)) :=
    (le_div_iff₀ ht₀t).mp h'
  have hclear : B * (t₀ - t) ≤ (γ * t + C) * (t₀ - t₂) + (t₂ - t) * A := by nlinarith [hstep]
  have hfinal : t * P ≤ -Q := by rw [hP, hQ]; nlinarith [hclear]
  have : -Q / P ≤ t := by
    rw [div_le_iff_of_neg hPneg]
    linarith [hfinal]
  linarith


/-- Controlled radii and actual finite-point lower/closed-ball upper bounds
produce one uniform bound for all admissible logarithmic exponents. -/
theorem log_exponent_le_uniform_point_bound {u : E → EReal} {Ω : Set E}
    (hu : PlurisubharmonicOn u Ω) {p y₀ : E} {r R A B γ C ρ : ℝ}
    (hΩ : closedBall p R ⊆ Ω) (hyr : ‖y₀ - p‖ ≤ r) (hrR : r < R) (hy₀p : y₀ ≠ p)
    (hA : ∀ z ∈ closedBall p R, u z ≤ (A : EReal)) (hB : ((-B : ℝ) : EReal) ≤ u y₀)
    (hρ : 0 < ρ)
    (hadm : ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      u z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal)) :
    γ ≤ (A + B) / (Real.log R - Real.log r) := by
  have hd : 0 < ‖y₀ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy₀p)
  have hr : 0 < r := hd.trans_le hyr
  have hyR : ‖y₀ - p‖ < R := hyr.trans_lt hrR
  have hAB : 0 ≤ A + B := by
    have h := EReal.coe_le_coe_iff.mp
      (hB.trans (hA y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hyR.le))))
    linarith
  have hden : 0 < Real.log R - Real.log r := sub_pos.mpr (Real.log_lt_log hr hrR)
  have hdenle : Real.log R - Real.log r ≤ Real.log R - Real.log ‖y₀ - p‖ := by
    linarith [Real.log_le_log hd hyr]
  have h := log_exponent_le_of_point_bounds hu hΩ hyR hy₀p hA hB hρ hadm
  rw [sub_neg_eq_add] at h
  exact h.trans (div_le_div_of_nonneg_left hAB hden hdenle)

end
end SGPT.Foundations.Analysis.Pending.LocalUniformLogarithmicExponentBound
