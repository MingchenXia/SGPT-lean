import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Recovering a monotone convex function from a one-parameter Legendre family

This is the convex-analysis step of the injectivity half of `lma:anaorder`
(`chapter_NApotential.tex`, *The comparison theorem*).  For `Γ ∈ PSH^NA(X, θ)`, a divisorial
valuation `t ord_E` and the slice Lelong numbers `g(τ) = ν(Γ_τ, E)` (`τ < Γ_max`), the book's
analytification is

`Γ^An(t ord_E) = sup_{τ < Γ_max} (τ - t g(τ))`,

and the book concludes from `Γ^An ≤ Γ'^An` on `X^Div` that `ν(Γ_τ, E) ≥ ν(Γ'_τ, E)` for every
`τ`, quoting `cor:Leginvpartdef`.  What is used is the inversion of this Legendre-type transform
on the *monotone convex* function `τ ↦ ν(Γ'_τ, E)`.  We prove it directly with a subgradient,
and only along rational `t > 0`, because `X^Div` consists of the valuations `t ord_E` with
`t ∈ ℚ_{>0}`.

## Main results

* `exists_nonneg_subgradient_of_convexOn_Iio`: a convex function on `(-∞, a)` that is monotone
  there has a nonnegative subgradient at every point.
* `le_of_forall_rat_legendre_le`: if `sup_{τ<a} (τ - t f(τ)) ≤ sup_{τ<b} (τ - t g(τ))` for all
  rational `t > 0` (in the sup-free form `hT`), `a ≤ b`, and `g` is convex and monotone on
  `(-∞, b)`, then `g ≤ f` on `(-∞, a)`.  No regularity of `f` is needed.
-/

set_option autoImplicit false

namespace SGPT.NAPotential.BJPrep

open Set

/-- A convex function on `(-∞, a)` that is monotone there has a nonnegative subgradient at
every point of `(-∞, a)`. -/
theorem exists_nonneg_subgradient_of_convexOn_Iio {a τ₀ : ℝ} {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Iio a) g) (hmono : MonotoneOn g (Iio a)) (hτ₀ : τ₀ < a) :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ τ < a, g τ₀ + s * (τ - τ₀) ≤ g τ := by
  set S : Set ℝ := (fun τ => (g τ - g τ₀) / (τ - τ₀)) '' Ioo τ₀ a with hS
  have hmid : (τ₀ + a) / 2 ∈ Ioo τ₀ a := ⟨by linarith, by linarith⟩
  have hSne : S.Nonempty := ⟨_, (τ₀ + a) / 2, hmid, rfl⟩
  have hτ₀mem : τ₀ ∈ Iio a := hτ₀
  -- every left secant slope is a lower bound of the right secant slopes
  have hleft : ∀ τ < τ₀, ∀ y ∈ S, (g τ₀ - g τ) / (τ₀ - τ) ≤ y := by
    rintro τ hτ _ ⟨τ', hτ', rfl⟩
    exact hg.slope_mono_adjacent (show τ ∈ Iio a from hτ.trans hτ₀) hτ'.2 hτ hτ'.1
  have hbdd : BddBelow S := ⟨_, hleft (τ₀ - 1) (by linarith)⟩
  refine ⟨sInf S, ?_, ?_⟩
  · apply le_csInf hSne
    rintro _ ⟨τ, hτ, rfl⟩
    apply div_nonneg _ (sub_nonneg.mpr hτ.1.le)
    exact sub_nonneg.mpr (hmono hτ₀mem hτ.2 hτ.1.le)
  · intro τ hτ
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · have h := le_csInf hSne (hleft τ hlt)
      have hpos : 0 < τ₀ - τ := sub_pos.mpr hlt
      rw [div_le_iff₀ hpos] at h
      nlinarith
    · subst heq
      simp
    · have h : sInf S ≤ (g τ - g τ₀) / (τ - τ₀) := csInf_le hbdd ⟨τ, ⟨hgt, hτ⟩, rfl⟩
      have hpos : 0 < τ - τ₀ := sub_pos.mpr hgt
      rw [le_div_iff₀ hpos] at h
      linarith

/-- **Legendre comparison.**  Let `a ≤ b`, let `g` be convex and monotone on `(-∞, b)` and let
`f` be arbitrary.  Assume that for every rational `t > 0`,
`sup_{τ < a} (τ - t f(τ)) ≤ sup_{τ < b} (τ - t g(τ))`, written without suprema as `hT`.
Then `g(τ₀) ≤ f(τ₀)` for every `τ₀ < a`. -/
theorem le_of_forall_rat_legendre_le {a b τ₀ : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hg : ConvexOn ℝ (Iio b) g) (hmono : MonotoneOn g (Iio b))
    (hT : ∀ t : ℚ, 0 < t → ∀ τ < a, ∀ c : ℝ,
      (∀ τ' < b, τ' - (t : ℝ) * g τ' ≤ c) → τ - (t : ℝ) * f τ ≤ c)
    (hτ₀ : τ₀ < a) : g τ₀ ≤ f τ₀ := by
  have hτ₀b : τ₀ < b := hτ₀.trans_le hab
  obtain ⟨s, hs0, hsub⟩ := exists_nonneg_subgradient_of_convexOn_Iio hg hmono hτ₀b
  by_contra hlt
  push Not at hlt
  set d := g τ₀ - f τ₀ with hd_def
  set D := b - τ₀ with hD_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hD : 0 < D := by rw [hD_def]; linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + d / D by
    have : 0 < d / D := div_pos hd hD
    linarith)
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt hs0 hq1
  have hqposQ : (0 : ℚ) < q := by exact_mod_cast hqpos
  set ε : ℝ := (q : ℝ) - s with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hεD : ε * D < d := by
    have h1 : ε < d / D := by rw [hε_def]; linarith
    calc ε * D < d / D * D := (mul_lt_mul_iff_left₀ hD).mpr h1
      _ = d := div_mul_cancel₀ d hD.ne'
  let t : ℚ := q⁻¹
  have ht : (0 : ℚ) < t := inv_pos.mpr hqposQ
  have htR : (t : ℝ) = (q : ℝ)⁻¹ := by simp [t]
  have htpos : (0 : ℝ) < (t : ℝ) := by rw [htR]; exact inv_pos.mpr hqpos
  have htq : (t : ℝ) * q = 1 := by rw [htR]; exact inv_mul_cancel₀ hqpos.ne'
  have key := hT t ht τ₀ hτ₀ ((t : ℝ) * (ε * b - g τ₀ + s * τ₀)) (by
    intro τ' hτ'
    have h1 : (t : ℝ) * (g τ₀ + s * (τ' - τ₀)) ≤ (t : ℝ) * g τ' :=
      mul_le_mul_of_nonneg_left (hsub τ' hτ') htpos.le
    have h2 : (t : ℝ) * (ε * τ') ≤ (t : ℝ) * (ε * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ'.le hε.le) htpos.le
    have h4 : (q : ℝ) = s + ε := by rw [hε_def]; ring
    have htq' : (t : ℝ) * (s + ε) = 1 := by rw [← h4]; exact htq
    calc τ' - (t : ℝ) * g τ' ≤ τ' - (t : ℝ) * (g τ₀ + s * (τ' - τ₀)) := by linarith
      _ = (t : ℝ) * (ε * τ' - g τ₀ + s * τ₀) := by linear_combination (-τ') * htq'
      _ ≤ (t : ℝ) * (ε * b - g τ₀ + s * τ₀) := by nlinarith [h2])
  -- multiply `key` by `q`
  have hkey : (q : ℝ) * (τ₀ - (t : ℝ) * f τ₀) ≤
      (q : ℝ) * ((t : ℝ) * (ε * b - g τ₀ + s * τ₀)) :=
    mul_le_mul_of_nonneg_left key hqpos.le
  have hqt : (q : ℝ) * (t : ℝ) = 1 := by rw [mul_comm]; exact htq
  have hL : (q : ℝ) * (τ₀ - (t : ℝ) * f τ₀) = q * τ₀ - f τ₀ := by
    have : (q : ℝ) * ((t : ℝ) * f τ₀) = f τ₀ := by rw [← mul_assoc, hqt, one_mul]
    rw [mul_sub, this]
  have hR : (q : ℝ) * ((t : ℝ) * (ε * b - g τ₀ + s * τ₀)) = ε * b - g τ₀ + s * τ₀ := by
    rw [← mul_assoc, hqt, one_mul]
  rw [hL, hR] at hkey
  have h4 : (q : ℝ) = s + ε := by rw [hε_def]; ring
  rw [h4] at hkey
  -- `hkey : (s + ε) τ₀ - f τ₀ ≤ ε b - g τ₀ + s τ₀`, i.e. `d ≤ ε D`
  have : d ≤ ε * D := by
    rw [hd_def, hD_def]
    nlinarith
  linarith

end SGPT.NAPotential.BJPrep
