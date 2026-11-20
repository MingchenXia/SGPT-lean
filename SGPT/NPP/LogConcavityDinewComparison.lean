import SGPT.NPP.LogConcavityDinewHeatFlow

/-!
# Upper test functions and the parabolic comparison principle

A function `g : ℂⁿ → ℝ` is a *viscosity subsolution* of `stdTrace (D²g) ≥ 0` (`IsViscositySub`)
if every quadratic polynomial touching it from above at a point
(`IsQuadraticUpperTest g x ℓ M`: `g ≤ g x + ℓ (· - x) + M (· - x) (· - x)` near `x`) has a
quadratic part of nonnegative trace in the real frame `eⱼ, i eⱼ`. This is FPT's upper-test
condition in `lem:constant-elliptic-upper-tests` for the operator `L = ∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`.

`le_heatFlow_of_isViscositySub`: if moreover `g` is upper semicontinuous, of quadratic growth,
and satisfies the initial-layer bound `g - heatFlow g t ≤ C₀ t`, then `g ≤ heatFlow g t` for
`0 < t ≤ 1`. The proof is the parabolic maximum principle: a positive maximum of
`g - heatFlow g t - η t - β ‖x‖²` on `ℂⁿ × [t₁, t]` is attained at an interior time; there the
second-order Taylor polynomial of the heat flow is an upper test (`heatFlow_taylor`), whose
trace is `4 ∂ₜ heatFlow` (`sum_heatFlowHess_coordinate`), contradicting the time monotonicity
at the maximum.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- The real inner product as a continuous bilinear form. -/
def innerBilin (n : ℕ) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ := innerSL ℝ

theorem innerBilin_apply (h k : ComplexModel n) : innerBilin n h k = inner ℝ h k := rfl

theorem stdTrace_innerBilin : stdTrace (innerBilin n) = 2 * n := stdTrace_innerSL

/-- A quadratic polynomial touching `g` from above at `x`. -/
def IsQuadraticUpperTest (g : ComplexModel n → ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) : Prop :=
  ∀ᶠ y in 𝓝 x, g y ≤ g x + ℓ (y - x) + M (y - x) (y - x)

/-- Viscosity subsolutions of `L g ≥ F`, `L = ∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`, tested with quadratic polynomials:
the quadratic polynomial `g x + ℓ (y - x) + M (y - x) (y - x)` has `L = stdTrace M / 2`. -/
def IsViscositySub (g : ComplexModel n → ℝ) (F : ℝ) : Prop :=
  ∀ x ℓ M, IsQuadraticUpperTest g x ℓ M → F ≤ stdTrace M / 2

theorem slope_le_of_left {f : ℝ → ℝ} {D a b c : ℝ} (hf : HasDerivAt f D b) (hab : a < b)
    (hle : ∀ t ∈ Ico a b, f b - f t ≤ -c * (b - t)) : D ≤ -c := by
  have hs : Tendsto (slope f b) (𝓝[<] b) (𝓝 D) :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono b (fun t (ht : t ∈ Iio b) => (ne_of_lt ht : t ≠ b)))
  have hev : ∀ᶠ t in 𝓝[<] b, slope f b t ≤ -c := by
    have : Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
    filter_upwards [this] with t ht
    rw [slope_def_field]
    have htb : t - b < 0 := by linarith [ht.2]
    have := hle t ⟨ht.1.le, ht.2⟩
    rw [div_le_iff_of_neg htb]
    linarith
  exact le_of_tendsto hs hev

theorem nat_mul_div_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) : (n : ℝ) * (η / (8 * (n + 1))) ≤ η / 8 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **The parabolic comparison principle**: an upper semicontinuous viscosity subsolution of
`L g ≥ F` of quadratic growth with an initial-layer bound satisfies `g + F t ≤ heatFlow g t`. -/
theorem le_heatFlow_of_isViscositySub {g : ComplexModel n → ℝ} {C F : ℝ}
    (hC : ∀ y, |g y| ≤ C * (1 + ‖y‖ ^ 2)) (hg : Measurable g) (husc : UpperSemicontinuous g)
    (hvisc : IsViscositySub g F) {C₀ : ℝ}
    (hinit : ∀ x t, 0 < t → t ≤ 1 → g x - heatFlow g t x ≤ C₀ * t) :
    ∀ x t, 0 < t → t ≤ 1 → g x + F * t ≤ heatFlow g t x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨xs, ts, hts0, hts1, hlt⟩ := hcon
  set δ : ℝ := g xs + F * ts - heatFlow g ts xs with hδ
  have hδ0 : 0 < δ := by linarith
  set C₁ : ℝ := max (C₀ + F) 1 with hC₁
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinit' : ∀ x t, 0 < t → t ≤ 1 → g x + F * t - heatFlow g t x ≤ C₁ * t :=
    fun x t ht0 ht1 => by
      have h1 := hinit x t ht0 ht1
      have h2 : (C₀ + F) * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le
      linarith
  set η : ℝ := δ / (4 * ts) with hη
  have hη0 : 0 < η := by positivity
  set β : ℝ := min (η / (8 * (n + 1))) (δ / (4 * (1 + ‖xs‖ ^ 2))) with hβ
  have hβ0 : 0 < β := lt_min (by positivity) (by positivity)
  set Z : ComplexModel n × ℝ → ℝ := fun p =>
    g p.1 + F * p.2 - heatFlow g p.2 p.1 - η * p.2 - β * ‖p.1‖ ^ 2 with hZ
  have hZs : δ / 2 ≤ Z (xs, ts) := by
    have h1 : η * ts = δ / 4 := by rw [hη]; field_simp
    have h2 : β * ‖xs‖ ^ 2 ≤ δ / 4 := by
      have hb : β ≤ δ / (4 * (1 + ‖xs‖ ^ 2)) := min_le_right _ _
      calc β * ‖xs‖ ^ 2 ≤ δ / (4 * (1 + ‖xs‖ ^ 2)) * ‖xs‖ ^ 2 := by gcongr
        _ ≤ δ / (4 * (1 + ‖xs‖ ^ 2)) * (1 + ‖xs‖ ^ 2) := by gcongr; linarith
        _ = δ / 4 := by field_simp
    simp only [hZ]
    linarith
  set t₁ : ℝ := δ / (4 * C₁) with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have hZsmall : ∀ x t, 0 < t → t ≤ t₁ → t ≤ 1 → Z (x, t) ≤ δ / 4 := by
    intro x t ht0 htt₁ ht1
    have h1 := hinit' x t ht0 ht1
    have h2 : C₁ * t ≤ C₁ * t₁ := mul_le_mul_of_nonneg_left htt₁ hC₁0.le
    have h3 : C₁ * t₁ = δ / 4 := by rw [ht₁]; field_simp
    have h4 : 0 ≤ η * t := mul_nonneg hη0.le ht0.le
    have h5 : 0 ≤ β * ‖x‖ ^ 2 := mul_nonneg hβ0.le (sq_nonneg ‖x‖)
    simp only [hZ]
    linarith
  have ht₁ts : t₁ < ts := by
    by_contra h
    push Not at h
    have := hZsmall xs ts hts0 h hts1
    linarith
  set R : ℝ := Real.sqrt (C₁ / β) with hR
  have hZfar : ∀ x t, 0 < t → t ≤ 1 → R < ‖x‖ → Z (x, t) < δ / 2 := by
    intro x t ht0 ht1 hx
    have h1 := hinit' x t ht0 ht1
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hx2 : C₁ / β < ‖x‖ ^ 2 := by
      have := pow_lt_pow_left₀ hx hR0 (two_ne_zero)
      rwa [hR, Real.sq_sqrt (by positivity)] at this
    have hx3 : C₁ < β * ‖x‖ ^ 2 := by rwa [div_lt_iff₀ hβ0, mul_comm] at hx2
    have h4 : 0 ≤ η * t := mul_nonneg hη0.le ht0.le
    have h5 : C₁ * t ≤ C₁ * 1 := mul_le_mul_of_nonneg_left ht1 hC₁0.le
    simp only [hZ]
    linarith
  have hxsR : xs ∈ Metric.closedBall (0 : ComplexModel n) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    have := hZfar xs ts hts0 hts1 h
    linarith
  set S : Set (ComplexModel n × ℝ) := Metric.closedBall (0 : ComplexModel n) R ×ˢ Icc t₁ ts with hS
  have hScpt : IsCompact S := (isCompact_closedBall _ _).prod isCompact_Icc
  have hSne : S.Nonempty := ⟨(xs, ts), hxsR, ⟨ht₁ts.le, le_rfl⟩⟩
  have hSpos : S ⊆ {p : ComplexModel n × ℝ | 0 < p.2} := fun p hp => ht₁0.trans_le hp.2.1
  have hZusc : UpperSemicontinuousOn Z S := by
    have h1 : UpperSemicontinuousOn (fun p : ComplexModel n × ℝ => g p.1) S :=
      (husc.comp continuous_fst).upperSemicontinuousOn S
    have h2 : ContinuousOn (fun p : ComplexModel n × ℝ =>
        F * p.2 + -heatFlow g p.2 p.1 - η * p.2 - β * ‖p.1‖ ^ 2) S := by
      refine ((((continuous_const.mul continuous_snd).continuousOn).add
        ((continuousOn_heatFlow hC hg).mono hSpos).neg).sub ?_).sub ?_
      · exact (continuous_const.mul continuous_snd).continuousOn
      · exact (continuous_const.mul (continuous_fst.norm.pow 2)).continuousOn
    have hZeq : Z = fun p : ComplexModel n × ℝ =>
        g p.1 + (F * p.2 + -heatFlow g p.2 p.1 - η * p.2 - β * ‖p.1‖ ^ 2) := by
      funext p; simp only [hZ]; ring
    rw [hZeq]
    exact h1.add h2.upperSemicontinuousOn
  obtain ⟨p₀, hp₀S, hmax⟩ := hZusc.exists_isMaxOn hSne hScpt
  obtain ⟨x₀, t₀⟩ := p₀
  have hZ₀ : δ / 2 ≤ Z (x₀, t₀) := hZs.trans (hmax ⟨hxsR, ⟨ht₁ts.le, le_rfl⟩⟩)
  have ht₀1 : t₀ ≤ 1 := hp₀S.2.2.trans hts1
  have ht₀ : t₁ < t₀ := by
    rcases eq_or_lt_of_le hp₀S.2.1 with h | h
    · have h' : t₁ = t₀ := h
      have := hZsmall x₀ t₀ (h' ▸ ht₁0) h'.ge ht₀1
      linarith
    · exact h
  have ht₀0 : 0 < t₀ := ht₁0.trans ht₀
  have hglobal : ∀ x, ∀ t ∈ Icc t₁ ts, Z (x, t) ≤ Z (x₀, t₀) := by
    intro x t ht
    by_cases hx : ‖x‖ ≤ R
    · exact hmax ⟨by rwa [Metric.mem_closedBall, dist_zero_right], ht⟩
    · push Not at hx
      exact (hZfar x t (ht₁0.trans_le ht.1) (ht.2.trans hts1) hx).le.trans hZ₀
  -- spatial upper test
  obtain ⟨C', hC'⟩ := heatFlow_taylor hC hg ht₀0 x₀
  obtain ⟨M, hM⟩ := exists_heatFlowHess_clm hC hg ht₀0 x₀
  set C'' : ℝ := max C' 0 with hC''
  set ℓ' : ComplexModel n →L[ℝ] ℝ := innerSL ℝ (heatFlowGrad g t₀ x₀ + (2 * β) • x₀) with hℓ'
  set M' : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • M + (2 * β) • innerBilin n with hM'
  have htest : IsQuadraticUpperTest g x₀ ℓ' M' := by
    have hρ : (0 : ℝ) < min 1 (β / (C'' + 1)) := lt_min one_pos (by positivity)
    filter_upwards [Metric.closedBall_mem_nhds x₀ hρ] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    set h := y - x₀ with hh
    have hy' : y = x₀ + h := by rw [hh]; abel
    have hh1 : ‖h‖ ≤ 1 := hy.trans (min_le_left _ _)
    have hh2 : ‖h‖ ≤ β / (C'' + 1) := hy.trans (min_le_right _ _)
    have hZy := hglobal y t₀ ⟨hp₀S.2.1, hp₀S.2.2⟩
    simp only [hZ] at hZy
    have hT := hC' h hh1
    have hT' : heatFlow g t₀ (x₀ + h) - heatFlow g t₀ x₀ ≤
        inner ℝ (heatFlowGrad g t₀ x₀) h + heatFlowHess g t₀ x₀ h h / 2 + β * ‖h‖ ^ 2 := by
      have h3 : C' * ‖h‖ ^ 3 ≤ β * ‖h‖ ^ 2 := by
        have : C' * ‖h‖ ≤ β := by
          calc C' * ‖h‖ ≤ C'' * ‖h‖ := by gcongr; exact le_max_left C' 0
            _ ≤ (C'' + 1) * ‖h‖ := by gcongr; linarith
            _ ≤ (C'' + 1) * (β / (C'' + 1)) := by gcongr
            _ = β := by
                have hne : C'' + 1 ≠ 0 := by linarith [le_max_right C' (0 : ℝ)]
                field_simp
        nlinarith [sq_nonneg ‖h‖]
      have := (abs_le.mp hT).2
      linarith
    have hnorm : ‖x₀ + h‖ ^ 2 = ‖x₀‖ ^ 2 + 2 * inner ℝ x₀ h + ‖h‖ ^ 2 := by
      rw [norm_add_sq_real]
    rw [hy'] at hZy
    have hℓv : ℓ' h = inner ℝ (heatFlowGrad g t₀ x₀) h + 2 * β * inner ℝ x₀ h := by
      rw [hℓ', innerSL_apply_apply, inner_add_left, real_inner_smul_left]
    have hMv : M' h h = heatFlowHess g t₀ x₀ h h / 2 + 2 * β * ‖h‖ ^ 2 := by
      rw [hM']
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        hM, innerBilin_apply, real_inner_self_eq_norm_sq]
      ring
    rw [hy', hℓv, hMv]
    nlinarith
  have htr := hvisc x₀ ℓ' M' htest
  have htrM : stdTrace M = 4 * heatFlowT g t₀ x₀ := by
    rw [← sum_heatFlowHess_coordinate hC hg ht₀0 x₀]
    simp only [stdTrace, hM]
  rw [hM', stdTrace_add, stdTrace_smul, stdTrace_smul, htrM, stdTrace_innerBilin] at htr
  -- time monotonicity
  have hD := hasDerivAt_heatFlow_time hC hg ht₀0 x₀
  have hDle : heatFlowT g t₀ x₀ ≤ -(η - F) := by
    refine slope_le_of_left hD ht₀ fun t ht => ?_
    have hZt := hglobal x₀ t ⟨ht.1, ht.2.le.trans hp₀S.2.2⟩
    simp only [hZ] at hZt
    linarith
  have hβη : β ≤ η / (8 * (n + 1)) := min_le_left _ _
  have h7 : F ≤ heatFlowT g t₀ x₀ + 2 * ((n : ℝ) * β) := by linarith
  have h8 : (n : ℝ) * β ≤ n * (η / (8 * (n + 1))) :=
    mul_le_mul_of_nonneg_left hβη (Nat.cast_nonneg n)
  have h9 : (n : ℝ) * (η / (8 * (n + 1))) ≤ η / 8 := nat_mul_div_le n hη0.le
  linarith

end SGPT.NPP.LogConcavityDinew
