import SGPT.Okounkov.TranscendentalRelGenGeneration
import SGPT.Foundations.Analysis.Pending.OTSliceVanishing
import SGPT.Foundations.Analysis.Pending.RiemannExtension
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin

/-!
# Square-integrable quotients by a holomorphic function

Blueprint node `relgen:l2-divisibility` (chapter `claude-tok-relgen`): the identity
`𝓘(m log |g|²) = (g^m)`, i.e. `L2DivisibilityStatement` (`l2DivisibilityStatement`). Let `g`,
`F` be holomorphic near `p ∈ ℂ^d`, `g` not identically zero, and `∫ |F|² |g|^{-2m} < ∞` near
`p`. Then `F = a g^m` near `p` with `a` holomorphic.

Proof. Choose a direction `v` with `τ ↦ g(p + τ v)` not identically zero, and a circle
`|τ| = ρ` on which `g(y + τ v) ≠ 0` for `y` near `p`. The Cauchy integral
`a(y) = (2πi)⁻¹ ∮_{|τ| = ρ} τ⁻¹ (F / g^m)(y + τ v) dτ` is holomorphic near `p`
(`RiemannExtension.differentiableAt_circleIntegral_param`). By Tonelli and translation
invariance, for almost every `y` the slice `τ ↦ |F|² |g|^{-2m} (y + τ v)` is integrable on a
disc; a meromorphic function of one variable with a square-integrable modulus has no pole
(`exists_bound_of_lintegral_ne_top`: a pole of order `≥ 1` gives `|τ - τ₀|^{-2}`, which is not
integrable in `ℂ`), so the slice quotient is holomorphic and `a(y) = (F / g^m)(y)` by Cauchy's
formula (`cauchy_integral_eq_of_locally_bounded`). Almost every point is dense, so
`a = F / g^m` off `g = 0`, and `F = a g^m` everywhere near `p` by continuity.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric MeasureTheory Complex
open scoped Topology ENNReal Real
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

/-! ### One variable -/

/-- `∫_{B(τ₀, δ)} c |τ - τ₀|^{-2} = ∞` in `ℂ`. -/
theorem lintegral_ball_div_normSq_sub_eq_top (τ₀ : ℂ) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∫⁻ τ in ball τ₀ δ, ENNReal.ofReal (c / ‖τ - τ₀‖ ^ 2) = ⊤ := by
  have h := OTChen.lintegral_ball_div_normSq_eq_top hδ hc
  rw [← lintegral_indicator measurableSet_ball] at h ⊢
  have hfun : (fun x => (ball τ₀ δ).indicator (fun τ => ENNReal.ofReal (c / ‖τ - τ₀‖ ^ 2))
      (x + τ₀)) = (ball (0 : ℂ) δ).indicator (fun u => ENNReal.ofReal (c / ‖u‖ ^ 2)) := by
    funext u
    have hmem : u + τ₀ ∈ ball τ₀ δ ↔ u ∈ ball (0 : ℂ) δ := by
      simp [mem_ball, dist_eq_norm]
    by_cases hu : u ∈ ball (0 : ℂ) δ
    · rw [indicator_of_mem (hmem.mpr hu), indicator_of_mem hu, add_sub_cancel_right]
    · rw [indicator_of_notMem (fun h => hu (hmem.mp h)), indicator_of_notMem hu]
  rw [← lintegral_add_right_eq_self (μ := (volume : Measure ℂ)) _ τ₀, hfun]
  exact h

/-- **A square-integrable quotient has no pole**: if `ψ`, `Φ` are analytic at `τ₀`, `ψ` is
not identically zero near `τ₀` and `∫ |Φ|² |ψ|^{-2m} < ∞` near `τ₀`, then `Φ / ψ^m` is bounded
near `τ₀` off the zeros of `ψ`. -/
theorem exists_bound_of_lintegral_ne_top {ψ Φ : ℂ → ℂ} {τ₀ : ℂ} (hψ : AnalyticAt ℂ ψ τ₀)
    (hΦ : AnalyticAt ℂ Φ τ₀) (hψ0 : ¬ ∀ᶠ τ in 𝓝 τ₀, ψ τ = 0) (m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hint : ∫⁻ τ in ball τ₀ δ, ENNReal.ofReal (‖Φ τ‖ ^ 2) /
      ENNReal.ofReal (‖ψ τ‖ ^ (2 * m)) ≠ ⊤) :
    ∃ C : ℝ, ∀ᶠ τ in 𝓝 τ₀, ψ τ ≠ 0 → ‖Φ τ / ψ τ ^ m‖ ≤ C := by
  obtain ⟨k, v, hv, hv0, hψeq⟩ := hψ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hψ0
  by_cases hΦ0 : ∀ᶠ τ in 𝓝 τ₀, Φ τ = 0
  · exact ⟨0, hΦ0.mono fun τ hτ _ => by simp [hτ]⟩
  obtain ⟨l, u, hu, hu0, hΦeq⟩ := hΦ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hΦ0
  by_cases hl : k * m ≤ l
  · -- no pole: the quotient is `(τ - τ₀)^{l - km} u / v^m`
    set q : ℂ → ℂ := fun τ => (τ - τ₀) ^ (l - k * m) * u τ / v τ ^ m
    have hqc : ContinuousAt q τ₀ :=
      (((continuousAt_id.sub continuousAt_const).pow _).mul hu.continuousAt).div
        (hv.continuousAt.pow _) (pow_ne_zero _ hv0)
    refine ⟨‖q τ₀‖ + 1, ?_⟩
    filter_upwards [hψeq, hΦeq, hqc.norm.eventually_lt continuousAt_const (lt_add_one ‖q τ₀‖)]
      with τ hψτ hΦτ hqτ hτ0
    have hpow : (τ - τ₀) ^ (k * m) ≠ 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · simp [hk]
      · refine pow_ne_zero _ fun h0 => hτ0 ?_
        rw [hψτ, h0, zero_pow hk.ne', zero_smul]
    have hvτ : v τ ≠ 0 := by
      intro h0
      apply hτ0
      rw [hψτ, h0, smul_zero]
    have heq : Φ τ / ψ τ ^ m = q τ := by
      rw [hΦτ, hψτ, smul_eq_mul, smul_eq_mul]
      simp only [q]
      have hl' : l = k * m + (l - k * m) := (Nat.add_sub_cancel' hl).symm
      rw [hl', pow_add, mul_pow, ← pow_mul, Nat.add_sub_cancel_left]
      field_simp
    rw [heq]
    exact hqτ.le
  · -- a pole: the integral diverges
    exfalso
    push Not at hl
    apply hint
    set c : ℝ := (‖u τ₀‖ / 2) ^ 2 / (‖v τ₀‖ + 1) ^ (2 * m) with hc
    have hcpos : 0 < c := by
      have : 0 < ‖u τ₀‖ := norm_pos_iff.mpr hu0
      positivity
    have hev : ∀ᶠ τ in 𝓝 τ₀, ‖u τ₀‖ / 2 < ‖u τ‖ ∧ ‖v τ‖ < ‖v τ₀‖ + 1 ∧ 0 < ‖v τ‖ ∧
        ψ τ = (τ - τ₀) ^ k • v τ ∧ Φ τ = (τ - τ₀) ^ l • u τ := by
      have h1 : ∀ᶠ τ in 𝓝 τ₀, ‖u τ₀‖ / 2 < ‖u τ‖ :=
        continuousAt_const.eventually_lt hu.continuousAt.norm
          (by have := norm_pos_iff.mpr hu0; linarith)
      have h2 : ∀ᶠ τ in 𝓝 τ₀, ‖v τ‖ < ‖v τ₀‖ + 1 :=
        hv.continuousAt.norm.eventually_lt continuousAt_const (lt_add_one _)
      have h3 : ∀ᶠ τ in 𝓝 τ₀, 0 < ‖v τ‖ :=
        continuousAt_const.eventually_lt hv.continuousAt.norm (norm_pos_iff.mpr hv0)
      filter_upwards [h1, h2, h3, hψeq, hΦeq] with τ a1 a2 a3 a4 a5
      exact ⟨a1, a2, a3, a4, a5⟩
    obtain ⟨δ', hδ', hδ's⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set δ'' := min (min δ δ') 1 with hδ''
    have hδ''0 : 0 < δ'' := lt_min (lt_min hδ hδ') one_pos
    refine top_le_iff.mp ((lintegral_ball_div_normSq_sub_eq_top τ₀ hδ''0 hcpos).symm.le.trans ?_)
    refine (setLIntegral_mono' measurableSet_ball fun τ hτ => ?_).trans
      (lintegral_mono_set (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))))
    have hτ' : τ ∈ ball τ₀ δ' :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hτ
    obtain ⟨a1, a2, a3, a4, a5⟩ := hδ's τ hτ'
    have hτ1 : ‖τ - τ₀‖ < 1 := by
      have := mem_ball.mp hτ
      rw [dist_eq_norm] at this
      exact lt_of_lt_of_le this (min_le_right _ _)
    rcases eq_or_ne τ τ₀ with rfl | hne
    · simp
    have hd : 0 < ‖τ - τ₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hψpos : 0 < ‖ψ τ‖ ^ (2 * m) := by
      rw [a4, norm_smul, norm_pow]
      positivity
    rw [← ENNReal.ofReal_div_of_pos hψpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [a4, a5, norm_smul, norm_smul, norm_pow, norm_pow]
    -- the exponent `2l - 2km ≤ -2`
    set t := ‖τ - τ₀‖
    have hj : 1 ≤ k * m - l := by omega
    have hkm : k * m = l + (k * m - l) := (Nat.add_sub_cancel' hl.le).symm
    have hmain : 1 / t ^ 2 ≤ (t ^ l) ^ 2 / (t ^ k) ^ (2 * m) := by
      rw [← pow_mul, ← pow_mul, show k * (2 * m) = 2 * (k * m) by ring, hkm, mul_add, pow_add,
        mul_comm l 2]
      have htl : 0 < t ^ (2 * l) := pow_pos hd _
      rw [div_mul_eq_div_div, div_self htl.ne', one_div_le_one_div (by positivity) (by positivity)]
      calc t ^ (2 * (k * m - l)) ≤ t ^ 2 :=
            pow_le_pow_of_le_one hd.le hτ1.le (by omega)
        _ = t ^ 2 := rfl
    have hu2 : (‖u τ₀‖ / 2) ^ 2 ≤ ‖u τ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) a1.le 2
    have hv2 : ‖v τ‖ ^ (2 * m) ≤ (‖v τ₀‖ + 1) ^ (2 * m) :=
      pow_le_pow_left₀ (norm_nonneg _) a2.le _
    have hv2pos : 0 < ‖v τ‖ ^ (2 * m) := pow_pos a3 _
    calc c / t ^ 2 = (‖u τ₀‖ / 2) ^ 2 / (‖v τ₀‖ + 1) ^ (2 * m) * (1 / t ^ 2) := by
          rw [hc]; ring
      _ ≤ ‖u τ‖ ^ 2 / ‖v τ‖ ^ (2 * m) * ((t ^ l) ^ 2 / (t ^ k) ^ (2 * m)) := by
          refine mul_le_mul ?_ hmain (by positivity) (by positivity)
          exact div_le_div₀ (sq_nonneg _) hu2 hv2pos hv2
      _ = (t ^ l * ‖u τ‖) ^ 2 / (t ^ k * ‖v τ‖) ^ (2 * m) := by
          rw [mul_pow, mul_pow]; field_simp

/-- **Cauchy's formula across removable singularities**: the variant of
`RiemannExtension.cauchy_integral_eq_of_bounded` with local bounds near the zeros of `ψ`. -/
theorem cauchy_integral_eq_of_locally_bounded {ψ φ : ℂ → ℂ} {R ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < R) (hψ : DifferentiableOn ℂ ψ (ball 0 R))
    (hψρ : ∀ τ ∈ sphere (0 : ℂ) ρ, ψ τ ≠ 0)
    (hφ : ∀ τ ∈ ball (0 : ℂ) R, ψ τ ≠ 0 → DifferentiableAt ℂ φ τ)
    (hφb : ∀ τ₀ ∈ ball (0 : ℂ) R, ψ τ₀ = 0 → ∃ C : ℝ, ∀ᶠ τ in 𝓝 τ₀, ψ τ ≠ 0 → ‖φ τ‖ ≤ C)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ) (hψt : ψ t ≠ 0) :
    ((2 * π * I : ℂ)⁻¹ • ∮ τ in C(0, ρ), (τ - t)⁻¹ • φ τ) = φ t := by
  classical
  set φ' : ℂ → ℂ := fun τ => if ψ τ = 0 then limUnder (𝓝[≠] τ) φ else φ τ with hφ'
  have hψa : AnalyticOnNhd ℂ ψ (ball 0 R) := hψ.analyticOnNhd isOpen_ball
  have hρmem : ((ρ : ℂ)) ∈ sphere (0 : ℂ) ρ := by simp [hρ.le]
  have hne : ∀ τ₀ ∈ ball (0 : ℂ) R, ∀ᶠ τ in 𝓝[≠] τ₀, ψ τ ≠ 0 := by
    intro τ₀ hτ₀
    refine (hψa τ₀ hτ₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun H => ?_
    have := hψa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hτ₀ H
      (sphere_subset_ball hρR hρmem)
    exact hψρ _ hρmem this
  have hdiff : DifferentiableOn ℂ φ' (ball 0 R) := by
    intro τ₀ hτ₀
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases h0 : ψ τ₀ = 0
    · obtain ⟨C, hC⟩ := hφb τ₀ hτ₀ h0
      obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1
        ((eventually_nhdsWithin_iff.1 (hne τ₀ hτ₀)).and
          ((show ∀ᶠ τ in 𝓝 τ₀, τ ∈ ball (0 : ℂ) R from isOpen_ball.mem_nhds hτ₀).and hC))
      have hdu := Complex.differentiableOn_update_limUnder_of_bddAbove
        (f := φ) (s := ball τ₀ ε) (c := τ₀) (ball_mem_nhds τ₀ hε)
        (fun τ hτ => (hφ τ (hεs τ hτ.1).2.1 ((hεs τ hτ.1).1 hτ.2)).differentiableWithinAt)
        ⟨C, by
          rintro _ ⟨τ, hτ, rfl⟩
          exact (hεs τ hτ.1).2.2 ((hεs τ hτ.1).1 hτ.2)⟩
      refine (hdu.differentiableAt (ball_mem_nhds τ₀ hε)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds τ₀ hε] with τ hτ
      by_cases hττ : τ = τ₀
      · subst hττ; simp [hφ', h0]
      · simp [hφ', Function.update_of_ne hττ, (hεs τ hτ).1 hττ]
    · have hev : ∀ᶠ τ in 𝓝 τ₀, ψ τ ≠ 0 :=
        (hψ.differentiableAt (isOpen_ball.mem_nhds hτ₀)).continuousAt.eventually_ne h0
      refine (hφ τ₀ hτ₀ h0).congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      simp [hφ', hτ]
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hcauchy := (hdiff.mono hcl).circleIntegral_sub_inv_smul ht
  have hcongr : (∮ τ in C(0, ρ), (τ - t)⁻¹ • φ τ) = ∮ τ in C(0, ρ), (τ - t)⁻¹ • φ' τ :=
    circleIntegral.integral_congr hρ.le fun τ hτ => by simp [hφ', hψρ τ hτ]
  rw [hcongr, hcauchy, inv_smul_smul₀ two_pi_I_ne_zero]
  simp [hφ', hψt]

/-! ### Several variables -/

/-- **`L²` divisibility** (blueprint `relgen:l2-divisibility`): `𝓘(m log |g|²) = (g^m)`. -/
theorem l2DivisibilityStatement : L2DivisibilityStatement := by
  intro d p r hr F g hF hg hne m hint
  classical
  -- a direction along which `g` does not vanish identically
  obtain ⟨w₁, hw₁, hgw₁⟩ : ∃ w₁ ∈ ball p (r / 4), g w₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (eventually_of_mem (ball_mem_nhds p (by positivity)) hall)
  set v := w₁ - p with hvdef
  have hv : ‖v‖ < r / 4 := by rw [hvdef, ← dist_eq_norm]; exact hw₁
  have hLmem : ∀ (y : ComplexModel d) (τ : ℂ), ‖y - p‖ < r / 2 → ‖τ‖ < 2 →
      y + τ • v ∈ ball p r := by
    intro y τ hy hτ
    rw [mem_ball, dist_eq_norm, show y + τ • v - p = (y - p) + τ • v by abel]
    have h1 : ‖τ‖ * ‖v‖ ≤ 2 * (r / 4) :=
      mul_le_mul hτ.le hv.le (norm_nonneg _) (by norm_num)
    calc ‖(y - p) + τ • v‖ ≤ ‖y - p‖ + ‖τ‖ * ‖v‖ := by
          rw [← norm_smul]; exact norm_add_le _ _
      _ < r / 2 + 2 * (r / 4) := by linarith
      _ = r := by ring
  have hgline : ∀ y : ComplexModel d, ‖y - p‖ < r / 2 →
      DifferentiableOn ℂ (fun τ : ℂ => g (y + τ • v)) (ball 0 2) := by
    intro y hy τ hτ
    have hτ' : ‖τ‖ < 2 := by simpa using hτ
    refine ((hg.differentiableAt (isOpen_ball.mem_nhds (hLmem y τ hy hτ'))).comp τ
      ?_).differentiableWithinAt
    fun_prop
  have hFline : ∀ y : ComplexModel d, ‖y - p‖ < r / 2 →
      DifferentiableOn ℂ (fun τ : ℂ => F (y + τ • v)) (ball 0 2) := by
    intro y hy τ hτ
    have hτ' : ‖τ‖ < 2 := by simpa using hτ
    refine ((hF.differentiableAt (isOpen_ball.mem_nhds (hLmem y τ hy hτ'))).comp τ
      ?_).differentiableWithinAt
    fun_prop
  -- the line through `p`
  have hp0 : ‖p - p‖ < r / 2 := by rw [sub_self, norm_zero]; positivity
  have hψ₀a : AnalyticOnNhd ℂ (fun τ : ℂ => g (p + τ • v)) (ball 0 2) :=
    (hgline p hp0).analyticOnNhd isOpen_ball
  have hψ₀1 : g (p + (1 : ℂ) • v) ≠ 0 := by rw [one_smul, hvdef, add_sub_cancel]; exact hgw₁
  have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  have hψ₀ne : ¬ ∀ᶠ τ in 𝓝 (0 : ℂ), g (p + τ • v) = 0 := by
    intro H
    exact hψ₀1 (hψ₀a.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 2).isPreconnected h0mem H h1mem)
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp
    ((hψ₀a 0 h0mem).eventually_eq_zero_or_eventually_ne_zero.resolve_left hψ₀ne))
  set ρ : ℝ := min (ε / 2) (1 / 2) with hρdef
  have hρ : 0 < ρ := lt_min (half_pos hε) (by norm_num)
  have hρ1 : ρ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hψ₀ρ : ∀ τ ∈ sphere (0 : ℂ) ρ, g (p + τ • v) ≠ 0 := by
    intro τ hτ
    have hτn : ‖τ‖ = ρ := by simpa using hτ
    refine hεs τ ?_ ?_
    · rw [mem_ball, dist_zero_right, hτn]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    · intro h0
      rw [h0, norm_zero] at hτn
      exact hρ.ne hτn
  -- the tube around `{p} × sphere 0 ρ`
  set O₁ : Set (ComplexModel d × ℂ) :=
    (fun q : ComplexModel d × ℂ => q.1 + q.2 • v) ⁻¹' (ball p r ∩ g ⁻¹' {0}ᶜ) with hO₁
  have hO₁o : IsOpen O₁ :=
    (hg.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).preimage
      (by fun_prop)
  obtain ⟨δ₀, hδ₀, hδ₀s⟩ := (isCompact_singleton.prod (isCompact_sphere (0 : ℂ) ρ)
    ).exists_cthickening_subset_open hO₁o (by
      rintro ⟨y, τ⟩ ⟨hy, hτ⟩
      rw [mem_singleton_iff] at hy
      subst hy
      have hτn : ‖τ‖ = ρ := by simpa using hτ
      exact ⟨hLmem _ τ hp0 (by rw [hτn]; linarith), hψ₀ρ τ hτ⟩)
  have htube : ∀ y ∈ ball p δ₀, ∀ τ ∈ sphere (0 : ℂ) ρ, (y, τ) ∈ O₁ := by
    intro y hy τ hτ
    refine hδ₀s (Metric.mem_cthickening_of_dist_le _ (p, τ) δ₀ _ ⟨rfl, hτ⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨(mem_ball.mp hy).le, hδ₀.le⟩
  set δ₁ := min δ₀ (r / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (half_pos hr)
  have hball₁ : ∀ y ∈ ball p δ₁, ‖y - p‖ < r / 2 := fun y hy => by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _)
  have hball₀ : ∀ y ∈ ball p δ₁, y ∈ ball p δ₀ := fun y hy =>
    ball_subset_ball (min_le_left _ _) hy
  -- the Cauchy integral
  set φ : ComplexModel d → ℂ := fun w => F w / g w ^ m with hφ
  have hφdiff : ∀ w ∈ ball p r, g w ≠ 0 → DifferentiableAt ℂ φ w := by
    intro w hw hgw
    have h1 := hF.differentiableAt (isOpen_ball.mem_nhds hw)
    have h2 : DifferentiableAt ℂ (fun w => g w ^ m) w :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hw)).pow m
    have h3 : DifferentiableAt ℂ (fun w => F w * (g w ^ m)⁻¹) w :=
      h1.mul (h2.inv (pow_ne_zero _ hgw))
    exact h3.congr_of_eventuallyEq (Eventually.of_forall fun w => div_eq_mul_inv _ _)
  set Fext : ComplexModel d → ℂ := fun y =>
    (2 * π * I : ℂ)⁻¹ • ∮ τ in C(0, ρ), τ⁻¹ • φ (y + τ • v) with hFext
  have hFextd : ∀ y ∈ ball p δ₁, DifferentiableAt ℂ Fext y := by
    intro y₀ hy₀
    set O : Set (ComplexModel d × ℂ) := O₁ ∩ {q | q.2 ≠ 0}
    have hOo : IsOpen O := hO₁o.inter (isOpen_ne_fun continuous_snd continuous_const)
    have hΨ : DifferentiableOn ℂ (fun q : ComplexModel d × ℂ => q.2⁻¹ • φ (q.1 + q.2 • v)) O := by
      intro q hq
      refine DifferentiableAt.differentiableWithinAt ?_
      have hw : q.1 + q.2 • v ∈ ball p r := hq.1.1
      have hgw : g (q.1 + q.2 • v) ≠ 0 := hq.1.2
      have hφd : DifferentiableAt ℂ φ (q.1 + q.2 • v) := hφdiff _ hw hgw
      have hlin : DifferentiableAt ℂ (fun q : ComplexModel d × ℂ => q.1 + q.2 • v) q := by
        fun_prop
      have hc : DifferentiableAt ℂ (φ ∘ fun q : ComplexModel d × ℂ => q.1 + q.2 • v) q :=
        hφd.comp q hlin
      exact (differentiableAt_snd.inv hq.2).smul hc
    have := RiemannExtension.differentiableAt_circleIntegral_param hOo hΨ hρ.le (p₀ := y₀)
      fun τ hτ => ⟨htube y₀ (hball₀ y₀ hy₀) τ hτ, by
        intro h0
        have h0' : τ = 0 := h0
        rw [h0'] at hτ
        simp only [mem_sphere_iff_norm, sub_zero, norm_zero] at hτ
        exact hρ.ne hτ⟩
    exact (this.const_smul ((2 * π * I : ℂ)⁻¹)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => rfl)
  -- a measurable version of the integrand, and Tonelli along the lines
  set f : ComplexModel d → ℝ≥0∞ := (ball p r).indicator
    (fun w => ENNReal.ofReal (‖F w‖ ^ 2) / ENNReal.ofReal (‖g w‖ ^ (2 * m))) with hfdef
  have hfmeas : Measurable f := by
    have hA : Measurable ((ball p r).piecewise (fun w => ENNReal.ofReal (‖F w‖ ^ 2))
        (fun _ => 0)) :=
      ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (hF.continuousOn.norm.pow 2))
        continuousOn_const measurableSet_ball
    have hB : Measurable ((ball p r).piecewise (fun w => ENNReal.ofReal (‖g w‖ ^ (2 * m)))
        (fun _ => 1)) :=
      ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (hg.continuousOn.norm.pow _))
        continuousOn_const measurableSet_ball
    convert hA.div hB using 1
    funext w
    by_cases hw : w ∈ ball p r
    · simp [hfdef, hw, Set.piecewise]
    · simp [hfdef, hw, Set.piecewise]
  have hfint : ∫⁻ w, f w ≠ ⊤ := by rw [hfdef, lintegral_indicator measurableSet_ball]; exact hint
  set H : ComplexModel d → ℂ → ℝ≥0∞ := fun y τ =>
    f (y + τ • v) * (ball (0 : ℂ) 2).indicator 1 τ with hH
  have hHmeas : Measurable (Function.uncurry H) :=
    (hfmeas.comp (by fun_prop : Continuous fun q : ComplexModel d × ℂ => q.1 + q.2 • v).measurable
      ).mul ((measurable_one.indicator measurableSet_ball).comp measurable_snd)
  have hswap : ∫⁻ y, ∫⁻ τ, H y τ ≠ ⊤ := by
    rw [lintegral_lintegral_swap hHmeas.aemeasurable]
    have : ∀ τ : ℂ, ∫⁻ y, H y τ = (∫⁻ w, f w) * (ball (0 : ℂ) 2).indicator 1 τ := by
      intro τ
      simp only [hH]
      have hm : Measurable fun y => f (y + τ • v) := hfmeas.comp (measurable_add_const _)
      rw [lintegral_mul_const _ hm,
        lintegral_add_right_eq_self (μ := (volume : Measure (ComplexModel d))) f (τ • v)]
    simp only [this]
    rw [lintegral_const_mul _ ((measurable_one.indicator measurableSet_ball)),
      lintegral_indicator_one measurableSet_ball]
    exact ENNReal.mul_ne_top hfint measure_ball_lt_top.ne
  have hgood : ∀ᵐ y : ComplexModel d, ∫⁻ τ, H y τ < ⊤ :=
    ae_lt_top (hHmeas.lintegral_prod_right') hswap
  set Good : Set (ComplexModel d) := {y | ∫⁻ τ, H y τ < ⊤} with hGood
  have hGoodc : volume Goodᶜ = 0 := by
    rw [hGood, compl_ofPred]
    exact ae_iff.mp hgood
  -- the Cauchy formula on good slices
  have hslice : ∀ y ∈ ball p δ₁, y ∈ Good → g y ≠ 0 → Fext y = φ y := by
    intro y hy hyG hgy
    have hyr := hball₁ y hy
    have hsl : ∫⁻ τ in ball (0 : ℂ) 2, ENNReal.ofReal (‖F (y + τ • v)‖ ^ 2) /
        ENNReal.ofReal (‖g (y + τ • v)‖ ^ (2 * m)) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hyG)
      rw [← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun τ => ?_
      by_cases hτ : τ ∈ ball (0 : ℂ) 2
      · have hτ' : ‖τ‖ < 2 := by simpa using hτ
        simp [hH, hfdef, indicator_of_mem hτ, indicator_of_mem (hLmem y τ hyr hτ')]
      · simp [hH, indicator_of_notMem hτ]
    have hψd : DifferentiableOn ℂ (fun τ : ℂ => g (y + τ • v)) (ball 0 1) :=
      (hgline y hyr).mono (ball_subset_ball (by norm_num))
    have hψρ : ∀ τ ∈ sphere (0 : ℂ) ρ, g (y + τ • v) ≠ 0 := fun τ hτ =>
      (htube y (hball₀ y hy) τ hτ).2
    have hcf := cauchy_integral_eq_of_locally_bounded (ψ := fun τ : ℂ => g (y + τ • v))
      (φ := fun τ : ℂ => φ (y + τ • v)) hρ hρ1 hψd hψρ ?_ ?_
      (t := 0) (mem_ball_self hρ) (by simpa using hgy)
    · simpa [hFext] using hcf
    · intro τ hτ hψτ
      have hτ' : ‖τ‖ < 2 := by have := mem_ball_zero_iff.mp hτ; linarith
      have hw := hLmem y τ hyr hτ'
      have hl : DifferentiableAt ℂ (fun τ : ℂ => y + τ • v) τ :=
        (differentiableAt_const _).add (differentiableAt_id.smul_const v)
      have hc : DifferentiableAt ℂ (φ ∘ fun τ : ℂ => y + τ • v) τ := (hφdiff _ hw hψτ).comp τ hl
      exact hc
    · intro τ₀ hτ₀ hψτ₀
      have hτ₀2 : τ₀ ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hτ₀
      have hψa : AnalyticOnNhd ℂ (fun τ : ℂ => g (y + τ • v)) (ball 0 1) :=
        hψd.analyticOnNhd isOpen_ball
      have hρmem : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ := by simp [hρ.le]
      have hψne : ¬ ∀ᶠ τ in 𝓝 τ₀, g (y + τ • v) = 0 := by
        intro H'
        exact hψρ _ hρmem (hψa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball (0 : ℂ) 1).isPreconnected hτ₀ H' (sphere_subset_ball hρ1 hρmem))
      have hδ : 0 < 1 - ‖τ₀‖ := by have := mem_ball_zero_iff.mp hτ₀; linarith
      have hsub : ball τ₀ (1 - ‖τ₀‖) ⊆ ball (0 : ℂ) 2 := by
        intro τ hτ
        rw [mem_ball, dist_eq_norm] at hτ
        rw [mem_ball_zero_iff]
        calc ‖τ‖ ≤ ‖τ - τ₀‖ + ‖τ₀‖ := by
              have := norm_add_le (τ - τ₀) τ₀
              rwa [sub_add_cancel] at this
          _ < 2 := by linarith
      obtain ⟨C, hC⟩ := exists_bound_of_lintegral_ne_top
        ((hgline y hyr).analyticAt (isOpen_ball.mem_nhds hτ₀2))
        ((hFline y hyr).analyticAt (isOpen_ball.mem_nhds hτ₀2)) hψne m hδ
        (ne_top_of_le_ne_top hsl (lintegral_mono_set hsub))
      exact ⟨C, hC⟩
  -- density of good points
  set S : Set (ComplexModel d) := ball p δ₁ ∩ {y | g y ≠ 0} with hS
  have hSo : IsOpen S :=
    hg.continuousOn.mono (ball_subset_ball ((min_le_right _ _).trans (by linarith)))
      |>.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hSdense : S ⊆ closure (S ∩ Good) := by
    intro y hy
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨N', hN'sub, hN'o, hyN'⟩ := _root_.mem_nhds_iff.mp hN
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hpos : 0 < volume (N' ∩ S) := (hN'o.inter hSo).measure_pos volume ⟨y, hyN', hy⟩
    have hsub : N' ∩ S ⊆ Goodᶜ := by
      intro w hw hwG
      have : w ∈ N ∩ (S ∩ Good) := ⟨hN'sub hw.1, hw.2, hwG⟩
      rw [hemp] at this
      exact this
    exact hpos.ne' (measure_mono_null hsub hGoodc)
  have hFextc : ContinuousOn Fext S := fun y hy =>
    (hFextd y hy.1).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ S := by
    intro y hy
    have hyr : y ∈ ball p r := ball_subset_ball ((min_le_right _ _).trans (by linarith)) hy.1
    exact (hφdiff y hyr hy.2).continuousAt.continuousWithinAt
  have hEqS : EqOn Fext φ S :=
    Set.EqOn.of_subset_closure (f := Fext) (g := φ)
      (fun y hy => hslice y hy.1.1 hy.2 hy.1.2) hFextc hφc inter_subset_left hSdense
  -- conclusion
  have hgU : DifferentiableOn ℂ g (ball p δ₁) :=
    hg.mono (ball_subset_ball ((min_le_right _ _).trans (by linarith)))
  have hdense := RiemannExtension.dense_compl_zeroSet isOpen_ball
    (convex_ball p δ₁).isPreconnected hgU (mem_ball_self hδ₁0) hne
  have hSeq : ball p δ₁ \ g ⁻¹' {0} = S := by
    ext y; simp [hS]
  rw [hSeq] at hdense
  have hFc : ContinuousOn F (ball p δ₁) :=
    hF.continuousOn.mono (ball_subset_ball ((min_le_right _ _).trans (by linarith)))
  have hFextcU : ContinuousOn Fext (ball p δ₁) := fun y hy =>
    (hFextd y hy).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (fun w => Fext w * g w ^ m) (ball p δ₁) :=
    hFextcU.mul (hgU.continuousOn.pow m)
  have hEqU : EqOn F (fun w => Fext w * g w ^ m) (ball p δ₁) := by
    refine EqOn.of_subset_closure ?_ hFc hGc (fun y hy => hy.1) hdense
    intro y hy
    simp only
    rw [hEqS hy, hφ, div_mul_cancel₀ _ (pow_ne_zero _ hy.2)]
  refine ⟨Fext, eventually_of_mem (ball_mem_nhds p hδ₁0) hFextd,
    eventually_of_mem (ball_mem_nhds p hδ₁0) fun y hy => hEqU hy⟩

/-- **Relative global generation from the `L²` generation theorem alone.** -/
theorem relativeGlobalGeneration_of_l2Generation'
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) :
    RelativeGlobalGenerationStatement.{u} :=
  relativeGlobalGeneration_of_l2Generation hL2 l2DivisibilityStatement

end SGPT.Okounkov.TranscendentalRelGen
