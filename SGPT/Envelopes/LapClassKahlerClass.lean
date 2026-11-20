import SGPT.Envelopes.LapClassKahler

/-!
# `prop:DR16_C11bar` for any reference metric and `thm:DNT23_C11bar` for Kähler classes

Lane LAP-CLASS (`claude-lap-class`, nodes `lap-class:dr16-gen`, `lap-class:dnt23`).  Here the
class `C^{1,1̄}_ω(X)` (`HasBoundedMetricLaplacian w`) is taken with respect to an arbitrary Kähler
form `ω = w`, and the envelope is taken in another Kähler class `κ = A` (FPT
`thm:kahler-metric-laplacian-rooftop` as stated there).

* `envelope_laplacian_of_chartSmooth_gen`: for a smooth obstacle `F` with `Δ_ω F ≤ S`, `|F| ≤ B`,
  `P_κ(F)` is real-valued, continuous and `-T_κ ≤ Δ_ω P_κ(F) ≤ 2(T + S) e^{a(2B + 1)}`.
* `envelope_min_hasBoundedMetricLaplacian_gen`: `P_κ(min{f₁, f₂}) ∈ C^{1,1̄}_ω(X)` for
  `f₁, f₂ ∈ C^{1,1̄}_ω(X)` (**`prop:DR16_C11bar` for every reference metric**).
* `HasBoundedMetricLaplacian.add_smul_chartSmooth`: the class is stable under adding `c ρ`, `ρ`
  smooth.
* `envelopeReal_hasBoundedMetricLaplacian_of_kahlerClass` (**`thm:DNT23_C11bar` for Kähler
  classes**): if `θ + ddᶜρ` is Kähler and `f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f)` is real-valued and in
  `C^{1,1̄}_ω(X)`, hence on `X ∖ nK({θ})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem traceForm_nonneg {g α : SmoothRealForm N Y 2} (hg : g.IsHermitian) (hα : α.IsKahler)
    (y : Y) : 0 ≤ traceForm g α y := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [traceForm, chartTrace, Matrix.trace]
  · exact (traceForm_pos hN hg hα y).le

variable [MeasurableSpace Y] [BorelSpace Y]

/-- **The Laplacian of the envelope of a smooth obstacle, general background.** -/
theorem envelope_laplacian_of_chartSmooth_gen [CompactSpace Y] [ConnectedSpace Y]
    (w A : KahlerBackground N Y) :
    ∃ a T Tκ : ℝ, 0 ≤ a ∧ 0 ≤ T ∧ ∀ (F : Y → ℝ), ChartSmooth (n := N) F → ∀ S B : ℝ,
      (∀ y, laplacian w.form.val F y ≤ S) → (∀ y, |F y| ≤ B) →
      (∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
        ((envelopeReal A.form F x : ℝ) : EReal)) ∧
      Continuous (envelopeReal A.form F) ∧
      LaplacianLE w (envelopeReal A.form F) (2 * (T + S) * Real.exp (a * (2 * B + 1))) ∧
      LaplacianGE w (envelopeReal A.form F) (-Tκ) := by
  obtain ⟨a, T, β₀, ha0, hT0, hβ₀, htr⟩ := betaSolution_traceForm_le w A
  have hg : w.form.val.IsHermitian := w.isKahler.1
  obtain ⟨Tκ, hTκ⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_traceForm hg A.form).continuousOn
  refine ⟨a, T, Tκ, ha0, hT0, fun F hF S B hFS hB => ?_⟩
  obtain ⟨S', hS'0, hFS'⟩ := exists_ddc_line_le_of_chartSmooth A hF
  set c₀ : ℝ := max β₀ 1 with hc₀def
  set β : ℕ → ℝ := fun j => (j : ℝ) + c₀ with hβdef
  have hβ1 : ∀ j, 1 ≤ β j := fun j => by
    have := le_max_right β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hββ₀ : ∀ j, β₀ ≤ β j := fun j => by
    have := le_max_left β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hβpos : ∀ j, 0 < β j := fun j => by linarith [hβ1 j]
  have U : ∀ j, BetaSolution A (β j) F := fun j =>
    Classical.choice (exists_betaSolution A (hβpos j) hF)
  set ε : ℕ → ℝ := fun j => (N * Real.log (1 + S') + 2 * B) / β j + N * (Real.log (β j) / β j)
    with hεdef
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 := tendsto_const_div_natCast_add (N * Real.log (1 + S') + 2 * B) c₀
    have h2 := (tendsto_log_div_natCast_add c₀).const_mul (N : ℝ)
    simpa [hεdef, hβdef] using h1.add h2
  have hS1 : 0 ≤ Real.log (1 + S') := Real.log_nonneg (by linarith)
  have hbd := fun j x => envelope_bounds A (hβ1 j) hF hS'0 hFS' hB (U j) x
  have hfin : ∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
      ((envelopeReal A.form F x : ℝ) : EReal) := by
    intro x
    obtain ⟨h1, h2⟩ := hbd 0 x
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)).symm
  have hclose : ∀ j x, |(U j).u x - envelopeReal A.form F x| ≤ ε j := by
    intro j x
    obtain ⟨h1, h2⟩ := hbd j x
    rw [hfin x] at h1 h2
    have h1' := EReal.coe_le_coe_iff.mp h1
    have h2' := EReal.coe_le_coe_iff.mp h2
    have hβj := hβpos j
    have hεj : ε j = N * Real.log (1 + S') / β j + (2 * B + N * Real.log (β j)) / β j := by
      simp only [hεdef]
      field_simp
      ring
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
    have p1 : 0 ≤ N * Real.log (1 + S') / β j := by positivity
    have p2 : 0 ≤ (2 * B + N * Real.log (β j)) / β j := by
      have : 0 ≤ Real.log (β j) := Real.log_nonneg (hβ1 j)
      positivity
    rw [abs_le]
    constructor <;> linarith
  have hconv : TendstoUniformly (fun j => (U j).u) (envelopeReal A.form F) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro r hr
    filter_upwards [(hεlim.eventually (gt_mem_nhds hr))] with j hj x
    rw [Real.dist_eq, abs_sub_comm]
    exact (hclose j x).trans_lt hj
  have hcont : ∀ j, Continuous (U j).u := fun j =>
    YauUniformEstimate.continuous_of_chartSmooth (U j).smooth
  refine ⟨hfin, hconv.continuous (Frequently.of_forall hcont), ?_, ?_⟩
  · refine laplacianLE_of_tendstoUniformly w hcont hconv ?_
    have hev : ∀ᶠ j in atTop, N * Real.log (1 + S') / β j ≤ 1 := by
      have h := tendsto_const_div_natCast_add (N * Real.log (1 + S')) c₀
      filter_upwards [h.eventually (ge_mem_nhds one_pos)] with j hj
      simpa [hβdef] using hj
    filter_upwards [hev] with j hj
    refine laplacianLE_of_chartSmooth w (U j).smooth fun y => ?_
    have hm : ∀ x, -B ≤ (U j).u x := fun x =>
      le_betaSolution_of_le (hβpos j) (fun x => (abs_le.mp (hB x)).1) (U j) x
    have h := htr (β j) (hββ₀ j) F hF S hFS (U j) (-B) hm y
    have hup := betaSolution_le_add (hβpos j) hF hS'0 hFS' (U j) y
    have hFy := (abs_le.mp (hB y)).2
    have hexp : Real.exp (a * ((U j).u y - -B)) ≤ Real.exp (a * (2 * B + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ha0)
    have hsplit := traceForm_add_ddc w A (U j).smooth y
    have hκ0 := traceForm_nonneg hg A.isKahler y
    have hTS : 0 ≤ 2 * (T + S) := by
      by_contra hneg
      push Not at hneg
      have : 2 * (T + S) * Real.exp (a * ((U j).u y - -B)) < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      have h0 := traceForm_nonneg hg (U j).isKahler y
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hexp hTS]
  · refine laplacianGE_of_tendstoUniformly w hcont hconv (Eventually.of_forall fun j => ?_)
    refine laplacianGE_of_chartSmooth w (U j).smooth fun y => ?_
    have hsplit := traceForm_add_ddc w A (U j).smooth y
    have h0 := traceForm_nonneg hg (U j).isKahler y
    have h1 := hTκ y (mem_univ y)
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (traceForm w.form.val A.form.val y)]

/-- **`prop:DR16_C11bar` for an arbitrary reference metric**: for Kähler forms `ω` (the metric of
`C^{1,1̄}_ω(X)`) and `κ` (the class of the envelope) and continuous `f₁, f₂` with `Δ_ω fᵢ ≤ Sᵢ`,
`P_κ(min{f₁, f₂})` is real-valued and lies in `C^{1,1̄}_ω(X)`. -/
theorem envelope_min_hasBoundedMetricLaplacian_gen_of_le [CompactSpace Y] [ConnectedSpace Y]
    (w A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    {S₁ S₂ : ℝ} (hS₁ : LaplacianLE w f₁ S₁) (hS₂ : LaplacianLE w f₂ S₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian w (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  classical
  obtain ⟨a, T, Tκ, ha0, hT0, hEnv⟩ := envelope_laplacian_of_chartSmooth_gen w A
  set S := max S₁ S₂ + 2 with hSdef
  obtain ⟨B₁, hB₁⟩ := isCompact_univ.exists_bound_of_continuousOn h₁.continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_univ.exists_bound_of_continuousOn h₂.continuousOn
  set B := max B₁ B₂ + 5 with hBdef
  set η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hηdef
  have hη : ∀ k, 0 < η k := fun k => by positivity
  have hη1 : ∀ k, η k ≤ 1 := fun k => by
    simp only [hηdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  choose g₁ hg₁ hg₁f hg₁L using fun k => exists_smooth_laplacian_le w h₁ hS₁ (hη k)
  choose g₂ hg₂ hg₂f hg₂L using fun k => exists_smooth_laplacian_le w h₂ hS₂ (hη k)
  set F : ℕ → Y → ℝ := fun k => smoothMin (η k) (g₁ k) (g₂ k) with hFdef
  have hF : ∀ k, ChartSmooth (n := N) (F k) := fun k => chartSmooth_smoothMin (η k) (hg₁ k) (hg₂ k)
  have hFL : ∀ k y, laplacian w.form.val (F k) y ≤ S := fun k y =>
    laplacian_smoothMin_le (hη k) w (hg₁ k) (hg₂ k)
      (fun y => (hg₁L k y).trans (by have := hη1 k; have := le_max_left S₁ S₂; linarith))
      (fun y => (hg₂L k y).trans (by have := hη1 k; have := le_max_right S₁ S₂; linarith)) y
  have hFclose : ∀ k y, |F k y - min (f₁ y) (f₂ y)| ≤ 5 * η k := by
    intro k y
    have h1 := abs_smoothMin_sub_le (hη k) (g₁ k) (g₂ k) y
    have h2 : |min (g₁ k y) (g₂ k y) - min (f₁ y) (f₂ y)| ≤ 4 * η k :=
      (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hg₁f k y) (hg₂f k y))
    calc |F k y - min (f₁ y) (f₂ y)| ≤ |F k y - min (g₁ k y) (g₂ k y)| +
          |min (g₁ k y) (g₂ k y) - min (f₁ y) (f₂ y)| := abs_sub_le _ _ _
      _ ≤ η k + 4 * η k := add_le_add h1 h2
      _ = 5 * η k := by ring
  have hFB : ∀ k y, |F k y| ≤ B := by
    intro k y
    have h1 := hFclose k y
    have hm : |min (f₁ y) (f₂ y)| ≤ max B₁ B₂ := by
      have a1 := hB₁ y (mem_univ y)
      have a2 := hB₂ y (mem_univ y)
      rw [Real.norm_eq_abs] at a1 a2
      rw [abs_le] at a1 a2 ⊢
      constructor
      · exact le_min (by linarith [le_max_left B₁ B₂]) (by linarith [le_max_right B₁ B₂])
      · exact (min_le_left _ _).trans (by linarith [le_max_left B₁ B₂])
    have := hη1 k
    calc |F k y| = |(F k y - min (f₁ y) (f₂ y)) + min (f₁ y) (f₂ y)| := by ring_nf
      _ ≤ |F k y - min (f₁ y) (f₂ y)| + |min (f₁ y) (f₂ y)| := abs_add_le _ _
      _ ≤ B := by rw [hBdef]; linarith
  have hE := fun k => hEnv (F k) (hF k) S B (hFL k) (hFB k)
  have hsand := fun k => envelope_sandwich A.form (F := F k)
    (G := fun y => min (f₁ y) (f₂ y)) (c := 5 * η k)
    (fun y => hFclose k y) (hE k).1
  have hconv : TendstoUniformly (fun k => envelopeReal A.form (F k))
      (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (show 0 < δ / 5 by positivity)
    filter_upwards [eventually_ge_atTop k₀] with k hk x
    rw [Real.dist_eq]
    have h1 := (hsand k).2 x
    have h2 := one_div_succ_le_one_div_succ hk
    simp only [hηdef] at h1
    linarith
  have hcont : ∀ k, Continuous (envelopeReal A.form (F k)) := fun k => (hE k).2.1
  refine ⟨(hsand 0).1, hconv.continuous (Frequently.of_forall hcont),
    max (2 * (T + S) * Real.exp (a * (2 * B + 1))) Tκ, ?_, ?_⟩
  · refine laplacianLE_of_tendstoUniformly w hcont hconv (Eventually.of_forall fun k => ?_)
    intro χ hχ hχ0
    exact ((hE k).2.2.1 χ hχ hχ0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg hχ0))
  · refine laplacianGE_of_tendstoUniformly w hcont hconv (Eventually.of_forall fun k => ?_)
    intro χ hχ hχ0
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg hχ0)) ((hE k).2.2.2 χ hχ hχ0)
    have := le_max_right (2 * (T + S) * Real.exp (a * (2 * B + 1))) Tκ
    linarith

/-- **`prop:DR16_C11bar` for every reference metric**: `P_κ(min{f₁, f₂}) ∈ C^{1,1̄}_ω(X)` for
`f₁, f₂ ∈ C^{1,1̄}_ω(X)` and Kähler forms `κ`, `ω`. -/
theorem envelope_min_hasBoundedMetricLaplacian_gen [CompactSpace Y] [ConnectedSpace Y]
    (w A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : HasBoundedMetricLaplacian w f₁)
    (h₂ : HasBoundedMetricLaplacian w f₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian w (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  obtain ⟨hc₁, M₁, hM₁, -⟩ := h₁
  obtain ⟨hc₂, M₂, hM₂, -⟩ := h₂
  exact envelope_min_hasBoundedMetricLaplacian_gen_of_le w A hc₁ hc₂ hM₁ hM₂

/-! ### Smooth shifts and Kähler classes -/

/-- The class is stable under adding `c ρ` with `ρ` smooth. -/
theorem HasBoundedMetricLaplacian.add_smul_chartSmooth [CompactSpace Y] (w : KahlerBackground N Y)
    {f ρ : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (hρ : ChartSmooth (n := N) ρ) (c : ℝ) :
    HasBoundedMetricLaplacian w (fun y => f y + c * ρ y) := by
  obtain ⟨hfc, M, hLE, hGE⟩ := hf
  have hcρ : ChartSmooth (n := N) (fun y => c * ρ y) := fun e => contDiffOn_const.mul (hρ e)
  obtain ⟨Bρ, hBρ⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_laplacian_of_chartSmooth w.isKahler.1 hcρ).continuousOn
  have hB : ∀ y, |laplacian w.form.val (fun y => c * ρ y) y| ≤ Bρ := fun y => by
    have := hBρ y (mem_univ y); rwa [Real.norm_eq_abs] at this
  have hρc := YauUniformEstimate.continuous_of_chartSmooth hcρ
  have hsplit : ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
      ∫ y, (f y + c * ρ y) * laplacian w.form.val χ y ∂(kahlerVolume w) =
        ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) +
          ∫ y, χ y * laplacian w.form.val (fun y => c * ρ y) y ∂(kahlerVolume w) := by
    intro χ hχ
    have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
    have e1 := integral_mul_laplacian_comm w hcρ hχ
    have e2 : ∫ y, (f y * laplacian w.form.val χ y + c * ρ y * laplacian w.form.val χ y)
        ∂(kahlerVolume w) = ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) +
          ∫ y, c * ρ y * laplacian w.form.val χ y ∂(kahlerVolume w) :=
      integral_add (integral_continuous (hfc.mul hL) _) (integral_continuous (hρc.mul hL) _)
    have e3 : ∫ y, (f y + c * ρ y) * laplacian w.form.val χ y ∂(kahlerVolume w) =
        ∫ y, (f y * laplacian w.form.val χ y + c * ρ y * laplacian w.form.val χ y)
          ∂(kahlerVolume w) :=
      integral_congr_ae (Eventually.of_forall fun y => by
        show (f y + c * ρ y) * laplacian w.form.val χ y =
          f y * laplacian w.form.val χ y + c * ρ y * laplacian w.form.val χ y
        ring)
    rw [e3, e2, e1]
  have hbound : ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
      |∫ y, χ y * laplacian w.form.val (fun y => c * ρ y) y ∂(kahlerVolume w)| ≤
        Bρ * ∫ y, χ y ∂(kahlerVolume w) := by
    intro χ hχ hχ0
    have hcχ := YauUniformEstimate.continuous_of_chartSmooth hχ
    have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hcρ
    have e1 : ∫ y, Bρ * χ y ∂(kahlerVolume w) = Bρ * ∫ y, χ y ∂(kahlerVolume w) :=
      integral_const_mul _ _
    rw [← e1]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      (integral_continuous (hcχ.mul hL).abs _) (integral_continuous (continuous_const.mul hcχ) _)
      fun y => ?_)
    show |χ y * laplacian w.form.val (fun y => c * ρ y) y| ≤ Bρ * χ y
    rw [abs_mul, abs_of_nonneg (hχ0 y), mul_comm Bρ]
    exact mul_le_mul_of_nonneg_left (hB y) (hχ0 y)
  refine ⟨hfc.add (continuous_const.mul (YauUniformEstimate.continuous_of_chartSmooth hρ)),
    M + Bρ, fun χ hχ hχ0 => ?_, fun χ hχ hχ0 => ?_⟩
  · rw [hsplit χ hχ]
    have h1 := hLE χ hχ hχ0
    have h2 := (abs_le.mp (hbound χ hχ hχ0)).2
    linarith
  · rw [hsplit χ hχ]
    have h1 := hGE χ hχ hχ0
    have h2 := (abs_le.mp (hbound χ hχ hχ0)).1
    linarith

/-- **Source `thm:DNT23_C11bar` for Kähler classes, bounded-Laplacian obstacles.**  Let `θ` be a
closed real `(1,1)`-form whose class is Kähler (`θ + ddᶜρ` Kähler for a chart-smooth `ρ`), and
`f ∈ C^{1,1̄}_ω(X)` for a Kähler form `ω`.  Then `P_θ(f)` is real-valued and lies in
`C^{1,1̄}_ω(X)` (on all of `X`, in particular on `X ∖ nK({θ})`). -/
theorem envelopeReal_hasBoundedMetricLaplacian_of_kahlerClass [CompactSpace Y] [ConnectedSpace Y]
    (w : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y) {ρ : Y → ℝ}
    (hρ : ChartSmooth (n := N) ρ) (hK : (θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    (∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal θ f x : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian w (envelopeReal θ f) := by
  set A : KahlerBackground N Y := ⟨θ + ddcClosedForm ρ hρ, hK⟩ with hAdef
  have hfρ : HasBoundedMetricLaplacian w (fun y => f y - ρ y) := by
    have := hf.add_smul_chartSmooth w hρ (-1)
    simpa [sub_eq_add_neg] using this
  obtain ⟨hreal, hcls⟩ := envelope_min_hasBoundedMetricLaplacian_gen w A hfρ hfρ
  simp only [min_self] at hreal hcls
  have hshift : ∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal A.form (fun y => f y - ρ y) x + ρ x : ℝ) : EReal) := by
    intro x
    rw [rooftopEnvelope_shift θ hρ f x, EReal.coe_add]
    congr 1
    exact hreal x
  have heq : envelopeReal θ f = fun x => envelopeReal A.form (fun y => f y - ρ y) x + 1 * ρ x := by
    funext x
    simp only [envelopeReal] at hshift ⊢
    rw [hshift x, EReal.toReal_coe, one_mul]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hshift x]
    congr 1
    rw [heq]
    ring
  · rw [heq]
    exact hcls.add_smul_chartSmooth w hρ 1


/-! ### The class on a subset, and the source envelopes -/

/-- **`C^{1,1̄}_ω(U)` on a subset `U ⊆ X`**: `f` is continuous on `U` and its distributional
`ω`-Laplacian is bounded on every compact `K ⊆ U`, i.e. `|∫ f Δ_ω χ ω^N| ≤ M_K ∫ χ ω^N` for all
smooth `χ ≥ 0` supported in `K` (FPT `thm:big-metric-laplacian-rooftop`: "bounded metric
Laplacian on every compact subset"). -/
def HasBoundedMetricLaplacianOn [CompactSpace Y] (w : KahlerBackground N Y) (U : Set Y)
    (f : Y → ℝ) : Prop :=
  ContinuousOn f U ∧ ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
    (∀ y, 0 ≤ χ y) → tsupport χ ⊆ K →
      |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤ M * ∫ y, χ y ∂(kahlerVolume w)

omit [BorelSpace Y] in
/-- `C^{1,1̄}_ω(X) ⊆ C^{1,1̄}_ω(U)`. -/
theorem HasBoundedMetricLaplacian.hasBoundedMetricLaplacianOn [CompactSpace Y]
    (w : KahlerBackground N Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (U : Set Y) :
    HasBoundedMetricLaplacianOn w U f := by
  obtain ⟨hc, M, hLE, hGE⟩ := hf
  refine ⟨hc.continuousOn, fun K _ _ => ⟨M, fun χ hχ hχ0 _ => abs_le.mpr ⟨?_, hLE χ hχ hχ0⟩⟩⟩
  have h := hGE χ hχ hχ0
  rw [neg_mul] at h
  exact h

section Source

open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- **Source `prop:DR16_C11bar` in the bounded-Laplacian class, with the source envelope**
`P_ω(min{f₁, f₂}) = sourceRelativeEnvelope ω ⊤ min{f₁, f₂}` (`def:Pthetaf`): for a Kähler form
`ω` and `f₁, f₂ ∈ C^{1,1̄}_ω(X)` the envelope is real-valued and lies in `C^{1,1̄}_ω(X)`. -/
theorem sourceObstacleEnvelope_min_hasBoundedMetricLaplacian [CompactSpace Y] [ConnectedSpace Y]
    (w : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hK : (atlasClosedFormToNative w).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative w, hK⟩ f₁)
    (h₂ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative w, hK⟩ f₂) :
    (∀ x, sourceRelativeEnvelope w (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      (((sourceRelativeEnvelope w (fun _ => ⊤)
        (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian ⟨atlasClosedFormToNative w, hK⟩
      (fun x => (sourceRelativeEnvelope w (fun _ => ⊤)
        (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal) := by
  obtain ⟨hreal, hC⟩ := envelope_min_hasBoundedMetricLaplacian ⟨atlasClosedFormToNative w, hK⟩ h₁ h₂
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

/-- **Source `thm:DNT23_C11bar` for Kähler classes, bounded-Laplacian obstacles, with the source
envelope** `P_θ(f) = sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`): if `θ + ddᶜρ` is Kähler and
`f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f)` is real-valued and lies in `C^{1,1̄}_ω(X ∖ nK({θ}))`, with
`nK({θ}) = sourceNonKahlerLocus` (`def:nKlocus`). -/
theorem sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_kahlerClass [CompactSpace Y]
    [ConnectedSpace Y] (w : KahlerBackground N Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y)) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (atlasClosedFormToNative θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    (∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
      (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  obtain ⟨hreal, hC⟩ :=
    envelopeReal_hasBoundedMetricLaplacian_of_kahlerClass w (atlasClosedFormToNative θ) hρ hK hf
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC.hasBoundedMetricLaplacianOn w _⟩

/-- **The "in particular" of source `thm:DNT23_C11bar` for Kähler classes**: `V_θ`
(`sourceMinimalEnvelope`, `eq:Vtheta`) is real-valued and lies in `C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_kahlerClass [CompactSpace Y]
    [ConnectedSpace Y] (w : KahlerBackground N Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y)) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (atlasClosedFormToNative θ + ddcClosedForm ρ hρ).val.IsKahler) :
    (∀ x, sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  set θn := atlasClosedFormToNative θ with hθn
  obtain ⟨hreal, hC⟩ := envelopeReal_hasBoundedMetricLaplacian_of_kahlerClass w θn hρ hK
    (f := fun _ => 0) (hasBoundedMetricLaplacian_of_chartSmooth w (fun _ => contDiffOn_const))
  -- `ρ` is `θ`-psh, so `PSH(X,θ) ≠ ∅` and `V_θ = P_θ(0)`
  have hρpsh : IsThetaPshPotential θn.val (fun y => (ρ y : EReal)) := by
    have h := thetaPshPotential_sub_smooth (θ := (θn + ddcClosedForm ρ hρ).val) (η := θn.val)
      (f := fun y => -ρ y) (fun e => (hρ e).neg) (fun e z hz => ?_)
      (u := fun _ => (0 : EReal)) ?_
    · have hfun : (fun y => (0 : EReal) - ((-ρ y : ℝ) : EReal)) =
          fun y => (ρ y : EReal) := by
        funext y
        rw [← EReal.coe_zero, ← EReal.coe_sub, zero_sub, neg_neg]
      rw [hfun] at h
      exact h
    · rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
        smoothDDC_neg (h := fun y => ρ (e.val.symm y)) e.val.open_target (hρ e) hz,
        add_neg_cancel_right]
    · exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (KahlerBackground.isSemipositive ⟨θn + ddcClosedForm ρ hρ, hK⟩)
  have hV : sourceMinimalEnvelope θ = rooftopEnvelope θn.val (fun _ => ((0 : ℝ) : EReal)) := by
    rw [sourceMinimalEnvelope_eq_native]
    exact thetaPshSupremum_eq_rooftopEnvelope_zero w θn hρpsh
  rw [hV]
  have heq : (fun x => (rooftopEnvelope θn.val (fun _ => ((0 : ℝ) : EReal)) x).toReal) =
      envelopeReal θn (fun _ => 0) := rfl
  rw [heq]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC.hasBoundedMetricLaplacianOn w _⟩

end Source

end SGPT.Envelopes.LapClass
