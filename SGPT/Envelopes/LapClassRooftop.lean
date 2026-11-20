import SGPT.Envelopes.LapClassTrace
import SGPT.Envelopes.LapClassSmoothing
import SGPT.Okounkov.TranscendentalWNRegEnvelope
import SGPT.Okounkov.TranscendentalWNRegSingular
import SGPT.Envelopes.DNTRegRooftop

/-!
# Envelopes of minima of obstacles with bounded metric Laplacian (`prop:DR16_C11bar`)

Lane LAP-CLASS (`claude-lap-class`, nodes `lap-class:soft-min`, `lap-class:smooth-envelope`,
`lap-class:dr16`).  Source: SGPT `prop:DR16_C11bar` (`author/chapter_npp.tex`), Darvas–Rubinstein
Theorem 2.5, with the proof of FPT `thm:kahler-metric-laplacian-rooftop`: for a Kähler form `ω`
and `f₁, f₂ ∈ C^{1,1̄}(X)` (bounded `ω`-Laplacian, `HasBoundedMetricLaplacian`), the envelope
`P_ω(min{f₁, f₂})` is real-valued and has bounded `ω`-Laplacian.

* `laplacian_smoothMin_le` (FPT `lem:soft-minimum-trace`): the smoothed minimum
  `min_ε(f₁, f₂)` of NPP-DNT keeps a common upper bound of the Laplacians.
* `envelope_laplacian_of_chartSmooth` (FPT `prop:penalized-envelope-uniform-limit`, Laplacian bound):
  for a smooth obstacle `F` with `Δ_ω F ≤ S` and `|F| ≤ B`, `P_ω(F)` is real-valued, continuous and
  `-N ≤ Δ_ω P_ω(F) ≤ 2(N + S) e^{a(2B + 1)} - N` in the sense of distributions; the β-solutions
  converge uniformly to `P_ω(F)` (WN-REG) and satisfy the trace estimate
  (`betaSolution_trace_le`).
* `envelope_min_hasBoundedMetricLaplacian` (**`prop:DR16_C11bar`** in the book's class): only upper
  bounds `Δ_ω fᵢ ≤ Sᵢ` are needed.  The obstacles are smoothed with one-sided bounds
  (`exists_smooth_laplacian_le`), combined by the smoothed minimum, and the uniform Laplacian
  bounds of the envelopes pass to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### The smoothed minimum -/

/-- **The smoothed minimum keeps a common upper bound of the Laplacian** (FPT
`lem:soft-minimum-trace`, for the smoothed minimum `min_ε` of NPP-DNT): if `Δ_ω fᵢ ≤ S` then
`Δ_ω min_ε(f₁, f₂) ≤ S`.  In every direction `v`, `(min_ε)_{vv̄} ≤ (1 - t)(f₂)_{vv̄} + t (f₁)_{vv̄}`
with the same `t ∈ [0, 1]`, and the Laplacian is a positive combination of such second
derivatives. -/
theorem laplacian_smoothMin_le {ε : ℝ} (hε : 0 < ε) (w : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : ChartSmooth (n := N) f₁) (h₂ : ChartSmooth (n := N) f₂) {S : ℝ}
    (hS₁ : ∀ y, laplacian w.form.val f₁ y ≤ S) (hS₂ : ∀ y, laplacian w.form.val f₂ y ≤ S)
    (y : Y) : laplacian w.form.val (smoothMin ε f₁ f₂) y ≤ S := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  set z := e.val y
  set F₁ : ComplexModel N → ℝ := fun w => f₁ (e.val.symm w) with hF₁def
  set F₂ : ComplexModel N → ℝ := fun w => f₂ (e.val.symm w) with hF₂def
  have hF₁ : ContDiffAt ℝ 2 F₁ z := contDiffAt_two_chart h₁ e hz
  have hF₂ : ContDiffAt ℝ 2 F₂ z := contDiffAt_two_chart h₂ e hz
  set g : ComplexModel N → ℝ := fun w => (F₂ w - F₁ w) / ε with hgdef
  have hg : ContDiffAt ℝ 2 g z := (hF₂.sub hF₁).div_const ε
  have hp : ContDiffAt ℝ 2 SmoothMax.posPart (g z) :=
    (SmoothMax.contDiff_posPart.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hpg : ContDiffAt ℝ 2 (fun w => SmoothMax.posPart (g w)) z := hp.comp (f := g) z hg
  set t := SmoothMax.trans (g z) with ht
  have ht0 : 0 ≤ t := SmoothMax.trans_nonneg _
  have ht1 : t ≤ 1 := SmoothMax.trans_le_one _
  -- the second derivatives in a direction
  have hdir : ∀ v, leviForm (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) z v ≤
      (1 - t) * leviForm F₂ z v + t * leviForm F₁ z v := by
    intro v
    have hchain := StokesCutoff.mul_leviForm_le_leviForm_comp hp hg
      (deriv_deriv_smoothPosPart_nonneg _) v
    rw [SmoothMax.deriv_posPart] at hchain
    have hlg : leviForm g z v = (leviForm F₂ z v - leviForm F₁ z v) / ε := by
      have hfun : g = ε⁻¹ • fun w => F₂ w - F₁ w := by
        funext w
        simp only [hgdef, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, leviForm_smul (hF₂.sub hF₁), leviForm_sub' hF₂ hF₁]
      ring
    have hlm : leviForm (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) z v =
        leviForm F₂ z v - ε * leviForm (fun w => SmoothMax.posPart (g w)) z v := by
      have hfun : (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) =
          F₂ + (-ε) • fun w => SmoothMax.posPart (g w) := by
        funext w
        simp only [smoothMin, hF₁def, hF₂def, hgdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, leviForm_add (v := (-ε) • fun w => SmoothMax.posPart (g w)) hF₂
        (hpg.const_smul (-ε)), leviForm_smul hpg]
      ring
    rw [hlm]
    rw [hlg] at hchain
    have hεchain : t * (leviForm F₂ z v - leviForm F₁ z v) ≤
        ε * leviForm (fun w => SmoothMax.posPart (g w)) z v := by
      have h := mul_le_mul_of_nonneg_left hchain hε.le
      have heq : ε * (t * ((leviForm F₂ z v - leviForm F₁ z v) / ε)) =
          t * (leviForm F₂ z v - leviForm F₁ z v) := by
        field_simp
      linarith
    linarith
  -- the trace
  have hsm : ContDiffAt ℝ 2 (fun w => smoothMin ε f₁ f₂ (e.val.symm w)) z :=
    contDiffAt_two_chart (chartSmooth_smoothMin ε h₁ h₂) e hz
  obtain ⟨m, v, hv, -⟩ := exists_trace_eq_sum_leviForm
    (posDef_coeff w.isKahler.1 hz).inv.posSemidef
  have e0 := laplacian_eq_trace w.form.val (smoothMin ε f₁ f₂) y
  have e1 := laplacian_eq_trace w.form.val f₁ y
  have e2 := laplacian_eq_trace w.form.val f₂ y
  rw [hv _ _ hsm] at e0
  rw [hv _ _ hF₁] at e1
  rw [hv _ _ hF₂] at e2
  have hsum : laplacian w.form.val (smoothMin ε f₁ f₂) y ≤
      (1 - t) * laplacian w.form.val f₂ y + t * laplacian w.form.val f₁ y := by
    rw [e0, e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hdir (v i)
  have := hS₁ y
  have := hS₂ y
  nlinarith

/-- `tr_ω(ω + ddᶜu) = N + Δ_ω u ≥ 0` for a β-solution. -/
theorem add_laplacian_nonneg (A : KahlerBackground N Y) {β : ℝ} {F : Y → ℝ}
    (U : BetaSolution A β F) (y : Y) : 0 ≤ (N : ℝ) + laplacian A.form.val U.u y := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [laplacian, chartLaplacian, Matrix.trace]
  · exact (add_laplacian_pos hN A U.smooth U.isKahler y).le

/-! ### Envelopes of smooth obstacles -/

variable [MeasurableSpace Y] [BorelSpace Y]

/-- **The Laplacian of the envelope of a smooth obstacle** (FPT
`prop:penalized-envelope-uniform-limit`, Laplacian bound, for the background `ω`).  There is
`a ≥ 0` depending only on `(Y, ω)` such that for every chart-smooth `F` with `Δ_ω F ≤ S` and
`|F| ≤ B`, the envelope `P_ω(F)` is real-valued and continuous, and
`-N ≤ Δ_ω P_ω(F) ≤ 2(N + S) e^{a(2B + 1)} - N` in the sense of distributions. -/
theorem envelope_laplacian_of_chartSmooth [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ (F : Y → ℝ), ChartSmooth (n := N) F → ∀ S B : ℝ,
      (∀ y, laplacian A.form.val F y ≤ S) → (∀ y, |F y| ≤ B) →
      (∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
        ((envelopeReal A.form F x : ℝ) : EReal)) ∧
      Continuous (envelopeReal A.form F) ∧
      LaplacianLE A (envelopeReal A.form F) (2 * (N + S) * Real.exp (a * (2 * B + 1)) - N) ∧
      LaplacianGE A (envelopeReal A.form F) (-N) := by
  obtain ⟨a, β₀, ha0, hβ₀, htr⟩ := betaSolution_trace_le A
  refine ⟨a, ha0, fun F hF S B hFS hB => ?_⟩
  -- a complex-Hessian bound of `F` (any, only used for the convergence)
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
  -- the envelope is real and within `ε_j` of `u_j`
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
  · -- the upper bound
    refine laplacianLE_of_tendstoUniformly A hcont hconv ?_
    have hev : ∀ᶠ j in atTop, N * Real.log (1 + S') / β j ≤ 1 := by
      have h := tendsto_const_div_natCast_add (N * Real.log (1 + S')) c₀
      filter_upwards [h.eventually (ge_mem_nhds one_pos)] with j hj
      simpa [hβdef] using hj
    filter_upwards [hev] with j hj
    refine laplacianLE_of_chartSmooth A (U j).smooth fun y => ?_
    have hm : ∀ x, -B ≤ (U j).u x := fun x =>
      le_betaSolution_of_le (hβpos j) (fun x => (abs_le.mp (hB x)).1) (U j) x
    have h := htr (β j) (hββ₀ j) F hF S hFS (U j) (-B) hm y
    have hup := betaSolution_le_add (hβpos j) hF hS'0 hFS' (U j) y
    have hFy := (abs_le.mp (hB y)).2
    have hexp : Real.exp (a * ((U j).u y - -B)) ≤ Real.exp (a * (2 * B + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ha0)
    have hpos := add_laplacian_nonneg A (U j) y
    have hNS : 0 ≤ 2 * (N + S) := by
      by_contra hneg
      push Not at hneg
      have : 2 * (N + S) * Real.exp (a * ((U j).u y - -B)) < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hexp hNS]
  · -- the lower bound
    refine laplacianGE_of_tendstoUniformly A hcont hconv (Eventually.of_forall fun j => ?_)
    refine laplacianGE_of_chartSmooth A (U j).smooth fun y => ?_
    have := add_laplacian_nonneg A (U j) y
    linarith

/-! ### `prop:DR16_C11bar` -/

/-- **Source `prop:DR16_C11bar` (Darvas–Rubinstein) for obstacles with bounded metric Laplacian;
one-sided form.**  On a compact connected complex manifold with a Kähler form `ω`, if `f₁, f₂` are
continuous with `Δ_ω fᵢ ≤ Sᵢ` in the sense of distributions, then `P_ω(min{f₁, f₂})` is real-valued
and has bounded metric Laplacian. -/
theorem envelope_min_hasBoundedMetricLaplacian_of_le [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    {S₁ S₂ : ℝ} (hS₁ : LaplacianLE A f₁ S₁) (hS₂ : LaplacianLE A f₂ S₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian A (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  classical
  obtain ⟨a, ha0, hEnv⟩ := envelope_laplacian_of_chartSmooth A
  set S := max S₁ S₂ + 2 with hSdef
  -- bounds of the obstacles
  obtain ⟨B₁, hB₁⟩ := isCompact_univ.exists_bound_of_continuousOn h₁.continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_univ.exists_bound_of_continuousOn h₂.continuousOn
  set B := max B₁ B₂ + 5 with hBdef
  -- the smooth approximations
  set η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hηdef
  have hη : ∀ k, 0 < η k := fun k => by positivity
  have hη1 : ∀ k, η k ≤ 1 := fun k => by
    simp only [hηdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  choose g₁ hg₁ hg₁f hg₁L using fun k => exists_smooth_laplacian_le A h₁ hS₁ (hη k)
  choose g₂ hg₂ hg₂f hg₂L using fun k => exists_smooth_laplacian_le A h₂ hS₂ (hη k)
  set F : ℕ → Y → ℝ := fun k => smoothMin (η k) (g₁ k) (g₂ k) with hFdef
  have hF : ∀ k, ChartSmooth (n := N) (F k) := fun k => chartSmooth_smoothMin (η k) (hg₁ k) (hg₂ k)
  have hFL : ∀ k y, laplacian A.form.val (F k) y ≤ S := fun k y =>
    laplacian_smoothMin_le (hη k) A (hg₁ k) (hg₂ k)
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
  -- the envelopes converge uniformly
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
    max (2 * (N + S) * Real.exp (a * (2 * B + 1)) - N) N, ?_, ?_⟩
  · refine laplacianLE_of_tendstoUniformly A hcont hconv (Eventually.of_forall fun k => ?_)
    intro χ hχ hχ0
    refine ((hE k).2.2.1 χ hχ hχ0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg hχ0))
  · refine laplacianGE_of_tendstoUniformly A hcont hconv (Eventually.of_forall fun k => ?_)
    intro χ hχ hχ0
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg hχ0)) ((hE k).2.2.2 χ hχ hχ0)
    have := le_max_right (2 * (N + S) * Real.exp (a * (2 * B + 1)) - N) (N : ℝ)
    linarith

/-- **Source `prop:DR16_C11bar` (Darvas–Rubinstein) in the book's class.**  On a compact
connected complex manifold `X` with a Kähler form `ω`, for `f₁, f₂ ∈ C^{1,1̄}(X)` (bounded
`ω`-Laplacian, `HasBoundedMetricLaplacian`) the envelope `P_ω(min{f₁, f₂})` (the source envelope
of `def:Pthetaf` by `sourceObstacleEnvelope_eq_native`) is real-valued and lies in
`C^{1,1̄}(X)`. -/
theorem envelope_min_hasBoundedMetricLaplacian [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (h₁ : HasBoundedMetricLaplacian A f₁)
    (h₂ : HasBoundedMetricLaplacian A f₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacian A (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  obtain ⟨hc₁, M₁, hM₁, -⟩ := h₁
  obtain ⟨hc₂, M₂, hM₂, -⟩ := h₂
  exact envelope_min_hasBoundedMetricLaplacian_of_le A hc₁ hc₂ hM₁ hM₂

end SGPT.Envelopes.LapClass
