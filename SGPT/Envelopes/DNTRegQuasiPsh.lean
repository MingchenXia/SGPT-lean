import SGPT.Envelopes.DNTRegKahlerClass
import SGPT.Envelopes.DNTC11Measure
import SGPT.Envelopes.DNTC11Density
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier

/-!
# Envelopes of quasi-psh `C^{1,1̄}` obstacles

This file extends `DNTRegRooftop` (source `prop:DR16_C11bar`) and
`DNTRegKahlerClass` (source `thm:DNT23_C11bar`) from smooth obstacles to continuous obstacles `f`
whose complex Hessian is bounded **from above**, `ddᶜf ≤ S ω` (i.e. `-f` is `Sω`-psh).  This class
contains the smooth and the `C^{1,1}` functions and the class `HasBoundedComplexHessian` of
`DNTC11` (continuous functions with locally bounded complex Hessian, i.e. `C^{1,1̄}(X) ∩ QPSH(X)`
in Darvas–Rubinstein's terms).

## Smoothing with a one-sided Hessian bound

If `-f` is continuous and `Sω`-psh (`S > 0`), choose smooth `h_k` with `|h_k - f| < 1/(k+1)`
(partition of unity).  The envelope `P_{Sω}(-h_k)` is within `1/(k+1)` of `P_{Sω}(-f) = -f`, and
Berman's estimate (`bermanSmoothEnvelopeStatement`) writes it as a uniform limit of smooth `u_j`
with `Sω + ddᶜu_j` Kähler.  So `g_k = -u_{j(k)}` are smooth, `g_k → f` uniformly and
`ddᶜg_k ≤ Sω` (`exists_tendstoUniformly_chartSmooth_ddc_le`).  No regularization theorem for
quasi-psh functions is needed beyond Berman's estimate.

## Main results

* `envelope_min_hasSmoothLineBoundApproximation_of_tendsto`: the Darvas–Rubinstein argument of
  `DNTRegRooftop` for obstacles that are uniform limits of smooth functions with a common upper
  bound of `ddᶜ`.
* `isCOneOneBar_envelopeReal_min_of_neg_psh`,
  `isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian` and `sourceObstacleEnvelope_min_isCOneOneBar_of_hasBoundedComplexHessian`: source
  `prop:DR16_C11bar` for these obstacles.
* `envelopeReal_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian`,
  `sourceObstacleEnvelope_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian`: source
  `thm:DNT23_C11bar` for a Kähler class and an obstacle with bounded complex Hessian.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.DNTReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Smooth uniform approximation -/

/-- A continuous function on a compact manifold is uniformly within `ε` of a chart-smooth one. -/
theorem exists_chartSmooth_abs_sub_lt [CompactSpace Y] {h : Y → ℝ} (hh : Continuous h) {ε : ℝ}
    (hε : 0 < ε) : ∃ g : Y → ℝ, ChartSmooth (n := N) g ∧ ∀ x, |g x - h x| < ε := by
  classical
  let S : Y → TopologicalSpace.Opens Y := fun x =>
    ⟨{y | |h y - h x| < ε / 2}, isOpen_lt (hh.sub continuous_const).abs continuous_const⟩
  have hcover : ∀ x : Y, ∃ y, x ∈ S y := fun x => ⟨x, by
    change |h x - h x| < ε / 2
    simp only [sub_self, abs_zero]
    positivity⟩
  obtain ⟨m, χ, idx, hχ, hn, hsupp, _hc, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := N) S hcover
  let g : Y → ℝ := fun y => ∑ a, h (idx a) * χ a y
  refine ⟨g, ?_, ?_⟩
  · intro e
    change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun z => ∑ a, h (idx a) * χ a (e.val.symm z)) e.val.target
    exact ContDiffOn.sum fun a _ => contDiffOn_const.mul (hχ a e)
  · intro x
    have he : g x - h x = ∑ a, χ a x * (h (idx a) - h x) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
      simp only [g, mul_comm]
    have hterm : ∀ a : Fin m, χ a x * |h (idx a) - h x| ≤ χ a x * (ε / 2) := by
      intro a
      by_cases hz : χ a x = 0
      · simp only [hz, zero_mul, le_refl]
      · have hxS := hsupp a (subset_tsupport (χ a) hz)
        change |h x - h (idx a)| < ε / 2 at hxS
        exact mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hxS.le) (hn a x)
    have hle : |g x - h x| ≤ ε / 2 := by
      calc
        _ = |∑ a, χ a x * (h (idx a) - h x)| := by rw [he]
        _ ≤ ∑ a, |χ a x * (h (idx a) - h x)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a, χ a x * |h (idx a) - h x| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg (hn a x)]
        _ ≤ ∑ a, χ a x * (ε / 2) := Finset.sum_le_sum fun a _ => hterm a
        _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    exact hle.trans_lt (by linarith)

/-- `ddᶜ(-u) = -ddᶜu` on complex lines. -/
theorem ddc_line_neg {u : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (hnu : ChartSmooth (n := N) (fun y => -u y)) (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) (v : ComplexModel N) :
    (ddcClosedForm (fun y => -u y) hnu).val.coeff e z ![v, Complex.I • v] =
      -(ddcClosedForm u hu).val.coeff e z ![v, Complex.I • v] := by
  rw [ddc_line_eq hnu e hz v, ddc_line_eq hu e hz v]
  have hneg : leviForm (fun w => -u (e.val.symm w)) z v =
      -leviForm (fun w => u (e.val.symm w)) z v :=
    leviForm_neg (fun w => u (e.val.symm w)) z v
  rw [hneg, neg_div]

/-- **Smoothing with a one-sided Hessian bound.**  On a compact connected manifold with a Kähler
form `ω`, if `f` is continuous and `-f` is `Sω`-psh (`S > 0`), then `f` is a uniform limit of
chart-smooth `g_k` with `ddᶜg_k ≤ Sω` on every complex line. -/
theorem exists_tendstoUniformly_chartSmooth_ddc_le [CompactSpace Y] [ConnectedSpace Y]
    (w : KahlerBackground N Y) {f : Y → ℝ} (hf : Continuous f) {S : ℝ} (hS : 0 < S)
    (hpsh : IsThetaPshPotential (S • w.form).val (fun x => ((-f x : ℝ) : EReal))) :
    ∃ (g : ℕ → Y → ℝ) (hg : ∀ k, ChartSmooth (n := N) (g k)),
      TendstoUniformly g f atTop ∧
      ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v : ComplexModel N,
        (ddcClosedForm (g k) (hg k)).val.coeff e z ![v, Complex.I • v] ≤
          S * w.form.val.coeff e z ![v, Complex.I • v] := by
  set A : KahlerBackground N Y := KahlerBackground.smul hS w with hAdef
  have hAform : A.form = S • w.form := rfl
  obtain ⟨a, Λ, ha, hΛ, hBer⟩ := bermanSmoothEnvelopeStatement N Y A
  -- the envelope of `-f` is `-f`
  have hself : rooftopEnvelope A.form.val (fun y => ((-f y : ℝ) : EReal)) =
      fun y => ((-f y : ℝ) : EReal) :=
    DominationPrincipleBarrier.rooftopEnvelope_eq_self hpsh
  have hreal_f : ∀ x, rooftopEnvelope A.form.val (fun y => ((-f y : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => -f y) x : ℝ) : EReal) := by
    intro x
    simp only [envelopeReal, hself, EReal.toReal_coe]
  have hpick : ∀ k : ℕ, ∃ u : Y → ℝ, ∃ hu : ChartSmooth (n := N) u,
      (∀ x, |-u x - f x| ≤ 2 / ((k : ℝ) + 1)) ∧ (A.form + ddcClosedForm u hu).val.IsKahler := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨h, hh, hhf⟩ := exists_chartSmooth_abs_sub_lt (N := N) hf hpos
    have hnh : ChartSmooth (n := N) (fun y => -h y) := fun e => (hh e).neg
    obtain ⟨S', hS'0, hS'⟩ := exists_ddc_line_le_of_chartSmooth A hnh
    obtain ⟨B, hB⟩ := YauContinuityMethod.exists_abs_le hnh
    obtain ⟨hreal, uj, huj, hunif, hK, -⟩ :=
      hBer _ hnh S' hS'0 hS' (-B) fun y => (abs_le.mp (hB y)).1
    -- `P_A(-h)` is within `1/(k+1)` of `-f`
    have hsand := envelope_sandwich A.form (F := fun y => -f y) (G := fun y => -h y)
      (c := 1 / ((k : ℝ) + 1)) (fun y => by
        rw [show -f y - -h y = h y - f y by ring]
        exact (hhf y).le) hreal_f
    obtain ⟨j, hj⟩ := ((Metric.tendstoUniformly_iff.mp hunif) _ hpos).exists
    refine ⟨uj j, huj j, fun x => ?_, hK j⟩
    have h1 := hsand.2 x
    have h2 := hj x
    have hfx : envelopeReal A.form (fun y => -f y) x = -f x := by
      simp only [envelopeReal, hself, EReal.toReal_coe]
    rw [hfx] at h1
    rw [Real.dist_eq] at h2
    have h3 : |-uj j x - f x| ≤
        |envelopeReal A.form (fun y => -h y) x - uj j x| +
          |envelopeReal A.form (fun y => -h y) x - -f x| := by
      calc |-uj j x - f x| = |(envelopeReal A.form (fun y => -h y) x - uj j x) -
            (envelopeReal A.form (fun y => -h y) x - -f x)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have h4 : (2 : ℝ) / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    rw [h4]
    linarith
  choose u hu hclose hK using hpick
  have hnu : ∀ k, ChartSmooth (n := N) (fun y => -u k y) := fun k e => (hu k e).neg
  refine ⟨fun k y => -u k y, hnu, ?_, fun k e z hz v => ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (half_pos hδ)
    filter_upwards [eventually_ge_atTop k₀] with k hk x
    rw [Real.dist_eq, abs_sub_comm]
    have h1 := hclose k x
    have h2 := one_div_succ_le_one_div_succ hk
    have h3 : (2 : ℝ) / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
    linarith
  · rw [ddc_line_neg (hu k) (hnu k) e hz v]
    have hsemi := coefficientSemipositive_of_isKahler (hK k) hz v
    rw [add_ddc_line, hAform, ClosedRealOneOneForm.coeff_smul] at hsemi
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hsemi
    linarith

/-! ### `prop:DR16_C11bar` for obstacles with an upper Hessian bound -/

/-- **The Darvas–Rubinstein argument for approximable obstacles.**  If `f₁, f₂` are uniform
limits of chart-smooth functions with a common upper bound `ddᶜ ≤ S ω`, then `P_ω(min{f₁, f₂})` is
real-valued and has a line-bounded smooth approximation with a constant bound. -/
theorem envelope_min_hasSmoothLineBoundApproximation_of_tendsto [CompactSpace Y]
    [ConnectedSpace Y] (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (hf₁ : Continuous f₁)
    (hf₂ : Continuous f₂) {g₁ g₂ : ℕ → Y → ℝ} (hg₁ : ∀ k, ChartSmooth (n := N) (g₁ k))
    (hg₂ : ∀ k, ChartSmooth (n := N) (g₂ k)) (hc₁ : TendstoUniformly g₁ f₁ atTop)
    (hc₂ : TendstoUniformly g₂ f₂ atTop) {S : ℝ} (hS0 : 0 ≤ S)
    (hS₁ : ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm (g₁ k) (hg₁ k)).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    (hS₂ : ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm (g₂ k) (hg₂ k)).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v]) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    ∃ M : ℝ, HasSmoothLineBoundApproximation A
      (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) (fun _ => M) := by
  -- bounds for the obstacles
  obtain ⟨B₁, hB₁⟩ := isCompact_univ.exists_bound_of_continuousOn hf₁.continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_univ.exists_bound_of_continuousOn hf₂.continuousOn
  set B := max B₁ B₂ with hBdef
  have hb₁ : ∀ y, |f₁ y| ≤ B := fun y => by
    have := hB₁ y (mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hb₂ : ∀ y, |f₂ y| ≤ B := fun y => by
    have := hB₂ y (mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_right _ _)
  have hminlo : ∀ y, -B ≤ min (f₁ y) (f₂ y) := fun y =>
    le_min (abs_le.mp (hb₁ y)).1 (abs_le.mp (hb₂ y)).1
  have hminup : ∀ y, min (f₁ y) (f₂ y) ≤ B := fun y =>
    (min_le_left _ _).trans (abs_le.mp (hb₁ y)).2
  -- choose approximation indices
  have hidx : ∀ k : ℕ, ∃ K : ℕ, ∀ y, dist (f₁ y) (g₁ K y) < 1 / ((k : ℝ) + 1) ∧
      dist (f₂ y) (g₂ K y) < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨K, hK⟩ := (((Metric.tendstoUniformly_iff.mp hc₁) _ hpos).and
      ((Metric.tendstoUniformly_iff.mp hc₂) _ hpos)).exists
    exact ⟨K, fun y => ⟨hK.1 y, hK.2 y⟩⟩
  choose K hK using hidx
  -- Berman's estimate
  obtain ⟨a, Λ, ha, hΛ, hBer⟩ := bermanSmoothEnvelopeStatement N Y A
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    simp only [hεdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set F : ℕ → Y → ℝ := fun k => smoothMin (ε k) (g₁ (K k)) (g₂ (K k)) with hFdef
  have hF : ∀ k, ChartSmooth (n := N) (F k) := fun k =>
    chartSmooth_smoothMin (ε k) (hg₁ (K k)) (hg₂ (K k))
  -- `F k` is within `2/(k+1)` of `min{f₁, f₂}`
  have hFclose : ∀ k y, |F k y - min (f₁ y) (f₂ y)| ≤ 2 * ε k := by
    intro k y
    have h1 := abs_smoothMin_sub_le (hε k) (g₁ (K k)) (g₂ (K k)) y
    have h2 : |min (g₁ (K k) y) (g₂ (K k) y) - min (f₁ y) (f₂ y)| ≤ ε k := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
      · have := (hK k y).1
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this.le
      · have := (hK k y).2
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this.le
    calc |F k y - min (f₁ y) (f₂ y)|
        = |(smoothMin (ε k) (g₁ (K k)) (g₂ (K k)) y - min (g₁ (K k) y) (g₂ (K k) y)) +
            (min (g₁ (K k) y) (g₂ (K k) y) - min (f₁ y) (f₂ y))| := by
          simp only [hFdef]
          ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε k + ε k := add_le_add h1 h2
      _ = 2 * ε k := by ring
  have hFlo : ∀ k y, -B - 2 ≤ F k y := fun k y => by
    have := (abs_le.mp (hFclose k y)).1
    linarith [hminlo y, hε1 k]
  have hFup : ∀ k y, F k y ≤ B + 2 := fun k y => by
    have := (abs_le.mp (hFclose k y)).2
    linarith [hminup y, hε1 k]
  have hber := fun k => hBer (F k) (hF k) S hS0
    (smoothMin_ddc_line_le (hε k) A (hg₁ (K k)) (hg₂ (K k)) (hS₁ (K k)) (hS₂ (K k))) (-B - 2)
    (hFlo k)
  have hsand := fun k => envelope_sandwich A.form (F := F k)
    (G := fun y => min (f₁ y) (f₂ y)) (c := 2 * ε k) (hFclose k) (hber k).1
  refine ⟨(hsand 0).1, (1 + S) * Λ * Real.exp (a * (B + 2 + (B + 2))), ?_⟩
  refine hasSmoothLineBoundApproximation_of_tendstoUniformly A
    (w := fun k => envelopeReal A.form (F k)) (fun k => (hber k).2) (fun k x => ?_) ?_
  · have h1S : 0 ≤ (1 + S) * Λ := by
      have : 0 ≤ 1 + S := by linarith
      positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ?_ ha)) h1S
    linarith [hFup k x]
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (half_pos hδ)
    filter_upwards [eventually_ge_atTop k₀] with k hk x
    rw [Real.dist_eq]
    have h1 := (hsand k).2 x
    have h2 := one_div_succ_le_one_div_succ hk
    simp only [hεdef] at h1
    linarith

/-- **Source `prop:DR16_C11bar` for obstacles with an upper Hessian bound.**  If `f₁, f₂` are
continuous and `-f₁` is `S₁ω`-psh, `-f₂` is `S₂ω`-psh (`S₁, S₂ > 0`, i.e. `ddᶜfᵢ ≤ Sᵢω`), then
`P_ω(min{f₁, f₂})` is real-valued and `C^{1,1̄}(X)`. -/
theorem isCOneOneBar_envelopeReal_min_of_neg_psh [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp₁ : IsThetaPshPotential (S₁ • A.form).val (fun x => ((-f₁ x : ℝ) : EReal)))
    (hp₂ : IsThetaPshPotential (S₂ • A.form).val (fun x => ((-f₂ x : ℝ) : EReal))) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  obtain ⟨g₁, hg₁, hc₁, hb₁⟩ := exists_tendstoUniformly_chartSmooth_ddc_le A hf₁ hS₁ hp₁
  obtain ⟨g₂, hg₂, hc₂, hb₂⟩ := exists_tendstoUniformly_chartSmooth_ddc_le A hf₂ hS₂ hp₂
  set S := max S₁ S₂ with hSdef
  have hle : ∀ (S' : ℝ), S' ≤ S → ∀ (e : ComplexChart N Y) (z : ComplexModel N),
      z ∈ e.val.target → ∀ (v : ComplexModel N) (c : ℝ),
        c ≤ S' * A.form.val.coeff e z ![v, Complex.I • v] →
          c ≤ S * A.form.val.coeff e z ![v, Complex.I • v] :=
    fun S' hS' e z hz v c hc =>
      hc.trans (mul_le_mul_of_nonneg_right hS' (A.isSemipositive e z hz v))
  obtain ⟨hreal, M, h⟩ := envelope_min_hasSmoothLineBoundApproximation_of_tendsto A hf₁ hf₂
    hg₁ hg₂ hc₁ hc₂ (le_max_of_le_left hS₁.le)
    (fun k e z hz v => hle S₁ (le_max_left _ _) e z hz v _ (hb₁ k e z hz v))
    (fun k e z hz v => hle S₂ (le_max_right _ _) e z hz v _ (hb₂ k e z hz v))
  exact ⟨hreal, isCOneOneBar_of_hasSmoothLineBoundApproximation A h fun _ => le_rfl⟩

/-- A function with bounded complex Hessian has `-f` quasi-psh. -/
theorem HasBoundedComplexHessian.exists_neg_psh [CompactSpace Y] (A : KahlerBackground N Y)
    {f : Y → ℝ} (hf : HasBoundedComplexHessian (n := N) f) :
    ∃ S : ℝ, 0 < S ∧ IsThetaPshPotential (S • A.form).val (fun x => ((-f x : ℝ) : EReal)) := by
  have hnf : HasBoundedComplexHessian (n := N) (fun x => -f x) := by
    refine ⟨hf.1.neg, fun e => ?_⟩
    obtain ⟨h, hh⟩ := hf.2 e
    refine ⟨_, (hh.smul (-1)).congr_fun ?_⟩
    funext z
    ring
  obtain ⟨T, hT1, hT⟩ := exists_isThetaPshPotential_add_smul A 0 hnf
  refine ⟨T, by linarith, ?_⟩
  have h := hT T le_rfl
  rwa [zero_add] at h

/-- **Source `prop:DR16_C11bar` for obstacles with bounded complex Hessian** (`C^{1,1̄} ∩ QPSH`,
`HasBoundedComplexHessian`): `P_ω(min{f₁, f₂})` is real-valued and `C^{1,1̄}(X)`. -/
theorem isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian [CompactSpace Y]
    [ConnectedSpace Y] (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂) :
    (∀ x, rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      ((envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal A.form (fun y => min (f₁ y) (f₂ y))) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := HasBoundedComplexHessian.exists_neg_psh A h₁
  obtain ⟨S₂, hS₂, hp₂⟩ := HasBoundedComplexHessian.exists_neg_psh A h₂
  exact isCOneOneBar_envelopeReal_min_of_neg_psh A h₁.1 h₂.1 hS₁ hS₂ hp₁ hp₂

/-! ### `thm:DNT23_C11bar` for a Kähler class and an obstacle with bounded complex Hessian -/

/-- **Source `thm:DNT23_C11bar`, Kähler class and obstacle with bounded complex Hessian.**  If
`θ + ddᶜρ` is a Kähler form for a chart-smooth `ρ` and `f` has bounded complex Hessian, then
`P_θ(f)` is real-valued and `C^{1,1̄}` on `X`, in particular on `X \ nK({θ})`. -/
theorem envelopeReal_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian [CompactSpace Y]
    [ConnectedSpace Y] (θ : ClosedRealOneOneForm N Y) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ}
    (hf : HasBoundedComplexHessian (n := N) f) :
    (∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal θ f x : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (envelopeReal θ f) ∧
    IsCOneOneBarOn (N := N)
      (SGPT.PSH.VariableComplexAtlas.sourceNonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (envelopeReal θ f) := by
  set A : KahlerBackground N Y := ⟨θ + ddcClosedForm ρ hρ, hK⟩ with hAdef
  have hfρ : HasBoundedComplexHessian (n := N) (fun y => f y - ρ y) := by
    refine ⟨hf.1.sub (YauUniformEstimate.continuous_of_chartSmooth hρ), fun e => ?_⟩
    obtain ⟨h, hh⟩ := hf.2 e
    refine ⟨_, (hh.add_contDiffOn (hρ e).neg).congr_fun ?_⟩
    funext z
    ring
  obtain ⟨hreal, hC⟩ := isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian A hfρ hfρ
  simp only [min_self] at hreal hC
  have hshift : ∀ x, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      ((envelopeReal A.form (fun y => f y - ρ y) x + ρ x : ℝ) : EReal) := by
    intro x
    rw [rooftopEnvelope_shift θ hρ f x, EReal.coe_add]
    congr 1
    exact hreal x
  have heq : envelopeReal θ f = fun x => envelopeReal A.form (fun y => f y - ρ y) x + ρ x := by
    funext x
    simp only [envelopeReal] at hshift ⊢
    rw [hshift x, EReal.toReal_coe]
  have hC' := IsCOneOneBar.add_chartSmooth hC hρ
  rw [← heq] at hC'
  refine ⟨fun x => ?_, hC', IsCOneOneBar.isCOneOneBarOn hC' _⟩
  rw [hshift x, heq]

section Source

open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- **Source `prop:DR16_C11bar` for obstacles with bounded complex Hessian, with the source
envelope** `P_ω(min{f₁, f₂}) = sourceRelativeEnvelope ω ⊤ min{f₁, f₂}` (`def:Pthetaf`). -/
theorem sourceObstacleEnvelope_min_isCOneOneBar_of_hasBoundedComplexHessian [CompactSpace Y]
    [ConnectedSpace Y] (w : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hK : (atlasClosedFormToNative w).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂) :
    (∀ x, sourceRelativeEnvelope w (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
      (((sourceRelativeEnvelope w (fun _ => ⊤)
        (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBar (N := N) (fun x => (sourceRelativeEnvelope w (fun _ => ⊤)
      (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal) := by
  obtain ⟨hreal, hC⟩ :=
    isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian ⟨atlasClosedFormToNative w, hK⟩ h₁ h₂
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

/-- **Source `thm:DNT23_C11bar`, Kähler class and obstacle with bounded complex Hessian, with the
source envelope** `P_θ(f) = sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`). -/
theorem sourceObstacleEnvelope_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian
    [CompactSpace Y] [ConnectedSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y)) {ρ : Y → ℝ} (hρ : ChartSmooth (n := N) ρ)
    (hK : (atlasClosedFormToNative θ + ddcClosedForm ρ hρ).val.IsKahler) {f : Y → ℝ}
    (hf : HasBoundedComplexHessian (n := N) f) :
    (∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
      (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBarOn (N := N)
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  obtain ⟨hreal, -, hC⟩ := envelopeReal_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian
    (atlasClosedFormToNative θ) hρ hK hf
  rw [sourceObstacleEnvelope_eq_native]
  exact ⟨fun x => by rw [hreal x, EReal.toReal_coe], hC⟩

end Source

end SGPT.Envelopes.DNTReg
