import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Flatness of a nonnegative function at density points of its zero set

Package WN-REG (`claude-tok-wn-reg`, node `tok-wn-reg:contact-flat`).  This is the real-analysis
input of the contact formula for smooth obstacles (`tok-wn-reg:dnt-local`): it replaces the
`W^{2,1}` theory and Stampacchia's theorem used in the book's `lma:DNTroof`.

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, `G ≥ 0` a
measurable function, `S` a measurable set, and suppose that `G` has quadratic ball averages at
the points of `S`: `∫_{B̄(y, s)} G ≤ C s² μ(B̄(y, s))` for `y ∈ S` near `z` and small `s`
(for `G = q - V` with `q` smooth and `V ≤ q` plurisubharmonic this is the sub-mean value
property of `V + C|· - y|² - q`).  If `z ∈ S` is a density point of `S`, then
`∫_{B̄(z, r)} G = o(r² μ(B̄(z, r)))`.

* `setLIntegral_mul_measure_closedBall_le` — Tonelli: `∫_{B̄(z,r)} G · μ(B̄(0,s)) ≤
  ∫_{y ∈ B̄(z, r+s)} ∫_{B̄(y,s)} G`.
* `eventually_setLIntegral_le_of_density` — the flatness statement.
* `ae_eventually_measure_closedBall_diff_le` — Lebesgue's density theorem in the form used
  above (Mathlib, `Besicovitch.ae_tendsto_measure_inter_div`).

## Proof of the flatness

Fix `η ∈ (0, 1]` and put `s = ηr`.  By Tonelli, `μ(B̄_s) ∫_{B̄(z,r)} G` is at most the integral over
`y ∈ B̄(z, 2r)` of `∫_{B̄(y,s)} G`.  For `y ∈ S` the inner integral is `≤ C s² μ(B̄_s)`; for `y ∉ S` it is
`≤ ∫_{B̄(z,3r)} G ≤ 9Cr² μ(B̄(z,3r))` (hypothesis at the centre `z ∈ S`), and these `y` have measure
`o(μ(B̄(z,2r)))`.  Dividing by `μ(B̄_s) = η^d μ(B̄(z,r))`,
`∫_{B̄(z,r)} G ≤ (C η² 2^d + o(1) η^{-d}) r² μ(B̄(z, r))`, and `η` is arbitrary.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Okounkov.TranscendentalWNReg.DensityPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Tonelli for ball averages.**  `∫_{B̄(z,r)} G · μ(B̄(0,s)) ≤ ∫_{y ∈ B̄(z,r+s)} ∫_{B̄(y,s)} G`. -/
theorem setLIntegral_mul_measure_closedBall_le {G : E → ℝ≥0∞} (hG : Measurable G) (z : E)
    (r s : ℝ) :
    (∫⁻ x in closedBall z r, G x ∂μ) * μ (closedBall (0 : E) s) ≤
      ∫⁻ y in closedBall z (r + s), ∫⁻ x in closedBall y s, G x ∂μ ∂μ := by
  set A : Set E := closedBall z (r + s) with hA
  set D : Set (E × E) := {p | dist p.2 p.1 ≤ s} with hD
  have hDm : MeasurableSet D :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  let f : E → E → ℝ≥0∞ := fun y x => A.indicator 1 y * (D.indicator 1 (y, x) * G x)
  have hf : Measurable (Function.uncurry f) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ (hG.comp measurable_snd))
    · exact (measurable_one.indicator measurableSet_closedBall).comp measurable_fst
    · exact measurable_one.indicator hDm
  have hind : ∀ y : E, A.indicator (1 : E → ℝ≥0∞) y ≠ ⊤ := by
    intro y
    by_cases hy : y ∈ A <;> simp [hy]
  have hinner : ∀ y : E, ∫⁻ x in closedBall y s, G x ∂μ = ∫⁻ x, D.indicator 1 (y, x) * G x ∂μ := by
    intro y
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ closedBall y s
    · have hxD : (y, x) ∈ D := by
        simpa only [hD, mem_ofPred_eq, mem_closedBall] using hx
      simp [hx, hxD]
    · have hxD : (y, x) ∉ D := by
        simpa only [hD, mem_ofPred_eq, mem_closedBall] using hx
      simp [hx, hxD]
  have hR : ∫⁻ y in A, ∫⁻ x in closedBall y s, G x ∂μ ∂μ = ∫⁻ y, ∫⁻ x, f y x ∂μ ∂μ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun y => ?_
    simp only [f]
    rw [lintegral_const_mul' _ _ (hind y), ← hinner y]
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := μ) hf.aemeasurable
  have hball : ∀ x : E, μ (closedBall (0 : E) s) = ∫⁻ y, D.indicator 1 (y, x) ∂μ := by
    intro x
    rw [← Measure.addHaar_closedBall_center μ x s, ← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_congr fun y => ?_
    by_cases hy : dist y x ≤ s
    · have hyD : (y, x) ∈ D := by simpa only [hD, mem_ofPred_eq, dist_comm] using hy
      have hy' : y ∈ closedBall x s := hy
      simp [hy', hyD]
    · have hyD : (y, x) ∉ D := by simpa only [hD, mem_ofPred_eq, dist_comm] using hy
      have hy' : y ∉ closedBall x s := hy
      simp [hy', hyD]
  calc (∫⁻ x in closedBall z r, G x ∂μ) * μ (closedBall (0 : E) s)
      = ∫⁻ x in closedBall z r, G x * μ (closedBall (0 : E) s) ∂μ :=
        (lintegral_mul_const _ hG).symm
    _ = ∫⁻ x in closedBall z r, ∫⁻ y, G x * D.indicator 1 (y, x) ∂μ ∂μ := by
        refine lintegral_congr fun x => ?_
        have hm : Measurable fun y : E => D.indicator (1 : E × E → ℝ≥0∞) (y, x) :=
          (measurable_one.indicator hDm).comp (measurable_id.prodMk measurable_const)
        rw [lintegral_const_mul _ hm, hball x]
    _ ≤ ∫⁻ x in closedBall z r, ∫⁻ y, f y x ∂μ ∂μ := by
        refine setLIntegral_mono' measurableSet_closedBall fun x hx => lintegral_mono fun y => ?_
        by_cases hyD : (y, x) ∈ D
        · have hyA : y ∈ A := by
            have h1 : dist x y ≤ s := hyD
            have h2 : dist x z ≤ r := hx
            rw [hA, mem_closedBall]
            linarith [dist_triangle y x z, dist_comm x y]
          simp [f, hyD, hyA, mul_comm]
        · simp [f, hyD]
    _ ≤ ∫⁻ x, ∫⁻ y, f y x ∂μ ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ∫⁻ x, f y x ∂μ ∂μ := hswap.symm
    _ = _ := hR.symm

/-- **Lebesgue's density theorem**, in the form used below: at almost every point `z` of a
measurable set `S`, `μ(B̄(z, r) \ S) ≤ τ μ(B̄(z, r))` for every `τ > 0` and all small `r > 0`. -/
theorem ae_eventually_measure_closedBall_diff_le {S : Set E} (hS : MeasurableSet S) :
    ∀ᵐ z ∂μ.restrict S, ∀ τ : ℝ, 0 < τ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall z r \ S) ≤ ENNReal.ofReal τ * μ (closedBall z r) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ S] with z hz
  intro τ hτ
  rcases lt_or_ge τ 1 with hτ1 | hτ1
  · have hlt : ENNReal.ofReal (1 - τ) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith)
    filter_upwards [hz.eventually (lt_mem_nhds hlt), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hBpos : μ (closedBall z r) ≠ 0 := (measure_closedBall_pos μ z hr0').ne'
    have hBfin : μ (closedBall z r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hBpos) (Or.inl hBfin), inter_comm] at hr
    have hsplit := measure_sdiff_add_inter (μ := μ) (closedBall z r) hS
    have hfin1 : μ (closedBall z r \ S) ≠ ⊤ :=
      ((measure_mono sdiff_subset).trans_lt measure_closedBall_lt_top).ne
    have hfin2 : μ (closedBall z r ∩ S) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt measure_closedBall_lt_top).ne
    have hr' := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin)
      hfin2).mpr hr
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hr'
    have hsplit' := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hfin1 hfin2] at hsplit'
    rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hBfin, ← ENNReal.ofReal_mul hτ.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · refine Eventually.of_forall fun r => ?_
    calc μ (closedBall z r \ S) ≤ μ (closedBall z r) := measure_mono sdiff_subset
      _ = 1 * μ (closedBall z r) := (one_mul _).symm
      _ ≤ ENNReal.ofReal τ * μ (closedBall z r) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hτ1

/-- **Flatness at density points.**  Let `G ≥ 0` be measurable, `S` measurable, `z ∈ S`, and suppose
`∫_{B̄(y,s)} G ≤ C s² μ(B̄(y, s))` for `y ∈ S` with `dist y z + s < s₀`.  If `z` is a density point of
`S`, then for every `ε > 0`, `∫_{B̄(z,r)} G ≤ ε r² μ(B̄(z, r))` for all small `r > 0`. -/
theorem eventually_setLIntegral_le_of_density {G : E → ℝ≥0∞} (hG : Measurable G)
    {S : Set E} (hS : MeasurableSet S) {z : E} (hz : z ∈ S) {C s₀ : ℝ} (hC : 0 ≤ C)
    (hs₀ : 0 < s₀)
    (hsub : ∀ y ∈ S, ∀ s : ℝ, 0 < s → dist y z + s < s₀ →
      ∫⁻ x in closedBall y s, G x ∂μ ≤ ENNReal.ofReal (C * s ^ 2) * μ (closedBall y s))
    (hdens : ∀ τ : ℝ, 0 < τ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall z r \ S) ≤ ENNReal.ofReal τ * μ (closedBall z r)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, G x ∂μ ≤ ENNReal.ofReal (ε * r ^ 2) * μ (closedBall z r) := by
  intro ε hε
  set d := Module.finrank ℝ E with hd
  set c := μ (ball (0 : E) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  set η : ℝ := min 1 (ε / (2 * (C * 2 ^ d + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηC : C * η ^ 2 * 2 ^ d ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * (C * 2 ^ d + 1)) := min_le_right _ _
    have h2 : η ^ 2 ≤ η := by nlinarith
    have hK : 0 ≤ C * 2 ^ d := by positivity
    have h3 : (C * 2 ^ d) * η ≤ (C * 2 ^ d) * (ε / (2 * (C * 2 ^ d + 1))) :=
      mul_le_mul_of_nonneg_left h1 hK
    have h4 : (C * 2 ^ d) * (ε / (2 * (C * 2 ^ d + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc C * η ^ 2 * 2 ^ d = (C * 2 ^ d) * η ^ 2 := by ring
      _ ≤ (C * 2 ^ d) * η := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ ε / 2 := h3.trans h4
  set τ : ℝ := ε * η ^ d / (2 * (9 * C * 3 ^ d * 2 ^ d + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτC : τ * 2 ^ d * (9 * C * 3 ^ d) ≤ ε * η ^ d / 2 := by
    have hK : 0 ≤ 9 * C * 3 ^ d * 2 ^ d := by positivity
    have hE : 0 ≤ ε * η ^ d := by positivity
    rw [hτ, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mem_Ioi.mpr (mul_pos two_pos hr)
  filter_upwards [h2.eventually (hdens τ hτ0), Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < s₀ / 3)]
    with r hdr hr
  obtain ⟨hr0, hr3⟩ := hr
  set s : ℝ := η * r with hs
  have hs0 : 0 < s := mul_pos hη0 hr0
  have hsr : s ≤ r := by nlinarith
  have key := setLIntegral_mul_measure_closedBall_le μ hG z r s
  rw [← lintegral_inter_add_sdiff _ (closedBall z (r + s)) hS] at key
  have hA1 : ∫⁻ y in closedBall z (r + s) ∩ S, ∫⁻ x in closedBall y s, G x ∂μ ∂μ ≤
      ENNReal.ofReal (C * s ^ 2) * μ (closedBall (0 : E) s) * μ (closedBall z (2 * r)) := by
    calc _ ≤ ∫⁻ y in closedBall z (r + s) ∩ S,
          ENNReal.ofReal (C * s ^ 2) * μ (closedBall (0 : E) s) ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.inter hS) fun y hy => ?_
          have hyz : dist y z ≤ r + s := hy.1
          rw [← Measure.addHaar_closedBall_center μ y s]
          exact hsub y hy.2 s hs0 (by linarith)
      _ = ENNReal.ofReal (C * s ^ 2) * μ (closedBall (0 : E) s) *
          μ (closedBall z (r + s) ∩ S) := by rw [setLIntegral_const]
      _ ≤ _ := by
          gcongr
          exact inter_subset_left.trans (closedBall_subset_closedBall (by linarith))
  have hz3 : ∫⁻ x in closedBall z (3 * r), G x ∂μ ≤
      ENNReal.ofReal (C * (3 * r) ^ 2) * μ (closedBall z (3 * r)) :=
    hsub z hz (3 * r) (by positivity) (by rw [dist_self]; linarith)
  have hA2 : ∫⁻ y in closedBall z (r + s) \ S, ∫⁻ x in closedBall y s, G x ∂μ ∂μ ≤
      μ (closedBall z (2 * r) \ S) *
        (ENNReal.ofReal (C * (3 * r) ^ 2) * μ (closedBall z (3 * r))) := by
    calc _ ≤ ∫⁻ y in closedBall z (r + s) \ S, ∫⁻ x in closedBall z (3 * r), G x ∂μ ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.diff hS) fun y hy => ?_
          refine lintegral_mono_set (closedBall_subset_closedBall' ?_)
          have : dist y z ≤ r + s := hy.1
          linarith
      _ = μ (closedBall z (r + s) \ S) * ∫⁻ x in closedBall z (3 * r), G x ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ _ := by
          gcongr
          linarith
  have hvol : ∀ (x : E) (t : ℝ), 0 ≤ t → μ (closedBall x t) = ENNReal.ofReal (t ^ d) * c :=
    fun x t ht => Measure.addHaar_closedBall μ x ht
  have hX0 : ENNReal.ofReal (s ^ d) * c ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hc0
  have hXtop : ENNReal.ofReal (s ^ d) * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  set P : ℝ := r ^ 2 * r ^ d * r ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set a₁ : ℝ := C * s ^ 2 * s ^ d * (2 * r) ^ d with ha₁
  set a₂ : ℝ := τ * (2 * r) ^ d * (C * (3 * r) ^ 2) * (3 * r) ^ d with ha₂
  set a₃ : ℝ := ε * r ^ 2 * r ^ d * s ^ d with ha₃
  have hreal : a₁ + a₂ ≤ a₃ := by
    have e1 : a₁ = (C * η ^ 2 * 2 ^ d) * η ^ d * P := by rw [ha₁, hs, hP]; ring
    have e2 : a₂ = (τ * 2 ^ d * (9 * C * 3 ^ d)) * P := by rw [ha₂, hP]; ring
    have e3 : a₃ = (ε * η ^ d) * P := by rw [ha₃, hs, hP]; ring
    rw [e1, e2, e3]
    have hηd : 0 ≤ η ^ d := by positivity
    have i1 : (C * η ^ 2 * 2 ^ d) * η ^ d * P ≤ (ε / 2) * η ^ d * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hηC hηd) hP0
    have i2 : (τ * 2 ^ d * (9 * C * 3 ^ d)) * P ≤ (ε * η ^ d / 2) * P :=
      mul_le_mul_of_nonneg_right hτC hP0
    nlinarith
  have hE1 : ENNReal.ofReal (C * s ^ 2) * (ENNReal.ofReal (s ^ d) * c) *
      (ENNReal.ofReal ((2 * r) ^ d) * c) = ENNReal.ofReal a₁ * (c * c) := by
    rw [ha₁, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C * s ^ 2 * s ^ d),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C * s ^ 2)]
    ring
  have hE2 : ENNReal.ofReal τ * (ENNReal.ofReal ((2 * r) ^ d) * c) *
      (ENNReal.ofReal (C * (3 * r) ^ 2) * (ENNReal.ofReal ((3 * r) ^ d) * c)) =
      ENNReal.ofReal a₂ * (c * c) := by
    rw [ha₂, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ τ * (2 * r) ^ d * (C * (3 * r) ^ 2)),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ τ * (2 * r) ^ d),
      ENNReal.ofReal_mul hτ0.le]
    ring
  have hE3 : ENNReal.ofReal (ε * r ^ 2) * (ENNReal.ofReal (r ^ d) * c) *
      (ENNReal.ofReal (s ^ d) * c) = ENNReal.ofReal a₃ * (c * c) := by
    rw [ha₃, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε * r ^ 2 * r ^ d),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε * r ^ 2)]
    ring
  rw [hvol z r hr0.le]
  refine (ENNReal.mul_le_mul_iff_left hX0 hXtop).mp ?_
  rw [hvol 0 s hs0.le] at key hA1
  rw [hvol z (2 * r) (by positivity)] at hA1 hdr
  rw [hvol z (3 * r) (by positivity)] at hA2
  calc (∫⁻ x in closedBall z r, G x ∂μ) * (ENNReal.ofReal (s ^ d) * c)
      ≤ _ := key
    _ ≤ ENNReal.ofReal (C * s ^ 2) * (ENNReal.ofReal (s ^ d) * c) *
          (ENNReal.ofReal ((2 * r) ^ d) * c) +
        ENNReal.ofReal τ * (ENNReal.ofReal ((2 * r) ^ d) * c) *
          (ENNReal.ofReal (C * (3 * r) ^ 2) * (ENNReal.ofReal ((3 * r) ^ d) * c)) := by
        gcongr
        exact hA2.trans (by gcongr)
    _ = ENNReal.ofReal (a₁ + a₂) * (c * c) := by
        rw [hE1, hE2, ← add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal a₃ * (c * c) := by gcongr
    _ = _ := hE3.symm

end SGPT.Okounkov.TranscendentalWNReg.DensityPoint
