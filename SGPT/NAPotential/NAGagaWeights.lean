import SGPT.NAPotential.NAGagaDisc
import SGPT.GAGA.H0TubeIntegrals

/-!
# The radial weights of the complexification of a test curve

Source: `chapter_NApotential.tex`, `prop:psiandPhi`. Blueprint `claude-na-gaga.tex`, node
`claude-na-gaga:weights`.

Let `Γ` be a test curve with `Γ_max ≤ 0` and `Γ^*_t = sup_{τ < Γ_max} (Γ_τ + tτ)` its Legendre
transform (`sourceTestCurveRawLegendre`). The complexification is `Ψ(y, δ) = Γ^*_{-log|δ|²}(y)`
on `X × Δ^*`. For `k ≥ 1`, `i ∈ ℕ` and `0 < r ≤ 1` put

`D_{k,i}(y, r) = ∫_{|w| < r} |w|^{2i} e^{-kΨ(y, w)} dw`,

the radial weight which governs whether `g(y) δ^i` lies in `𝓘(kΨ)` (`radialWeight`). This file
proves the three pointwise estimates:

* `multiplierWeight_slice_le_radialWeight`: for `τ = -(i+1)/k < Γ_max`,
  `e^{-kΓ_τ(y)} ≤ K · D_{k,i}(y, r)` with a constant `K` independent of `y` (lower bound of
  `D` on an annulus `{ρ/2 < |w| < ρ}` where `Ψ(y, ·) ≤ Ψ(y, ρ)`, and the inverse Legendre formula
  `Γ_τ = inf_{t > 0} (Γ^*_t - tτ)`);
* `radialWeight_eq_top`: if `i + 1 + kΓ_max ≤ 0` then `D_{k,i}(y, r) = ∞` (from `Γ^*_t ≤ tΓ_max`);
* `multiplierWeight_raw_le`: `e^{-kΓ^*_t(y)} ≤ e^{-kΓ_τ(y)} e^{-ktτ}` (from `Γ^*_t ≥ Γ_τ + tτ`),
  the input of the inclusion `𝓘(kΓ_τ) δ^i ⊆ 𝓘(kΨ)` when `i + kτ > -1`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NAGaga

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

/-! ### Weights -/

theorem multiplierWeight_add_real {c : ℝ} (hc : 0 < c) {a : EReal} (ha : a ≠ ⊤) (s : ℝ) :
    multiplierWeight c (a + (s : EReal)) =
      multiplierWeight c a * ENNReal.ofReal (Real.exp (-(c * s))) := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot hc, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe a =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
  | top => exact absurd rfl ha

theorem multiplierWeight_sub_real {c : ℝ} (hc : 0 < c) {a : EReal} (ha : a ≠ ⊤) (s : ℝ) :
    multiplierWeight c (a - (s : EReal)) =
      multiplierWeight c a * ENNReal.ofReal (Real.exp (c * s)) := by
  rw [sub_eq_add_neg, ← EReal.coe_neg, multiplierWeight_add_real hc ha]
  congr 3; ring

theorem measurable_multiplierWeight {c : ℝ} (hc : c ≠ 0) : Measurable (multiplierWeight c) := by
  have h1 : Measurable (fun a : EReal => (c : EReal) * a) :=
    (continuous_eReal_const_mul hc).measurable
  exact EReal.measurable_exp.comp (continuous_neg.measurable.comp h1)

/-- **The infimum estimate.** If `F` is decreasing on `(0, ∞)`, `τ ≤ 0`, `T ≥ 0` and
`e^{-c(F(t) - tτ)} ≤ A` for every `t > T`, then
`e^{-c inf_{t > 0} (F(t) - tτ)} ≤ e^{c(1 + (T+1)(-τ))} A`. -/
theorem multiplierWeight_iInf_le_of_tail {F : ℝ → EReal} {c τ T : ℝ} (hc : 0 < c) (hτ : τ ≤ 0)
    (hT : 0 ≤ T) (hanti : ∀ t t', 0 < t → t ≤ t' → F t' ≤ F t) {A : ℝ≥0∞}
    (hA : ∀ t, T < t → multiplierWeight c (F t - ((t * τ : ℝ) : EReal)) ≤ A) :
    multiplierWeight c (⨅ t : Ioi (0 : ℝ), F t.1 - ((t.1 * τ : ℝ) : EReal)) ≤
      ENNReal.ofReal (Real.exp (c * (1 + (T + 1) * (-τ)))) * A := by
  set C : ℝ := (T + 1) * (-τ) with hCdef
  have hC : 0 ≤ C := mul_nonneg (by linarith) (by linarith)
  -- every value of the infimum below `s` is matched, after the tail, below `s + C`
  have key : ∀ s : ℝ, (⨅ t : Ioi (0 : ℝ), F t.1 - ((t.1 * τ : ℝ) : EReal)) < (s : EReal) →
      ENNReal.ofReal (Real.exp (-(c * (s + C)))) ≤ A := by
    intro s hs
    obtain ⟨t₀, ht₀⟩ := iInf_lt_iff.mp hs
    have ht₀pos : 0 < t₀.1 := t₀.2
    set t₁ : ℝ := max t₀.1 (T + 1) with ht₁
    have hTt₁ : T < t₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have ht₀₁ : t₀.1 ≤ t₁ := le_max_left _ _
    have hdiff : t₁ - t₀.1 ≤ T + 1 := by
      rcases le_total t₀.1 (T + 1) with h | h
      · rw [ht₁, max_eq_right h]; linarith
      · rw [ht₁, max_eq_left h]; linarith
    have hF : F t₁ ≤ F t₀.1 := hanti _ _ ht₀pos ht₀₁
    have hlt : F t₁ - ((t₁ * τ : ℝ) : EReal) < ((s + C : ℝ) : EReal) := by
      have h1 : F t₁ - ((t₁ * τ : ℝ) : EReal) ≤
          F t₀.1 - ((t₀.1 * τ : ℝ) : EReal) + (((t₁ - t₀.1) * (-τ) : ℝ) : EReal) := by
        have he : F t₀.1 - ((t₁ * τ : ℝ) : EReal) =
            F t₀.1 - ((t₀.1 * τ : ℝ) : EReal) + (((t₁ - t₀.1) * (-τ) : ℝ) : EReal) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_neg,
            ← EReal.coe_add]
          congr 2; ring
        rw [← he]
        exact EReal.sub_le_sub hF le_rfl
      have h2 : (((t₁ - t₀.1) * (-τ) : ℝ) : EReal) ≤ (C : EReal) :=
        EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hdiff (by linarith))
      calc F t₁ - ((t₁ * τ : ℝ) : EReal)
          ≤ F t₀.1 - ((t₀.1 * τ : ℝ) : EReal) + (C : EReal) := h1.trans (add_le_add le_rfl h2)
        _ < (s : EReal) + (C : EReal) := EReal.add_lt_add_right_coe ht₀ C
        _ = ((s + C : ℝ) : EReal) := by rw [EReal.coe_add]
    have hw := multiplierWeight_antitone hc.le hlt.le
    rw [multiplierWeight_coe] at hw
    exact hw.trans (hA t₁ hTt₁)
  set I := ⨅ t : Ioi (0 : ℝ), F t.1 - ((t.1 * τ : ℝ) : EReal) with hI
  induction hIe : I using EReal.rec with
  | bot =>
    rw [multiplierWeight_bot hc]
    have hAtop : A = ⊤ := by
      by_contra hne
      set a := A.toReal
      have h := key (-(Real.log (a + 1)) / c - C) (by rw [hIe]; exact EReal.bot_lt_coe _)
      have he : Real.exp (-(c * (-(Real.log (a + 1)) / c - C + C))) = a + 1 := by
        rw [show -(c * (-(Real.log (a + 1)) / c - C + C)) = Real.log (a + 1) by
          field_simp; ring]
        exact Real.exp_log (by positivity)
      rw [he] at h
      have := (ENNReal.ofReal_le_iff_le_toReal hne).mp h
      linarith
    rw [hAtop, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | top =>
    rw [multiplierWeight_top hc]
    exact bot_le
  | coe r =>
    have h := key (r + 1) (by rw [hIe]; exact_mod_cast (by linarith : r < r + 1))
    rw [multiplierWeight_coe]
    calc ENNReal.ofReal (Real.exp (-(c * r)))
        = ENNReal.ofReal (Real.exp (c * (1 + C))) *
            ENNReal.ofReal (Real.exp (-(c * (r + 1 + C)))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2; ring
      _ ≤ ENNReal.ofReal (Real.exp (c * (1 + C))) * A := by gcongr

/-! ### The Legendre transform of a test curve -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- `Γ_τ(y) + tτ ≤ Γ^*_t(y)`. -/
theorem slice_add_le_rawLegendre (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) (t : ℝ) (y : M) :
    Γ.potential τ y + ((t * τ.1 : ℝ) : EReal) ≤ sourceTestCurveRawLegendre Γ t y := by
  rw [Γ.rawLegendre_eq_iSup_open t y, add_comm]
  exact le_iSup (fun σ : Iio Γ.max => ((t * σ.1 : ℝ) : EReal) + Γ.potential σ y) τ

/-- `t ↦ Γ^*_t(y)` is decreasing when `Γ_max ≤ 0`. -/
theorem rawLegendre_antitone (Γ : SourceTestCurvePredata θ) (hmax : Γ.max ≤ 0) (y : M)
    {t t' : ℝ} (htt' : t ≤ t') :
    sourceTestCurveRawLegendre Γ t' y ≤ sourceTestCurveRawLegendre Γ t y := by
  rw [Γ.rawLegendre_eq_iSup_open t' y, Γ.rawLegendre_eq_iSup_open t y]
  refine iSup_mono fun σ => add_le_add ?_ le_rfl
  exact EReal.coe_le_coe_iff.mpr
    (mul_le_mul_of_nonpos_right htt' ((le_of_lt σ.2).trans hmax))

theorem rawLegendre_ne_top (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) (y : M) :
    sourceTestCurveRawLegendre Γ t y ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (Γ.rawLegendre_le_cutoff ht y)

theorem slice_ne_top (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) (y : M) :
    Γ.potential τ y ≠ ⊤ :=
  ne_top_of_le_ne_top EReal.zero_ne_top (Γ.le_zero τ y)

/-! ### The radial weight -/

/-- `D_{k,i}(y, r) = ∫_{|w| < r} |w|^{2i} e^{-kΓ^*_{-log|w|²}(y)} dw`, `w ∈ ℂ¹`. -/
def radialWeight (Γ : SourceTestCurvePredata θ) (k i : ℕ) (y : M) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in ball (0 : ComplexModel 1) r, ENNReal.ofReal (‖w‖ ^ (2 * i)) *
    multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (‖w‖ ^ 2)) y)

theorem neg_log_sq_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) : 0 ≤ -Real.log (a ^ 2) := by
  rw [neg_nonneg]
  exact Real.log_nonpos (sq_nonneg _) (by nlinarith)

/-- **The annulus estimate.** For `0 < ρ < r ≤ 1`,
`(ρ/2)^{2i} vol({ρ/2 < |w| < ρ}) e^{-kΓ^*_{-log ρ²}(y)} ≤ D_{k,i}(y, r)`. -/
theorem annulus_le_radialWeight (Γ : SourceTestCurvePredata θ) (hmax : Γ.max ≤ 0) {k : ℕ}
    (i : ℕ) (y : M) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    ENNReal.ofReal ((ρ / 2) ^ (2 * i)) *
        (ENNReal.ofReal (3 / 4 * ρ ^ 2) * volume (ball (0 : ComplexModel 1) 1)) *
        multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (ρ ^ 2)) y) ≤
      radialWeight Γ k i y r := by
  set A : Set (ComplexModel 1) := ball 0 ρ \ closedBall 0 (ρ / 2) with hA
  have hAsub : A ⊆ ball 0 r := fun w hw => ball_subset_ball hρr.le hw.1
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hpt : ∀ w ∈ A, ENNReal.ofReal ((ρ / 2) ^ (2 * i)) *
      multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (ρ ^ 2)) y) ≤
      ENNReal.ofReal (‖w‖ ^ (2 * i)) *
        multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (‖w‖ ^ 2)) y) := by
    intro w hw
    have hw1 : ‖w‖ < ρ := mem_ball_zero_iff.mp hw.1
    have hw2 : ρ / 2 < ‖w‖ := by
      have := hw.2
      rw [mem_closedBall_zero_iff, not_le] at this
      exact this
    have hwpos : 0 < ‖w‖ := lt_trans (by linarith) hw2
    gcongr
    · apply multiplierWeight_antitone (Nat.cast_nonneg k)
      apply rawLegendre_antitone Γ hmax y
      have : Real.log (‖w‖ ^ 2) ≤ Real.log (ρ ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      linarith
  calc ENNReal.ofReal ((ρ / 2) ^ (2 * i)) *
        (ENNReal.ofReal (3 / 4 * ρ ^ 2) * volume (ball (0 : ComplexModel 1) 1)) *
        multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (ρ ^ 2)) y)
      = ∫⁻ _ in A, ENNReal.ofReal ((ρ / 2) ^ (2 * i)) *
          multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (ρ ^ 2)) y) := by
        rw [setLIntegral_const, volume_annulus hρ]
        ring
    _ ≤ ∫⁻ w in A, ENNReal.ofReal (‖w‖ ^ (2 * i)) *
          multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ (-Real.log (‖w‖ ^ 2)) y) :=
        setLIntegral_mono' hAm hpt
    _ ≤ radialWeight Γ k i y r := lintegral_mono_set hAsub

/-- **The slice is controlled by the radial weight.** For `k ≥ 1`, `i ∈ ℕ`,
`τ = -(i+1)/k < Γ_max ≤ 0` and `0 < r ≤ 1`:
`e^{-kΓ_τ(y)} ≤ K D_{k,i}(y, r)` with
`K = e^{k(1 + (T+1)(-τ))} ((3/4) 4^{-i} vol B(0,1))⁻¹`, `T = -log r²`. -/
theorem multiplierWeight_slice_le_radialWeight [CompactSpace M] [ConnectedSpace M]
    (Γ : SourceTestCurvePredata θ) (hmax : Γ.max ≤ 0)
    {k : ℕ} (hk : 0 < k) (i : ℕ) (hτ : -((i : ℝ) + 1) / k < Γ.max) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) (y : M) :
    multiplierWeight (k : ℝ) (Γ.potential ⟨-((i : ℝ) + 1) / k, hτ⟩ y) ≤
      ENNReal.ofReal (Real.exp ((k : ℝ) * (1 + (-Real.log (r ^ 2) + 1) *
          (-(-((i : ℝ) + 1) / k))))) *
        ((ENNReal.ofReal (3 / 4 * (1 / 2) ^ (2 * i)) * volume (ball (0 : ComplexModel 1) 1))⁻¹ *
          radialWeight Γ k i y r) := by
  set τ : ℝ := -((i : ℝ) + 1) / k with hτdef
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hτneg : τ ≤ 0 := (le_of_lt hτ).trans hmax
  set T : ℝ := -Real.log (r ^ 2) with hT
  have hT0 : 0 ≤ T := neg_log_sq_nonneg hr0.le hr1
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (3 / 4 * (1 / 2) ^ (2 * i)) * volume (ball (0 : ComplexModel 1) 1)
    with hK₀
  have hK₀0 : K₀ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    volume_unitBall_pos.ne'
  have hK₀top : K₀ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top volume_unitBall_ne_top
  -- the slice through the inverse Legendre formula
  have hslice : Γ.potential ⟨τ, hτ⟩ y =
      ⨅ t : Ioi (0 : ℝ), sourceTestCurveRawLegendre Γ t.1 y - ((t.1 * τ : ℝ) : EReal) := by
    rw [← Γ.at_eq_iInf_positive_rawLegendre τ y]
    simp only [sourceTestCurveAt, dif_pos hτ]
  rw [hslice]
  apply multiplierWeight_iInf_le_of_tail hkpos hτneg hT0
    (fun t t' ht htt' => rawLegendre_antitone Γ hmax y htt')
  intro t ht
  -- `ρ = e^{-t/2} ∈ (0, r)` and `-log ρ² = t`
  set ρ : ℝ := Real.exp (-t / 2) with hρ
  have hρpos : 0 < ρ := Real.exp_pos _
  have hρsq : ρ ^ 2 = Real.exp (-t) := by
    rw [hρ, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hlogρ : -Real.log (ρ ^ 2) = t := by rw [hρsq, Real.log_exp, neg_neg]
  have hρr : ρ < r := by
    have h1 : Real.log (ρ ^ 2) < Real.log (r ^ 2) := by
      rw [hρsq, Real.log_exp]; linarith
    have h2 : ρ ^ 2 < r ^ 2 := (Real.log_lt_log_iff (by positivity) (by positivity)).mp h1
    nlinarith
  have hann := annulus_le_radialWeight Γ hmax (k := k) i y hρpos hρr hr1
  rw [hlogρ] at hann
  -- the weight of `Γ^*_t - tτ` is `ρ^{2i+2}` times the weight of `Γ^*_t`
  have hwt : multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y - ((t * τ : ℝ) : EReal)) =
      multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) *
        ENNReal.ofReal (ρ ^ (2 * i) * ρ ^ 2) := by
    rw [multiplierWeight_sub_real hkpos (rawLegendre_ne_top Γ (by linarith) y)]
    congr 2
    rw [← pow_add, show 2 * i + 2 = 2 * (i + 1) by ring, pow_mul, hρsq, ← Real.exp_nat_mul]
    congr 1
    rw [hτdef]; field_simp; push_cast; ring
  rw [hwt, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hK₀0) (Or.inl hK₀top)]
  have hab : ρ ^ (2 * i) * ρ ^ 2 * (3 / 4 * (1 / 2) ^ (2 * i)) =
      (ρ / 2) ^ (2 * i) * (3 / 4 * ρ ^ 2) := by
    rw [div_pow, div_pow, one_pow]; ring
  calc multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) *
        ENNReal.ofReal (ρ ^ (2 * i) * ρ ^ 2) * K₀
      = multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) *
          (ENNReal.ofReal (ρ ^ (2 * i) * ρ ^ 2) * ENNReal.ofReal (3 / 4 * (1 / 2) ^ (2 * i))) *
          volume (ball (0 : ComplexModel 1) 1) := by rw [hK₀]; ring
    _ = multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) *
          ENNReal.ofReal ((ρ / 2) ^ (2 * i) * (3 / 4 * ρ ^ 2)) *
          volume (ball (0 : ComplexModel 1) 1) := by
        rw [← ENNReal.ofReal_mul (by positivity), hab]
    _ = ENNReal.ofReal ((ρ / 2) ^ (2 * i)) *
          (ENNReal.ofReal (3 / 4 * ρ ^ 2) * volume (ball (0 : ComplexModel 1) 1)) *
          multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring
    _ ≤ radialWeight Γ k i y r := hann


/-- The constant of `multiplierWeight_slice_le_radialWeight` is finite and independent of `y`. -/
theorem exists_multiplierWeight_slice_le_radialWeight [CompactSpace M] [ConnectedSpace M]
    (Γ : SourceTestCurvePredata θ) (hmax : Γ.max ≤ 0) {k : ℕ} (hk : 0 < k) (i : ℕ)
    (hτ : -((i : ℝ) + 1) / k < Γ.max) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ y : M,
      multiplierWeight (k : ℝ) (Γ.potential ⟨-((i : ℝ) + 1) / k, hτ⟩ y) ≤
        K * radialWeight Γ k i y r := by
  have hK₀0 : ENNReal.ofReal (3 / 4 * (1 / 2) ^ (2 * i)) * volume (ball (0 : ComplexModel 1) 1)
      ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' volume_unitBall_pos.ne'
  refine ⟨ENNReal.ofReal (Real.exp ((k : ℝ) * (1 + (-Real.log (r ^ 2) + 1) *
      (-(-((i : ℝ) + 1) / k))))) *
      (ENNReal.ofReal (3 / 4 * (1 / 2) ^ (2 * i)) * volume (ball (0 : ComplexModel 1) 1))⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hK₀0), fun y => ?_⟩
  rw [mul_assoc]
  exact multiplierWeight_slice_le_radialWeight Γ hmax hk i hτ hr0 hr1 y

/-- `Γ^*_t(y) ≥ Γ_τ(y) + tτ` gives `e^{-kΓ^*_t(y)} ≤ e^{-kΓ_τ(y)} e^{-ktτ}`. -/
theorem multiplierWeight_raw_le (Γ : SourceTestCurvePredata θ) {c : ℝ} (hc : 0 < c)
    (τ : Iio Γ.max) (t : ℝ) (y : M) :
    multiplierWeight c (sourceTestCurveRawLegendre Γ t y) ≤
      multiplierWeight c (Γ.potential τ y) * ENNReal.ofReal (Real.exp (-(c * (t * τ.1)))) := by
  rw [← multiplierWeight_add_real hc (slice_ne_top Γ τ y)]
  exact multiplierWeight_antitone hc.le (slice_add_le_rawLegendre Γ τ t y)

/-- `x^{2i} e^{-k(-log x²)τ} = x^{2(i + kτ)}` for `x > 0` (real powers). -/
theorem pow_mul_exp_eq_rpow {x : ℝ} (hx : 0 < x) (i : ℕ) (c τ : ℝ) :
    x ^ (2 * i) * Real.exp (-(c * (-Real.log (x ^ 2) * τ))) =
      x ^ (2 * ((i : ℝ) + c * τ)) := by
  rw [Real.rpow_def_of_pos hx, Real.log_pow, ← Real.exp_log (pow_pos hx (2 * i)),
    Real.log_pow, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The pole estimate.** If `i + 1 + kΓ_max ≤ 0` then `D_{k,i}(y, r) = ∞` for `0 < r ≤ 1`:
by `Γ^*_t ≤ tΓ_max`, the integrand is at least `|w|^{2(i + kΓ_max)} ≥ |w|^{-2}`. -/
theorem radialWeight_eq_top (Γ : SourceTestCurvePredata θ) {k i : ℕ}
    (hki : (i : ℝ) + 1 + k * Γ.max ≤ 0) (y : M) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    radialWeight Γ k i y r = ⊤ := by
  apply eq_top_iff.mpr
  rw [← SGPT.GAGA.H0.lintegral_ball_norm_rpow_eq_top (r := 1) one_pos hr0]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ComplexModel 1))] with w hw hw0
  have ha : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have ha1 : ‖w‖ < 1 := lt_of_lt_of_le (mem_ball_zero_iff.mp hw) hr1
  set t : ℝ := -Real.log (‖w‖ ^ 2) with ht
  have ht0 : 0 ≤ t := neg_log_sq_nonneg (norm_nonneg _) ha1.le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw1 : multiplierWeight (k : ℝ) ((t * Γ.max : ℝ) : EReal) ≤
      multiplierWeight (k : ℝ) (sourceTestCurveRawLegendre Γ t y) :=
    multiplierWeight_antitone hk0 (Γ.rawLegendre_le_cutoff ht0 y)
  rw [multiplierWeight_coe] at hw1
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hw1 bot_le)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlog : Real.log ‖w‖ < 0 := Real.log_neg ha ha1
  rw [Real.rpow_def_of_pos ha, ← Real.exp_log (pow_pos ha (2 * i)), ← Real.exp_add, ht,
    Real.log_pow, Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

/-- `∫_{|w| < r} |w|^s dw < ∞` in `ℂ¹` for `s > -2`. -/
theorem lintegral_ball_rpow_lt_top {s : ℝ} (hs : -2 < s) (r : ℝ) :
    ∫⁻ w in ball (0 : ComplexModel 1) r, ENNReal.ofReal (‖w‖ ^ s) < ⊤ := by
  have hint : IntegrableOn (fun w : ComplexModel 1 => ‖w‖ ^ s) (ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := -s) ?_ ?_ ?_ ?_
    · rw [finrank_complexModel_one]; norm_num
    · rw [finrank_complexModel_one]; push_cast; linarith
    · refine Eventually.of_forall fun w => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul, neg_neg]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  exact hint.lintegral_lt_top

end SGPT.NAPotential.NAGaga
