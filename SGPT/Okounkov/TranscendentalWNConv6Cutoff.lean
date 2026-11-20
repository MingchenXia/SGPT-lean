import SGPT.Okounkov.TranscendentalWNConvStatement
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The cutoff `χ` of WN21 §6 exists

Blueprint `tok-wn-conv6:cutoff` (chapter `claude-tok-wn-conv6`); source WN21 §6 (the smooth convex
`χ` with `χ(x) = x` for `x ≥ 0` and `χ(x) = eˣ - 1` for `x ≤ -1`, whose existence WN21 takes for
granted).

`χ` is a primitive of a smooth nondecreasing `h` with `h = eˣ` on `(-∞, -1]`, `h = 1` on
`[0, ∞)` and `∫_{-1}^0 h = 1 - e⁻¹`:

`h_a(x) = C - (C - eˣ)(1 - σ(8(x + 1))) + (1 - C) σ(8(x - a))`, `C = e^{-7/8}`,

with `σ = Real.smoothTransition`; the first part increases from `eˣ` to `C` on `[-1, -7/8]`, the
second jumps from `0` to `1 - C` on `[a, a + 1/8]`.  `a ↦ ∫_{-1}^0 h_a` is continuous, `≥ 3/4` at
`a = -7/8` and `≤ 71/120` at `a = -1/8`, so the intermediate value theorem gives `a` with
`∫_{-1}^0 h_a = 1 - e⁻¹`; then `χ(x) = e⁻¹ - 1 + ∫_{-1}^x h_a` (`exists_isWNCutoff`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ContDiff

namespace Cutoff

/-- The constant `C = e^{-7/8}`. -/
def cst : ℝ := Real.exp (-7 / 8)

theorem cst_pos : 0 < cst := Real.exp_pos _

theorem cst_le : cst ≤ 8 / 15 := by
  have h := Real.add_one_le_exp (7 / 8 : ℝ)
  have hpos : 0 < Real.exp (7 / 8 : ℝ) := Real.exp_pos _
  have hmul : cst * Real.exp (7 / 8) = 1 := by
    rw [cst, ← Real.exp_add]; norm_num
  have : cst * (15 / 8) ≤ 1 := by
    calc cst * (15 / 8) ≤ cst * Real.exp (7 / 8) :=
          mul_le_mul_of_nonneg_left (by linarith) cst_pos.le
      _ = 1 := hmul
  linarith

theorem cst_lt_one : cst < 1 := by
  have := cst_le; linarith

/-- The first (rising) part `C - (C - eˣ)(1 - σ(8(x + 1)))`. -/
def rise (x : ℝ) : ℝ := cst - (cst - Real.exp x) * (1 - Real.smoothTransition (8 * (x + 1)))

/-- The derivative `h_a` of the cutoff. -/
def slope (a x : ℝ) : ℝ := rise x + (1 - cst) * Real.smoothTransition (8 * (x - a))

theorem rise_of_le {x : ℝ} (hx : x ≤ -1) : rise x = Real.exp x := by
  rw [rise, Real.smoothTransition.zero_of_nonpos (by linarith)]; ring

theorem rise_of_ge {x : ℝ} (hx : -7 / 8 ≤ x) : rise x = cst := by
  rw [rise, Real.smoothTransition.one_of_one_le (by linarith)]; ring

theorem rise_le (x : ℝ) : rise x ≤ cst := by
  rcases le_or_gt x (-7 / 8) with hx | hx
  · have h1 : 0 ≤ cst - Real.exp x := by
      rw [sub_nonneg, cst]; exact Real.exp_le_exp.mpr hx
    have h2 : 0 ≤ 1 - Real.smoothTransition (8 * (x + 1)) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have := mul_nonneg h1 h2
    rw [rise]; linarith
  · rw [rise_of_ge hx.le]

theorem rise_nonneg (x : ℝ) : 0 ≤ rise x := by
  have hσ0 := Real.smoothTransition.nonneg (8 * (x + 1))
  have hσ1 := Real.smoothTransition.le_one (8 * (x + 1))
  have he := Real.exp_pos x
  have hc := cst_pos
  have : rise x = cst * Real.smoothTransition (8 * (x + 1)) +
      Real.exp x * (1 - Real.smoothTransition (8 * (x + 1))) := by rw [rise]; ring
  rw [this]
  exact add_nonneg (mul_nonneg hc.le hσ0) (mul_nonneg he.le (by linarith))

theorem rise_monotone : Monotone rise := by
  intro x y hxy
  rcases le_or_gt y (-7 / 8) with hy | hy
  · have hx : x ≤ -7 / 8 := hxy.trans hy
    have h1x : 0 ≤ cst - Real.exp x := by rw [sub_nonneg, cst]; exact Real.exp_le_exp.mpr hx
    have h1 : cst - Real.exp y ≤ cst - Real.exp x := by
      linarith [Real.exp_le_exp.mpr hxy]
    have h1y : 0 ≤ cst - Real.exp y := by rw [sub_nonneg, cst]; exact Real.exp_le_exp.mpr hy
    have h2 : 1 - Real.smoothTransition (8 * (y + 1)) ≤ 1 - Real.smoothTransition (8 * (x + 1)) :=
      sub_le_sub_left (Real.smoothTransition.monotone (by linarith)) _
    have h2y : 0 ≤ 1 - Real.smoothTransition (8 * (y + 1)) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have := mul_le_mul h1 h2 h2y h1x
    rw [rise, rise]; linarith
  · rw [rise_of_ge hy.le]; exact rise_le x

theorem continuous_rise : Continuous rise := by
  unfold rise
  have := Real.smoothTransition.continuous
  fun_prop

theorem contDiff_rise : ContDiff ℝ ∞ rise := by
  unfold rise
  have h : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  have h8 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (8 * (x + 1))) :=
    h.comp (contDiff_const.mul (contDiff_id.add contDiff_const))
  exact contDiff_const.sub ((contDiff_const.sub Real.contDiff_exp).mul (contDiff_const.sub h8))

theorem continuous_slope_uncurry : Continuous (Function.uncurry slope) := by
  have h1 : Continuous fun p : ℝ × ℝ => rise p.2 := continuous_rise.comp continuous_snd
  have h2 : Continuous fun p : ℝ × ℝ => Real.smoothTransition (8 * (p.2 - p.1)) :=
    Real.smoothTransition.continuous.comp (by fun_prop)
  exact h1.add (continuous_const.mul h2)

theorem continuous_slope (a : ℝ) : Continuous (slope a) :=
  continuous_slope_uncurry.comp (Continuous.prodMk continuous_const continuous_id)

theorem contDiff_slope (a : ℝ) : ContDiff ℝ ∞ (slope a) := by
  have h : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  exact contDiff_rise.add (contDiff_const.mul (h.comp (contDiff_const.mul
    (contDiff_id.sub contDiff_const))))

theorem slope_monotone (a : ℝ) : Monotone (slope a) := by
  intro x y hxy
  have := mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone
    (show 8 * (x - a) ≤ 8 * (y - a) by linarith)) (sub_nonneg.mpr cst_lt_one.le)
  exact add_le_add (rise_monotone hxy) this

theorem slope_of_le {a x : ℝ} (ha : -1 ≤ a) (hx : x ≤ -1) : slope a x = Real.exp x := by
  rw [slope, rise_of_le hx, Real.smoothTransition.zero_of_nonpos (by linarith)]; ring

theorem slope_of_ge {a x : ℝ} (ha : a ≤ -1 / 8) (hx : 0 ≤ x) : slope a x = 1 := by
  rw [slope, rise_of_ge (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]; ring

theorem slope_nonneg (a x : ℝ) : 0 ≤ slope a x :=
  add_nonneg (rise_nonneg x) (mul_nonneg (sub_nonneg.mpr cst_lt_one.le)
    (Real.smoothTransition.nonneg _))

/-- `∫_{-1}^0 h_a`. -/
def mass (a : ℝ) : ℝ := ∫ x in (-1 : ℝ)..0, slope a x

theorem continuous_mass : Continuous mass :=
  continuous_parametric_intervalIntegral_of_continuous' continuous_slope_uncurry _ _

theorem mass_left : 3 / 4 ≤ mass (-7 / 8) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (slope (-7 / 8)) volume a b := fun a b =>
    (continuous_slope _).intervalIntegrable a b
  rw [mass, ← integral_add_adjacent_intervals (hint (-1) (-3 / 4)) (hint (-3 / 4) 0)]
  have h1 : 0 ≤ ∫ x in (-1 : ℝ)..(-3 / 4), slope (-7 / 8) x :=
    integral_nonneg (by norm_num) fun x _ => slope_nonneg _ x
  have h2 : ∫ x in (-3 / 4 : ℝ)..0, slope (-7 / 8) x = ∫ _x in (-3 / 4 : ℝ)..0, (1 : ℝ) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [slope, rise_of_ge (by linarith [hx.1]),
      Real.smoothTransition.one_of_one_le (by linarith [hx.1])]
    ring
  rw [h2]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  linarith

theorem mass_right : mass (-1 / 8) ≤ 71 / 120 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (slope (-1 / 8)) volume a b := fun a b =>
    (continuous_slope _).intervalIntegrable a b
  rw [mass, ← integral_add_adjacent_intervals (hint (-1) (-1 / 8)) (hint (-1 / 8) 0)]
  have h1 : ∫ x in (-1 : ℝ)..(-1 / 8), slope (-1 / 8) x ≤ ∫ _x in (-1 : ℝ)..(-1 / 8), cst := by
    refine integral_mono_on (by norm_num) (hint _ _) intervalIntegrable_const fun x hx => ?_
    rw [slope, Real.smoothTransition.zero_of_nonpos (by linarith [hx.2])]
    simpa using rise_le x
  have h2 : ∫ x in (-1 / 8 : ℝ)..0, slope (-1 / 8) x ≤ ∫ _x in (-1 / 8 : ℝ)..0, (1 : ℝ) := by
    refine integral_mono_on (by norm_num) (hint _ _) intervalIntegrable_const fun x _ => ?_
    have := rise_le x
    have := Real.smoothTransition.le_one (8 * (x - -1 / 8))
    have := cst_lt_one
    rw [slope]; nlinarith
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1 h2
  have := cst_le
  linarith

theorem one_sub_exp_neg_one_mem :
    1 - Real.exp (-1) ∈ Icc (mass (-1 / 8)) (mass (-7 / 8)) := by
  have he1 : Real.exp (-1) ≤ 49 / 120 := by
    have h := Real.exp_one_gt_d9
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have hpos := Real.exp_pos (-1 : ℝ)
    nlinarith
  have he2 : 1 / 4 ≤ Real.exp (-1) := by
    have h := Real.exp_one_lt_d9
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have hpos := Real.exp_pos (-1 : ℝ)
    nlinarith
  exact ⟨by linarith [mass_right], by linarith [mass_left]⟩

theorem exists_mass_eq : ∃ a ∈ Icc (-7 / 8 : ℝ) (-1 / 8), mass a = 1 - Real.exp (-1) := by
  obtain ⟨a, ha, h⟩ := intermediate_value_Icc' (show (-7 / 8 : ℝ) ≤ -1 / 8 by norm_num)
    continuous_mass.continuousOn one_sub_exp_neg_one_mem
  exact ⟨a, ha, h⟩

/-- The cutoff `χ(x) = e⁻¹ - 1 + ∫_{-1}^x h_a`. -/
def cutoffOf (a : ℝ) (x : ℝ) : ℝ := Real.exp (-1) - 1 + ∫ t in (-1 : ℝ)..x, slope a t

theorem hasDerivAt_cutoffOf (a x : ℝ) : HasDerivAt (cutoffOf a) (slope a x) x :=
  ((continuous_slope a).integral_hasStrictDerivAt (-1) x).hasDerivAt.const_add _

theorem deriv_cutoffOf (a : ℝ) : deriv (cutoffOf a) = slope a :=
  funext fun x => (hasDerivAt_cutoffOf a x).deriv

theorem isWNCutoff_cutoffOf {a : ℝ} (ha : a ∈ Icc (-7 / 8 : ℝ) (-1 / 8))
    (hm : mass a = 1 - Real.exp (-1)) : IsWNCutoff (cutoffOf a) := by
  have hdiff : Differentiable ℝ (cutoffOf a) := fun x =>
    (hasDerivAt_cutoffOf a x).differentiableAt
  have hint : ∀ u v : ℝ, IntervalIntegrable (slope a) volume u v := fun u v =>
    (continuous_slope a).intervalIntegrable u v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [contDiff_infty_iff_deriv, deriv_cutoffOf]
    exact ⟨hdiff, contDiff_slope a⟩
  · exact Monotone.convexOn_univ_of_deriv hdiff (by rw [deriv_cutoffOf]; exact slope_monotone a)
  · intro x hx
    rw [cutoffOf, ← integral_add_adjacent_intervals (hint (-1) 0) (hint 0 x)]
    have h0 : ∫ t in (0 : ℝ)..x, slope a t = ∫ _t in (0 : ℝ)..x, (1 : ℝ) := by
      refine integral_congr fun t ht => ?_
      rw [uIcc_of_le hx] at ht
      exact slope_of_ge ha.2 ht.1
    have hm' : ∫ t in (-1 : ℝ)..0, slope a t = 1 - Real.exp (-1) := hm
    rw [hm', h0]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    ring
  · intro x hx
    rw [cutoffOf]
    have h0 : ∫ t in (-1 : ℝ)..x, slope a t = ∫ t in (-1 : ℝ)..x, Real.exp t := by
      refine integral_congr fun t ht => ?_
      rw [uIcc_of_ge hx] at ht
      exact slope_of_le (by linarith [ha.1]) ht.2
    rw [h0, integral_exp]
    ring

end Cutoff

/-- **The cutoff of WN21 §6 exists** (`tok-wn-conv6:cutoff`): there is a smooth convex
`χ : ℝ → ℝ` with `χ(x) = x` for `x ≥ 0` and `χ(x) = eˣ - 1` for `x ≤ -1`. -/
theorem exists_isWNCutoff : ∃ χ : ℝ → ℝ, IsWNCutoff χ := by
  obtain ⟨a, ha, hm⟩ := Cutoff.exists_mass_eq
  exact ⟨Cutoff.cutoffOf a, Cutoff.isWNCutoff_cutoffOf ha hm⟩

end SGPT.Okounkov.TranscendentalWN
