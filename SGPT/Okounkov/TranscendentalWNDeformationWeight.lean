import SGPT.Okounkov.TranscendentalWNDeformationLine

/-!
# The weight comparison on `X × ℂ`

Blueprint `tok-wn-def:weight-comparison` (`claude-tok-wn-def`), used in the proof of
`tok-wn:legendre-identification` (WN21 Proposition 4.5) for the functions
`v_t + λ log |τ|²`, `v_t ≤ t g + C`, in place of the Lelong-number argument along `ℰ`.

For `0 < r = |s_Z|²_h ≤ 1`, `0 < |τ| ≤ 1` and `t, λ ≥ 0` with `t + λ ≥ c ≥ 0`:
`t log r + λ log |τ|² ≤ c log ((r + |τ|²) / (1 + |τ|²)) + (t + λ) log 2`
(`log_exceptional_comparison`), and in terms of `W` (`log_baseExceptionalWeight_comparison`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Real

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- `N₁ = 1 / (1 + |τ|²)` off `∞`. -/
theorem projectiveWeight_one_eq {p : ProjectiveLine} (hp : p.rep 1 ≠ 0) :
    projectiveWeight 1 p = 1 / (1 + ‖projectiveAffine p‖ ^ 2) := by
  have h := projectiveWeight_add p
  rw [projectiveWeight_zero_eq hp] at h
  have hpos : 0 < 1 + ‖projectiveAffine p‖ ^ 2 := by positivity
  field_simp
  linarith

/-- **`W` in the affine coordinate**: `W(x, τ) = (|s_Z(x)|²_h + |τ|²) / (1 + |τ|²)` for `τ ≠ ∞`. -/
theorem baseExceptionalWeight_eq_affine
    (E : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor (m + 1) F.carrier)
    {q : F.carrier × ProjectiveLine} (hq : q.2.rep 1 ≠ 0) :
    baseExceptionalWeight F E q =
      ((EReal.exp (E.weight q.1)).toReal + ‖projectiveAffine q.2‖ ^ 2) /
        (1 + ‖projectiveAffine q.2‖ ^ 2) := by
  rw [baseExceptionalWeight_eq, projectiveWeight_zero_eq hq, projectiveWeight_one_eq hq]
  have hpos : 0 < 1 + ‖projectiveAffine q.2‖ ^ 2 := by positivity
  field_simp

/-- `W ≤ 1` (i.e. `|s_ℰ| ≤ 1`) when `|s_Z|_h ≤ 1`. -/
theorem baseExceptionalWeight_le_one
    (E : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hE : ∀ x, E.weight x ≤ 0) (q : F.carrier × ProjectiveLine) :
    baseExceptionalWeight F E q ≤ 1 := by
  rw [baseExceptionalWeight_eq]
  have hr : (EReal.exp (E.weight q.1)).toReal ≤ 1 := by
    have h1 : EReal.exp (E.weight q.1) ≤ 1 := by
      have := EReal.exp_monotone (hE q.1)
      simpa using this
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    simpa using this
  have h0 := projectiveWeight_nonneg 1 q.2
  have hadd := projectiveWeight_add q.2
  nlinarith [ENNReal.toReal_nonneg (a := EReal.exp (E.weight q.1))]

/-- **The weight comparison** (real form). -/
theorem log_exceptional_comparison {r s t l c : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hs1 : s ≤ 1) (ht : 0 ≤ t) (hl : 0 ≤ l) (hc : 0 ≤ c) (htl : c ≤ t + l) :
    t * Real.log r + l * Real.log s ≤
      c * Real.log ((r + s) / (1 + s)) + (t + l) * Real.log 2 := by
  have hR : 0 < r + s := by linarith
  have hR2 : r + s ≤ 2 := by linarith
  have hlogR : Real.log (r + s) ≤ Real.log 2 := Real.log_le_log hR hR2
  have h1 : Real.log r ≤ Real.log (r + s) := Real.log_le_log hr (by linarith)
  have h2 : Real.log s ≤ Real.log (r + s) := Real.log_le_log hs (by linarith)
  have h3 : Real.log ((r + s) / (1 + s)) = Real.log (r + s) - Real.log (1 + s) :=
    Real.log_div hR.ne' (by linarith)
  have h4 : Real.log (1 + s) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have h5 : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  rw [h3]
  have e1 : t * Real.log r ≤ t * Real.log (r + s) := mul_le_mul_of_nonneg_left h1 ht
  have e2 : l * Real.log s ≤ l * Real.log (r + s) := mul_le_mul_of_nonneg_left h2 hl
  have e3 : (t + l - c) * Real.log (r + s) ≤ (t + l - c) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlogR (by linarith)
  have e4 : c * Real.log (1 + s) ≤ c * Real.log 2 := mul_le_mul_of_nonneg_left h4 hc
  nlinarith

/-- **The weight comparison** for `W` (`tok-wn-def:weight-comparison`): at `(x, τ)` with
`x ∉ Z`, `0 < |τ| ≤ 1`, for `|s_Z|_h ≤ 1` and `t, λ ≥ 0`, `t + λ ≥ c ≥ 0`,
`t log |s_Z(x)|²_h + λ log |τ|² ≤ c log W(x, τ) + (t + λ) log 2`. -/
theorem log_baseExceptionalWeight_comparison
    (E : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hE : ∀ x, E.weight x ≤ 0) {q : F.carrier × ProjectiveLine} (hq : q.2.rep 1 ≠ 0)
    (hr : 0 < (EReal.exp (E.weight q.1)).toReal) (hτ : projectiveAffine q.2 ≠ 0)
    (hτ1 : ‖projectiveAffine q.2‖ ≤ 1) {t l c : ℝ} (ht : 0 ≤ t) (hl : 0 ≤ l) (hc : 0 ≤ c)
    (htl : c ≤ t + l) :
    t * Real.log (EReal.exp (E.weight q.1)).toReal + l * Real.log (‖projectiveAffine q.2‖ ^ 2) ≤
      c * Real.log (baseExceptionalWeight F E q) + (t + l) * Real.log 2 := by
  have hr1 : (EReal.exp (E.weight q.1)).toReal ≤ 1 := by
    have h1 : EReal.exp (E.weight q.1) ≤ 1 := by
      have := EReal.exp_monotone (hE q.1)
      simpa using this
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    simpa using this
  rw [baseExceptionalWeight_eq_affine F E hq]
  exact log_exceptional_comparison hr hr1 (by positivity)
    (by nlinarith [norm_nonneg (projectiveAffine q.2)]) ht hl hc htl

end SGPT.Okounkov.TranscendentalWN
