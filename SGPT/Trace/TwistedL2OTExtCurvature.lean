import SGPT.Trace.TwistedL2Twist

/-!
# `thm:OT_ext`, Step 1: the twisted curvature along a normal pole

Blueprint `claude-ot-ext.tex`, node `claude-ot-ext:normal-twisted-curvature`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `thm:compact-submanifold-extension`, Step 1, display
`eq:global-normal-twisted-curvature`, in chart form.

Let `R > 0` be smooth with `R < e^{-4}`, `0 < ε < e^{-4}`, `ψ = log R`, `ψ_ε = log(ε + R)` and
`a_ε = μ_ε(ψ_ε)`, `b_ε = (2 - ψ_ε)²` the critical twist functions (`twistMu`, `twistB`).  For the
weight `p + qψ` (the local weight of `F = L ⊗ K_X^{-1}` with the extra pole `R^{-q}`), if
`Levi(p) ≥ A Q` and `Levi(ψ) ≥ -B Q` for a nonnegative quadratic quantity `Q` (in the
application `Q = ω(v, iv)`, `A = 2π N₀`, `B = 2π b`), with `qB ≤ A`, then the twisted curvature
satisfies

`H_ε(v) ≥ (A - (q + 2) B) Q + (ε/R) |∂ψ_ε(v)|²`             (`twistedCurvature_normal_pole_ge`),

and consequently `|∂ψ_ε(v)|² ≤ (R/ε) H_ε(v)` when `A ≥ (q + 2) B`
(`holDerivSq_le_of_twistedCurvature`), the rank-one bound used for the cut-off error
`g_ε^{(1)} = ρ'(R/ε)(1 + R/ε) ∂̄ψ_ε G` in Step 2.  The proof is FPT's: the twist identity
(`twistedCurvature_twist`), the logarithmic Hessian identity (`leviForm_log_add`) and the bounds
`a_ε ≥ 1`, `1 ≤ -μ'(ψ_ε) ≤ 2`, `0 ≤ R/(ε + R) ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

theorem holDerivSq_nonneg (f : ComplexModel n → ℝ) (z v : ComplexModel n) :
    0 ≤ holDerivSq f z v := by
  unfold holDerivSq
  positivity

/-- **The twisted curvature along a normal pole** (FPT `eq:global-normal-twisted-curvature`). -/
theorem twistedCurvature_normal_pole_ge {p R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p z) (hR : ContDiffAt ℝ 2 R z) (hRz : 0 < R z)
    (hR4 : R z < Real.exp (-4)) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) {q : ℝ}
    (hq : 0 ≤ q) {A B Q : ℝ} (v : ComplexModel n) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hqA : q * B ≤ A)
    (hpA : A * Q ≤ leviForm p z v)
    (hψB : -(B * Q) ≤ leviForm (fun y => Real.log (R y)) z v) :
    (A - (q + 2) * B) * Q + ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v ≤
      twistedCurvature (fun y => twistMu ε (Real.log (ε + R y)))
        (fun y => twistB (Real.log (ε + R y))) (fun y => p y + q * Real.log (R y)) z v := by
  have hS : ContDiffAt ℝ 2 (fun y => ε + R y) z := contDiffAt_const.add hR
  have hψε : ContDiffAt ℝ 2 (fun y => Real.log (ε + R y)) z := hS.log (by linarith)
  have hlogR : ContDiffAt ℝ 2 (fun y => Real.log (R y)) z := hR.log hRz.ne'
  obtain ⟨-, h3, -, -⟩ := twist_sum_le_five_sq hε hε4 hRz hR4
  rw [twistedCurvature_twist ε hψε (by linarith) v]
  -- the Levi form of the weight
  have hweight : leviForm (fun y => p y + q * Real.log (R y)) z v =
      leviForm p z v + q * leviForm (fun y => Real.log (R y)) z v := by
    have hsm : ContDiffAt ℝ 2 (q • fun y => Real.log (R y)) z := hlogR.const_smul q
    have h := leviForm_add hp hsm v
    rw [leviForm_smul hlogR] at h
    exact h
  rw [hweight, leviForm_log_add hR hRz hε v]
  -- the scalar bounds
  set t := Real.log (ε + R z) with ht
  have ha : 1 ≤ twistMu ε t := le_trans (by linarith) (neg_le_twistMu hε.le (by linarith))
  have hm1 : 1 ≤ -deriv (twistMu ε) t := one_le_neg_deriv_twistMu ε (by linarith)
  have hm2 : -deriv (twistMu ε) t ≤ 2 := neg_deriv_twistMu_le_two ε (by linarith)
  have hr0 : 0 ≤ R z / (ε + R z) := by positivity
  have hr1 : R z / (ε + R z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set D := holDerivSq (fun y => Real.log (ε + R y)) z v with hD
  have hD0 : 0 ≤ D := holDerivSq_nonneg _ _ _
  have hεR : 0 ≤ ε / R z := by positivity
  set L₁ := leviForm p z v
  set L₂ := leviForm (fun y => Real.log (R y)) z v
  set a := twistMu ε t
  set m := -deriv (twistMu ε) t
  set r := R z / (ε + R z)
  -- `a (L₁ + q L₂) ≥ (A - qB) Q`
  have h1 : (A - q * B) * Q ≤ a * (L₁ + q * L₂) := by
    have hle : (A - q * B) * Q ≤ L₁ + q * L₂ := by nlinarith
    have hnn : 0 ≤ (A - q * B) * Q := mul_nonneg (by linarith) hQ
    nlinarith
  -- `m r L₂ ≥ -2 B Q`
  have h2 : -(2 * (B * Q)) ≤ m * (r * L₂) := by
    have hmr0 : 0 ≤ m * r := mul_nonneg (by linarith) hr0
    have hmr2 : m * r ≤ 2 := by nlinarith
    have hBQ : 0 ≤ B * Q := mul_nonneg hB hQ
    nlinarith
  -- `m (ε/R) D ≥ (ε/R) D`
  have h3' : ε / R z * D ≤ m * (ε / R z * D) := by
    have : 0 ≤ ε / R z * D := mul_nonneg hεR hD0
    nlinarith
  have hgoal : a * (L₁ + q * L₂) - deriv (twistMu ε) t * (r * L₂ + ε / R z * D) =
      a * (L₁ + q * L₂) + m * (r * L₂) + m * (ε / R z * D) := by
    simp only [m]; ring
  rw [hgoal]
  nlinarith

/-- **The rank-one bound** used for the cut-off error of Step 2: if moreover `A ≥ (q + 2) B`, then
`|∂ψ_ε(v)|² ≤ (R/ε) H_ε(v)`. -/
theorem holDerivSq_le_of_twistedCurvature {p R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p z) (hR : ContDiffAt ℝ 2 R z) (hRz : 0 < R z)
    (hR4 : R z < Real.exp (-4)) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) {q : ℝ}
    (hq : 0 ≤ q) {A B Q : ℝ} (v : ComplexModel n) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hA : (q + 2) * B ≤ A) (hpA : A * Q ≤ leviForm p z v)
    (hψB : -(B * Q) ≤ leviForm (fun y => Real.log (R y)) z v) :
    holDerivSq (fun y => Real.log (ε + R y)) z v ≤
      R z / ε * twistedCurvature (fun y => twistMu ε (Real.log (ε + R y)))
        (fun y => twistB (Real.log (ε + R y))) (fun y => p y + q * Real.log (R y)) z v := by
  have hqA : q * B ≤ A := by nlinarith
  have h := twistedCurvature_normal_pole_ge hp hR hRz hR4 hε hε4 hq v hQ hB hqA hpA hψB
  have hnn : 0 ≤ (A - (q + 2) * B) * Q := mul_nonneg (by linarith) hQ
  have hle : ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v ≤
      twistedCurvature (fun y => twistMu ε (Real.log (ε + R y)))
        (fun y => twistB (Real.log (ε + R y))) (fun y => p y + q * Real.log (R y)) z v := by
    linarith
  have hRε : 0 < R z / ε := div_pos hRz hε
  calc holDerivSq (fun y => Real.log (ε + R y)) z v
      = R z / ε * (ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hRε.le

/-- **The lower bound by the Kähler form** (`H_ε ≥ (A - (q+2)B) Q`), used for the error
`g_ε^{(2)} = ρ(R/ε) ∂̄G` in Step 2 (with `A - (q + 2) B = 2π`, `H_ε ≥ 2πω`). -/
theorem twistedCurvature_normal_pole_ge_quad {p R : ComplexModel n → ℝ} {z : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p z) (hR : ContDiffAt ℝ 2 R z) (hRz : 0 < R z)
    (hR4 : R z < Real.exp (-4)) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < Real.exp (-4)) {q : ℝ}
    (hq : 0 ≤ q) {A B Q : ℝ} (v : ComplexModel n) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hqA : q * B ≤ A)
    (hpA : A * Q ≤ leviForm p z v)
    (hψB : -(B * Q) ≤ leviForm (fun y => Real.log (R y)) z v) :
    (A - (q + 2) * B) * Q ≤
      twistedCurvature (fun y => twistMu ε (Real.log (ε + R y)))
        (fun y => twistB (Real.log (ε + R y))) (fun y => p y + q * Real.log (R y)) z v := by
  have h := twistedCurvature_normal_pole_ge hp hR hRz hR4 hε hε4 hq v hQ hB hqA hpA hψB
  have : 0 ≤ ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v :=
    mul_nonneg (by positivity) (holDerivSq_nonneg _ _ _)
  linarith

end SGPT.Trace.TwistedL2
