import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.StokesCutoff
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

/-!
# The critical twist functions

Blueprint `claude-twisted-l2:critical-twist-functions` and `claude-twisted-l2:twist-identity`;
Xia, *Foundations of pluripotential theory*, q07, `lem:critical-twist-functions`.

For `0 < ε` and `t < 1` put `μ_ε(t) = ε - t + log(1 - t)` (`twistMu`) and `b(t) = (2 - t)²`
(`twistB`).  With `ψ_ε = log(ε + R)` the twist functions of the Ohsawa--Takegoshi estimate are
`a_ε = μ_ε ∘ ψ_ε` and `b_ε = b ∘ ψ_ε`.

* `twistMu_second_add_sq_div` — `μ'' + μ'²/b = 0` on `t < 1`, the identity which makes the twist
  terms collapse;
* `twistedCurvature_twist` — FPT part (2): for every weight `p`,
  `H = a_ε Levi(p) - Levi(a_ε) - |∂a_ε|²/b_ε = a_ε Levi(p) - μ'(ψ_ε) Levi(ψ_ε)`;
* `one_le_neg_deriv_twistMu`, `neg_deriv_twistMu_le_two`, `neg_le_twistMu`,
  `twistMu_add_twistB_le` — FPT part (1): `1 ≤ -μ' ≤ 2`, `a ≥ -t`, `a + b ≤ 5t²`;
* `log_add_lt_neg_three`, `twist_sum_le_five_sq` — the normalization `ψ < ψ_ε < -3` and
  `a_ε + b_ε ≤ 5ψ²` for `0 < R, ε < e^{-4}`;
* `leviForm_log_add` — FPT part (3):
  `Levi(log(ε + R)) = R/(ε + R) · Levi(log R) + (ε/R) |∂ log(ε + R)|²`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.FirstPass

/-! ### Real calculus -/

/-- `μ_ε(t) = ε - t + log(1 - t)`. -/
def twistMu (ε t : ℝ) : ℝ := ε - t + Real.log (1 - t)

/-- `b(t) = (2 - t)²`. -/
def twistB (t : ℝ) : ℝ := (2 - t) ^ 2

theorem hasDerivAt_twistMu (ε : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (twistMu ε) (-1 - (1 - t)⁻¹) t := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t :=
    h1.log (by linarith)
  have h3 : HasDerivAt (fun s : ℝ => ε - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub ε
  have h4 : HasDerivAt (fun s : ℝ => ε - s + Real.log (1 - s)) (-1 + -1 / (1 - t)) t :=
    h3.add h2
  have he : (-1 : ℝ) + -1 / (1 - t) = -1 - (1 - t)⁻¹ := by ring
  rw [he] at h4
  exact h4

theorem deriv_twistMu (ε : ℝ) {t : ℝ} (ht : t < 1) :
    deriv (twistMu ε) t = -1 - (1 - t)⁻¹ :=
  (hasDerivAt_twistMu ε ht).deriv

theorem deriv_deriv_twistMu (ε : ℝ) {t : ℝ} (ht : t < 1) :
    deriv (deriv (twistMu ε)) t = -((1 - t) ^ 2)⁻¹ := by
  have hev : deriv (twistMu ε) =ᶠ[𝓝 t] fun s => -1 - (1 - s)⁻¹ := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact deriv_twistMu ε hs
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h3 : HasDerivAt (fun s : ℝ => (1 - s)⁻¹) (-(-1) / (1 - t) ^ 2) t :=
    h1.inv (by linarith)
  have h4 : HasDerivAt (fun s : ℝ => -1 - (1 - s)⁻¹) (-(-(-1) / (1 - t) ^ 2)) t :=
    h3.const_sub (-1)
  rw [h4.deriv]
  ring

theorem contDiffAt_twistMu (ε : ℝ) {t : ℝ} (ht : t < 1) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (twistMu ε) t := by
  have h1 : ContDiffAt ℝ k (fun s : ℝ => 1 - s) t := contDiffAt_const.sub contDiffAt_id
  exact (contDiffAt_const.sub contDiffAt_id).add (h1.log (by linarith))

/-- **`μ'' + μ'²/b = 0`** on `t < 1`. -/
theorem twistMu_second_add_sq_div (ε : ℝ) {t : ℝ} (ht : t < 1) :
    deriv (deriv (twistMu ε)) t + deriv (twistMu ε) t ^ 2 / twistB t = 0 := by
  rw [deriv_deriv_twistMu ε ht, deriv_twistMu ε ht, twistB]
  have h1 : (1 : ℝ) - t ≠ 0 := by linarith
  have h2 : (2 : ℝ) - t ≠ 0 := by linarith
  field_simp
  ring

theorem one_le_neg_deriv_twistMu (ε : ℝ) {t : ℝ} (ht : t ≤ 0) :
    1 ≤ -deriv (twistMu ε) t := by
  rw [deriv_twistMu ε (by linarith)]
  have : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
  linarith

theorem neg_deriv_twistMu_le_two (ε : ℝ) {t : ℝ} (ht : t ≤ 0) :
    -deriv (twistMu ε) t ≤ 2 := by
  rw [deriv_twistMu ε (by linarith)]
  have : (1 - t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

theorem neg_le_twistMu {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : t ≤ 0) : -t ≤ twistMu ε t := by
  have : 0 ≤ Real.log (1 - t) := Real.log_nonneg (by linarith)
  unfold twistMu
  linarith

theorem twistMu_add_twistB_le {ε : ℝ} (hε : ε ≤ 1) {t : ℝ} (ht : t ≤ -3) :
    twistMu ε t + twistB t ≤ 5 * t ^ 2 := by
  have hlog : Real.log (1 - t) ≤ -t := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - t)
    linarith
  unfold twistMu twistB
  nlinarith

/-- With `0 < R < e^{-4}` and `0 < ε < e^{-4}`: `log(ε + R) < -3`. -/
theorem log_add_lt_neg_three {ε R : ℝ} (hε : 0 < ε) (hε' : ε < Real.exp (-4)) (hR : 0 < R)
    (hR' : R < Real.exp (-4)) : Real.log (ε + R) < -3 := by
  rw [Real.log_lt_iff_lt_exp (by linarith)]
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have h3 : Real.exp (-3) = Real.exp 1 * Real.exp (-4) := by
    rw [← Real.exp_add]; norm_num
  have h4 : 0 < Real.exp (-4) := Real.exp_pos _
  rw [h3]
  nlinarith

/-- `ψ < ψ_ε < -3` and `a_ε + b_ε ≤ 5ψ_ε² ≤ 5ψ²` (`ψ = log R`, `ψ_ε = log(ε + R)`). -/
theorem twist_sum_le_five_sq {ε R : ℝ} (hε : 0 < ε) (hε' : ε < Real.exp (-4)) (hR : 0 < R)
    (hR' : R < Real.exp (-4)) :
    Real.log R < Real.log (ε + R) ∧ Real.log (ε + R) < -3 ∧
      twistMu ε (Real.log (ε + R)) + twistB (Real.log (ε + R)) ≤ 5 * Real.log (ε + R) ^ 2 ∧
      5 * Real.log (ε + R) ^ 2 ≤ 5 * Real.log R ^ 2 := by
  have h1 : Real.log R < Real.log (ε + R) := Real.log_lt_log hR (by linarith)
  have h2 := log_add_lt_neg_three hε hε' hR hR'
  have hε1 : ε ≤ 1 := by
    have : Real.exp (-4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  refine ⟨h1, h2, twistMu_add_twistB_le hε1 h2.le, ?_⟩
  nlinarith

/-! ### The twisted curvature of the critical twist -/

section Levi

variable {n : ℕ}

theorem fderiv_comp_real {θ : ℝ → ℝ} {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hθ : DifferentiableAt ℝ θ (f z)) (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun y => θ (f y)) z = deriv θ (f z) • fderiv ℝ f z :=
  (hθ.hasDerivAt.comp_hasFDerivAt z hf.hasFDerivAt).fderiv

theorem holDerivSq_comp {θ : ℝ → ℝ} {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hθ : DifferentiableAt ℝ θ (f z)) (hf : DifferentiableAt ℝ f z) (v : ComplexModel n) :
    holDerivSq (fun y => θ (f y)) z v = deriv θ (f z) ^ 2 * holDerivSq f z v := by
  unfold holDerivSq
  rw [fderiv_comp_real hθ hf]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- **The twist identity** (FPT `lem:critical-twist-functions` (2)): for `a = μ_ε ∘ ψ` and
`b = (2 - ψ)²`, `a Levi(p) - Levi(a) - |∂a|²/b = a Levi(p) - μ_ε'(ψ) Levi(ψ)`, for every weight
`p`, at every point where `ψ < 1`. -/
theorem twistedCurvature_twist (ε : ℝ) {ψ p : ComplexModel n → ℝ} {z : ComplexModel n}
    (hψ : ContDiffAt ℝ 2 ψ z) (hz : ψ z < 1) (v : ComplexModel n) :
    twistedCurvature (fun y => twistMu ε (ψ y)) (fun y => twistB (ψ y)) p z v =
      twistMu ε (ψ z) * leviForm p z v - deriv (twistMu ε) (ψ z) * leviForm ψ z v := by
  have hμ : ContDiffAt ℝ 2 (twistMu ε) (ψ z) := contDiffAt_twistMu ε hz
  have hψd : DifferentiableAt ℝ ψ z := hψ.differentiableAt (by norm_num)
  have hμd : DifferentiableAt ℝ (twistMu ε) (ψ z) := hμ.differentiableAt (by norm_num)
  unfold twistedCurvature
  rw [StokesCutoff.leviForm_comp hμ hψ v, holDerivSq_comp hμd hψd v]
  have key := twistMu_second_add_sq_div ε hz
  have hsec : deriv (deriv (twistMu ε)) (ψ z) =
      -(deriv (twistMu ε) (ψ z) ^ 2 / twistB (ψ z)) := by linarith
  rw [hsec]
  unfold holDerivSq
  ring

/-- **The logarithmic Hessians** (FPT `lem:critical-twist-functions` (3)): for `R > 0` at `z`
and `ε > 0`,
`Levi(log(ε + R)) = R/(ε + R) · Levi(log R) + (ε/R) |∂ log(ε + R)|²`. -/
theorem leviForm_log_add {R : ComplexModel n → ℝ} {z : ComplexModel n} (hR : ContDiffAt ℝ 2 R z)
    (hRz : 0 < R z) {ε : ℝ} (hε : 0 < ε) (v : ComplexModel n) :
    leviForm (fun y => Real.log (ε + R y)) z v =
      R z / (ε + R z) * leviForm (fun y => Real.log (R y)) z v +
        ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v := by
  have hS : ContDiffAt ℝ 2 (fun y => ε + R y) z := contDiffAt_const.add hR
  have hSz : 0 < ε + R z := by linarith
  rw [ConcentrationPotentialLevi.leviForm_log_of_pos hS hSz v,
    ConcentrationPotentialLevi.leviForm_log_of_pos hR hRz v]
  have hL : leviForm (fun y => ε + R y) z v = leviForm R z v := by
    have : (fun y => ε + R y) = (fun _ => ε) + R := rfl
    rw [this, leviForm_add contDiffAt_const hR, leviForm_const, zero_add]
  have hD : fderiv ℝ (fun y => ε + R y) z = fderiv ℝ R z := fderiv_const_add ε
  have hlogD : fderiv ℝ (fun y => Real.log (ε + R y)) z = (ε + R z)⁻¹ • fderiv ℝ R z := by
    have h := (hS.differentiableAt (by norm_num)).hasFDerivAt.log hSz.ne'
    rw [h.fderiv, hD]
  rw [hL, hD]
  unfold holDerivSq
  rw [hlogD]
  simp only [_root_.smul_apply, smul_eq_mul]
  field_simp
  ring

end Levi

end SGPT.Trace.TwistedL2
